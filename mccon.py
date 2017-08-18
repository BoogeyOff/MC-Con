#!/usr/bin/env python
"""module for multi-colour printing to console.
also includes:
 - timestamped logging and echoing of all stdout and stderr to a log file
 - seleciton between background event printing and user input modes
 - clear highlighting of stderr output
 - combining of multiple closely time-spaced stderr (eg exception trace)
    prints into batches to avoid mixing with stdout prints. This introduces
    a very slight delay and time-stamped stderr messages can appear after
    later-timestamped stdout messages
 - extended/simplified user raw and password input catpuring
 - simple exception trace printing
"""

import sys, traceback, threading, os
from datetime import datetime
from contextlib import contextmanager
from Queue import Queue
from threading import Timer
import getpass

__author__  = "Dmytro Bugayev"
__credits__ = ["Countless Pythonistas on StackOverflow, as always!","Wikipedia"]
__license__ = "GPL"

#default user prompt
global PROMPT
PROMPT = 'Command> '

# used to separate fields in print statements. something not common
# in usual print statements for easy log file imports into spreadsheets
global SEPARATOR
SEPARATOR = "|"

#the log file - opened when init is called
global log_file
log_file = None

#if true, then only print statements inside a "with user():" will be printed
#useful to block printing from a background process. all events are always logged
#to the log file, irrespective of this flag
global user_mode
user_mode = False
# the print datetime format

global datetime_format
# date time log format. nd how many characters to remove from the end.
# this allows you to control the sub-second precision easily(-3=ms precision)
datetime_format = ("%y-%m-%d %H:%M:%S.%f",-3)

# set this to False if you don't want the name of the destination
# log file to be printed after the init() call
global print_log_name
print_log_name = True

# lock object to separate stdout and std err prints
# can use it externally to "batch" multiple prints from different threads
global lock
lock = threading.RLock()

# timeout used to batch stderr messages. default is 50ms
global timeout
timeout = 0.02

# dictionary of words and their colour mappings to be automatically highlighted
global highlights
highlights = {}

# the pre-fix to all timestamped messages. can be set through init()
# can be overridden with prefix()
global prefix
prefix = 'mccon'

# status keywords for convenience; and their highlight colours
global STAT, WARN, ERROR
STAT = 'STAT'
WARN = 'WARN'
ERRO = 'ERRO'
stat_highlight = {}

# first up, make stderr and stdout unbuffered
sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', 0)
sys.stderr = os.fdopen(sys.stderr.fileno(), 'w', 0)

# save the original stdout and stderr
old_stdout = sys.stdout
old_stderr = sys.stderr


# call this first up to initialise the module
def init(colour=True, log=None, default_prefix='mccon',\
         log_stderr=True, print_stderr_header=True):
    """
    Call this function before any print statements.
    Initialises all the important variables
    the app name is pre-pended to all time-tamped messages
    """
    global prefix
    prefix = default_prefix
    global use_colour
    use_colour = colour


    # console colour codes.the various ANSI escape codes, including the colours below
    # are documented at https://en.wikipedia.org/wiki/ANSI_escape_code
    # the format is basically as follows:
    # the escape sequence \033[ + colour number xx + optional brightness ;1 + m
    # the m is the colour instruction code. 30s numbers - foreground. 40s - backgr
    # use the gen_color method to create your own colours that aren't listed here
    global PROMPT_COLOUR, USER_INPUT_COLOUR, DISABLED_COLOUR,\
           NO_COLOUR, ERROR_COLOUR, WARN_COLOUR, STAT_COLOUR, DULL_COLOUR,\
           USER_COLOUR, HIGHLIGHT_COLOUR, LOWLIGHT_COLOUR,\
           STDERR_PREFIX, STDERR_HEADER

    #set up the colour scheme
    if use_colour:
        PROMPT_COLOUR       = gen_color(36)            #dark cyan
        USER_INPUT_COLOUR   = gen_color(36,True)       #bright cyan
        DISABLED_COLOUR     = gen_color(30,True)       #dark grey (light black)
        NO_COLOUR           = gen_color(0)             #back to default
        ERROR_COLOUR        = gen_color(31,True)       #bright red
        WARN_COLOUR         = gen_color(33,True)       #bright yellow
        STAT_COLOUR         = gen_color(37)            #white/grey
        DULL_COLOUR         = gen_color(32)            #dark green
        USER_COLOUR         = gen_color(32,True)       #bright green
        HIGHLIGHT_COLOUR    = gen_color(35,True)       #bright magenta
        LOWLIGHT_COLOUR     = gen_color(30,True)       #dark grey (light black)

        # a few other colour related vars
        # dark red bg, black fg, the + char prefix makes stderr
        # output easier to search for in the log file
        STDERR_PREFIX = NO_COLOUR + gen_color(41) + gen_color(30) + '+' +\
            NO_COLOUR + '    ' + ERROR_COLOUR
        #printed at the start of an stderr print block (black+ on dark red bg)
        STDERR_HEADER = '\n'+NO_COLOUR + gen_color(41) + gen_color(30) + ''

    #clear all formatting
    else:
        PROMPT_COLOUR = USER_INPUT_COLOUR = DISABLED_COLOUR = NO_COLOUR = \
        ERROR_COLOUR = WARN_COLOUR = STAT_COLOUR = DULL_COLOUR = \
        USER_COLOUR = HIGHLIGHT_COLOUR = LOWLIGHT_COLOUR = ''
        STDERR_PREFIX = '+    '
        STDERR_HEADER = '\n'

    #status code highlighting
    stat_highlight.update({STAT : STAT_COLOUR,
                           WARN : WARN_COLOUR,
                           ERRO : ERROR_COLOUR})

    global mccon_out, mccon_err
    if log is not None:
        #open log_file in append mode
        log_file = open(log, 'a')

    #create and set up the new sterr and stdout objects
    mccon_out = MCConOut(old_stdout,log_file)
    mccon_err = MCConErr(old_stderr,log_file if log_stderr else None,
        print_stderr_header)

    #comment out the next two lines for debugging purposes
    sys.stdout = mccon_out
    sys.stderr = mccon_err

    #open the log file and print the name if required
    global print_log_name
    if log_file is not None and print_log_name:
        print_log_name = False
        with user(), highlight([log,default_prefix],[]):
            print "%s: begin logging to %s" % (default_prefix, log)

# new multi-colour stdout
class MCConOut():
    def __init__(self, stream, log):
        self.old = stream
        self.log = log
        self.user = False
        self.error = False
        self.warn = False
        self.file_only = False
        self.high_words = {}
        self.low_words = {}
        self.last = None
        self.allowed = True
        self.queue = Queue()

    # text formatting routine
    def process_text(self, text):
        if use_colour:
            text_len = len(text)
            #decide on the overall colour to use for this message
            msg_col = USER_COLOUR if self.user else DULL_COLOUR
            msg_col = WARN_COLOUR if self.warn else msg_col
            msg_col = ERROR_COLOUR if self.error else msg_col

            #build up an overall map of keywords and colours
            word_col_map = {}
            for wmap, def_col in [\
                (self.high_words,HIGHLIGHT_COLOUR),\
                (self.low_words ,LOWLIGHT_COLOUR),\
                (highlights     ,HIGHLIGHT_COLOUR),\
                (stat_highlight ,HIGHLIGHT_COLOUR)]:
                for word in wmap:#self.high_words:
                    if len(word) < text_len and word not in word_col_map:
                        col = wmap[word]
                        col = col if col is not None else def_col
                        word_col_map[word] = col
                #text = text.replace(word,NO_COLOUR + col + word + msg_col)

            #add the special case SEPARATOR mapping
            word_col_map[SEPARATOR] = DISABLED_COLOUR
            #apply the highlighting routine with words in decreasing length order
            words = word_col_map.keys()
            words.sort(key=len)
            words.reverse()
            split_text = [(text,msg_col)]
            # this is essentially a 'recursive' split using keywords, building up
            # a text fragment to colour tuple list
            for word in words:
                new_split_text = []
                for txt,col in split_text:
                    split = txt.split(word)
                    for fragment in split[:-1]:
                        new_split_text.append((fragment,col))
                        new_split_text.append((word,word_col_map.get(word)))
                    new_split_text.append((split[-1],col))
                split_text = new_split_text
            form_text = ''
            for txt,col in split_text:
                form_text += '%s%s%s' % (NO_COLOUR, col, txt)
            return form_text
        return text

    #will be called as a result of print statementss
    def write(self, text):
        #synchronise the operation
        with lock:
            if text is not None:
                self.queue.put((self.file_only,text,
                self.process_text(text),(self.user and user_mode) or not user_mode))
            if not self.allowed:
                return
            # first write to the log file
            while not self.queue.empty():
                file_only, text, form_text, prnt = self.queue.get()
                if self.log:
                    self.log.write(text)
                #print if: in user mode and done with user() or not in user mode
                if not file_only and prnt:
                    self.old.write(form_text)
                #force a disk write on a new line
                if '\n' in text:
                    self.flush()
                if len(text) > 0:
                    self.last = text[-1]
            if self.last == '\n':
                mccon_err.write_buffer(True)

    def flush(self):
        if self.log:
            self.log.flush()

    # when closing print the no colour instruction otherwise the
    def close(self):
        self.flush()
        if use_colour:
            self.old.write(NO_COLOUR)

#new multi-colour stderr
class MCConErr():
    def __init__(self, old, log, print_header):
        self.old = old
        self.log = log
        self.user = False
        self.error = True
        self.warn = False
        self.file_only = False
        self.print_header = print_header
        #queue object used for buffering closely spaced writes
        self.queue = Queue()
        self.t = None
        self.msg = ''

    def process_text(self,text):
        #print to screen if: in loggin mode, or user feedback in non-loggin mode
        text = text.replace('\n','\n'+STDERR_PREFIX)
        if use_colour:
            try:
                #pick the message colour
                msg_col = ERROR_COLOUR \
                    if self.error else WARN_COLOUR
                msg_col = USER_COLOUR \
                    if self.user else msg_col
                #format the text
                form_text = NO_COLOUR + msg_col + text + NO_COLOUR
                return form_text
            except:
                traceback.print_exc(file=self.old)
        return text

    def write(self,text):
        try:
            with lock:
                #if the exception header is enabled, add it to the queue
                if self.queue.empty() and self.print_header:
                    self.queue.put(STDERR_HEADER +\
                        _logprefix()+self.msg+NO_COLOUR+'\n')
                self.queue.put(text)
                if self.t is None:
                    self.t = Timer(timeout,self.write_buffer,args=[False])
                    self.t.start()
        except:
            traceback.print_exc(file=self.old)


    def write_buffer(self,print_anyway):
        #self.old.write('\n'+str(print_anyway)+'\n')
        try:
            with lock:
                self.t = None
                if self.queue.empty():
                    return
                if not print_anyway and mccon_out.last != '\n':
                    self.t = Timer(timeout,self.write_buffer,args=[True])
                    self.t.start()
                    return
                while True:
                    mccon_out.allowed = False
                    try:
                        #try to get an item
                        text = self.queue.get(True,timeout)
                    except: #failed to get item in the timeout
                        if not self.file_only and \
                            ((self.user and user_mode) or not user_mode):
                            if self.log:
                                self.log.write('\n')
                            self.old.write('\n')
                            self.flush()
                        mccon_out.allowed = True
                        break
                    # first write to the log file
                    if self.log:
                        self.log.write(text)
                    #print if: in user mode and done with user() or not in user mode
                    if not self.file_only and \
                        ((self.user and user_mode) or not user_mode):
                        self.old.write(self.process_text(text))
                    #force a disk write on a new line
                    if '\n' in text:
                        self.flush()
        except:
            traceback.print_exc(file=self.old)
        mccon_out.allowed = True


    def flush(self):
        self.log.flush()

    def close(self):
        self.flush()
        if use_colour:
            self.old.write(NO_COLOUR)

#import atexit
#@atexit.register
#close the log file on exit
def close():
    mccon_out.close()
    mccon_err.close()
    global log_file
    if log_file is not None:
        try:
            log_file.close()
        except:
            print_exception()
        log_file = False

# generates a colour string for the given code and brightness flag
def gen_color(code, bright=False):
    return '\033['+str(code) + (';1m' if bright else 'm') #+' '+\
        #str(code*10+(1 if bright else 0))+'_'
    #comment out the above two lines for debugging

@contextmanager
def file_only():
    mccon_out.file_only = True
    yield
    mccon_out.file_only = False

@contextmanager
def none():
    yield

@contextmanager
def user():
    mccon_out.user = True
    yield
    mccon_out.user = False
    #print '',

@contextmanager
def user_err():
    mccon_err.user = True
    yield
    mccon_err.user = False

@contextmanager
#highlight with the default colour scheme
def highlight(hiwords,lowords):
    high_map = {}
    low_map = {}
    for word in hiwords:
        high_map[word] = None
    for word in lowords:
        low_map[word] = None
    mccon_out.high_words = high_map
    mccon_out.low_words = low_map
    yield
    mccon_out.high_words = {}
    mccon_out.low_words = {}

@contextmanager
#highlight with custom colours
def highmap(hiwords,lowords):
    mccon_out.high_words = hiwords
    mccon_out.low_words = lowords
    yield
    mccon_out.high_words = {}
    mccon_out.low_words = {}

@contextmanager
def error():
    mccon_out.error = True
    yield
    mccon_out.error = False

@contextmanager
def pre(pre=prefix):
    global prefix
    old_prefix = prefix
    prefix = pre
    yield
    prefix = old_prefix

@contextmanager
def warn():
    mccon_out.warn = True
    yield
    mccon_out.warn = False

@contextmanager
#prints a time-stamp log message with a status
def logstat(typ=STAT):
    mccon_out.write(_logprefix(typ))
    yield

@contextmanager
# prints a time-stamped log message without a status field
def log():
    mccon_out.write(_logprefix())
    yield

# generates the log prefix
def _logprefix(typ=None):
    if typ is None:
        return "{0}{2}{1}{2}".format(prefix, \
            datetime.now().strftime(datetime_format[0])[:datetime_format[1]],
            SEPARATOR)
    else:
        return "{0}{3}{1}{3}{2}{3}".format(prefix, typ, \
            datetime.now().strftime(datetime_format[0])[:datetime_format[1]],
            SEPARATOR)

# extended user input function. takes in:
# prompt to display, whether the user input is visible. Invisible input is
# retrieved through getpass, and the received input isn't logged to file
# whether to block all other output from being printed to the console
def user_input(msg=PROMPT, visible=True):
    with user():
        if user_mode:
            if use_colour:
                old_stdout.write(NO_COLOUR + PROMPT_COLOUR +
                    msg + USER_INPUT_COLOUR)
            else:
                old_stdout.write(msg)
        else:
            old_stdout.write(NO_COLOUR + DISABLED_COLOUR)
        if visible:
            val = raw_input()
            with file_only():
                print msg + val
        else:
            val = getpass.getpass('')
            with file_only():
                print msg + '********'
        return val

@contextmanager
def err_header_msg(msg):
    old_err_msg = mccon_err.msg
    mccon_err.msg = msg
    yield
    mccon_err.msg = old_err_msg

#convenience function - prints the current exception trace
def print_exception(msg='Exception Details'):
    with err_header_msg(' ' +msg+' '):
        traceback.print_exc(file=sys.stderr)


#
