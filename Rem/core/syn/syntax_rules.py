'''
This file contains the common syntax rules.
'''

from ..rem_error import *

#############################################################
# Common lexing rules
####

# the re expr for ID (allowing ')
regex_ID = r'[a-zA-Z\'][a-zA-Z\'0-9]*'

# the re expr for NATURALNUM
regex_NATURALNUM = r'0|([1-9][0-9]*)'

# the re expr for INT
regex_INT = r'[-+]?(0|([1-9][0-9]*))'


# the re expr for complex number
regex_COMPLEXNUM = r'([-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?[-+][0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?j)|([-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?j)|([-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?)'

# the re expr for float number
regex_FLOATNUM = r'[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?'

# use // or /* */ to comment
def t_COMMENT(t):
    r'(/\*(.|\n)*?\*/)|(//.*)'
    for c in t.value:
        if c == '\n':
            t.lexer.lineno += 1

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_error(t):
    raise REM_Syntax_Error(f"Syntax Error: Illegal character '{t.value[0]}'. (line {t.lineno})")


#############################################################
# Common parsing rules
####

def p_error(p):
    if p is None:
        raise REM_Syntax_Error("Empty or incomplete input.")
    raise REM_Syntax_Error(f"Syntax error in input: '{str(p.value)}'.")
