

from __future__ import annotations

from typing import Tuple
from types import FunctionType

from ply import lex, yacc

from .syntax_rules import *

from .rem_error import REM_Error, REM_type_check


###################################
# Lexer
###################################

class PLYLexer:

    # the object to store the rules
    class BuildData:
        '''
        This build data only stores those attributes directly used in lexer building.
        '''
        def __init__(self):
            self.tokens : list[str]
            self.literals : list[str]

            # the default `t_error` function is necessary
            self.t_error = t_error


    def __init__(self, empty_mode : bool = False):
        '''
        Construct a basic lexer.

        - `empty_mode` : `bool`, if set to `True`, there will be no default lexing rules defined (e.g., `t_error`, `t_COMMENT`, ...). The default is `False`.
        '''
        self.__lexer = None

        self.reserved : dict[str, str] = {}
        # this `unreserved_tokens` does not contain reserved tokens
        self.unreserved_tokens : list[str] = []
        self.literals : list[str] = []

        # lexing rule stack
        self.stack : list[Tuple[str, str | function]] = []

        # default lexing rules
        if not empty_mode:
            self.stack.append(("ignore", ' \t'))
            self.stack.append(("COMMENT", t_COMMENT))
            self.stack.append(("newline", t_newline))

        self.__build_data : PLYLexer.BuildData | None = None

    @property
    def build_data(self) -> PLYLexer.BuildData:
        if self.__build_data is None:
            raise REM_Error("Rem has not built the lexer yet.")
        return self.__build_data

    @property
    def lexer(self):
        if self.__lexer is None:
            raise REM_Error("Rem has not built the lexer yet.")
        return self.__lexer

    def add_reserved(self, reserved_type : str, reserved_key : str):
        REM_type_check(reserved_key, str)
        REM_type_check(reserved_type, str)

        self.reserved[reserved_key] = reserved_type

    def add_rule(self, token : str, rule : str | function):

        if isinstance(rule, str):
            self.stack.append((token, rule))

            if token not in ['ignore', 'COMMENT']:
                self.unreserved_tokens.append(token)

        elif isinstance(rule, FunctionType):
            rule.__name__ = f"t_{token}"
            self.stack.append((token, rule))

            if token not in ['ignore', 'COMMENT']:
                self.unreserved_tokens.append(token)

        else:
            raise REM_Error(f"Rem detected the invalid lexing rule '{rule}'.")
        
    def add_literals(self, literal : str | list[str]):
        if isinstance(literal, str):
            self.literals.append(literal)

        elif isinstance(literal, list):
            self.literals += literal
            
        else:
            raise REM_Error(f"Rem detected the invalid lexing literals '{literal}'.")

    def build(self):

        self.__build_data = self.BuildData()
        self.build_data.literals = self.literals.copy()

        for token, rule in self.stack:
            setattr(self.build_data, f"t_{token}", rule)

        self.build_data.tokens = list(self.reserved.values()) + self.unreserved_tokens

        self.__lexer = lex.lex(self.build_data)

    # interface
    def __call__(self, raw : str):
        return self.lexer.input(raw)
    def token(self):
        return self.lexer.token()
    

    # fusion
    def fuse_append(self, other : PLYLexer) -> None:
        '''
        Fuse the two lexer definitions.
        It will update the definitions of `other` on `self`.
        It means that definitions from `other` will be used when conflicts happen.

        TODO #4
        '''
        REM_type_check(other, PLYLexer)

        self.reserved = self.reserved.copy()
        self.reserved.update(other.reserved)

        self.unreserved_tokens = self.unreserved_tokens + other.unreserved_tokens
        self.literals = self.literals + other.literals
        self.stack = self.stack + other.stack






##############################################################
# Parser
#########

def type_match(p, types: Tuple[str, ...]) -> bool:
    '''
    A syntax sugar for parsing rules.
    The method to check whether the sentence match the corresponding types.
    '''
    if len(p) != len(types) + 1:
        return False
    
    for i in range(len(types)):
        if p.slice[i + 1].type != types[i]:
            return False
    return True




class PLYParser:
    MAX_PRECEDENCE = 512
    
    class BuildData:
        '''
        This build data only stores those attributes directly used in parser building.
        '''
        def __init__(self):

            self.tokens : list[str]

            self.start : str

            self.precedence : Tuple[Tuple[str, ...], ...]

            # the default `p_error` function is necessary
            self.p_error = p_error




    def __init__(self, empty_mode : bool = False):
        '''
        About precedence: items with higher precedence will be matched first.

        - `empty_mode` : `bool`, if set to `True`, there will be no default parsing rules defined (e.g., `p_error`). The default is `False`.
        '''

        self.__parser = None

        # the precedence tab
        # the first element in the tuple is the associativity. If it is left `None`, then the default value is applied.
        self.prec_tab : list[Tuple[str | None, list[str]]] = [(None, [])] * PLYParser.MAX_PRECEDENCE

        # the parsing rule stack. A list of (item_name, item_func)
        self.stack : list[Tuple[str, FunctionType]] = []

        if not empty_mode:
            pass
        
        self.__build_data : PLYParser.BuildData | None = None

    @property
    def build_data(self) -> PLYParser.BuildData:
        if self.__build_data is None:
            raise REM_Error("Rem has not built the parser yet.")
        return self.__build_data

    @property
    def parser(self):
        if self.__parser is None:
            raise REM_Error("Rem has not built the parser yet.")
        return self.__parser

    def set_precedence(self, term : str, prec : int, assoc : str):
        '''
        Set the precedence of the term. #TODO #8
        '''
        REM_type_check(term, str)
        REM_type_check(prec, int)
        if not 0 <= prec < PLYParser.MAX_PRECEDENCE:
            raise REM_Error(f"Rem detected invalid precedence number {prec}. It should be between 0 and {PLYParser.MAX_PRECEDENCE-1}.")
        
        if assoc not in ("left", "right", "nonassoc"):
            raise REM_Error(f"Rem detected invalid associativity {assoc}. It should be 'left', 'right' or 'nonassoc'.")
        
        if self.prec_tab[prec][0] is not None and self.prec_tab[prec][0] != assoc:
            raise REM_Error(f"Rem found that the precedence {prec} has been defined as '{self.prec_tab[prec][0]}' associativity, which is inconsistent with the current specification '{assoc}'.")
        
        self.prec_tab[prec] = (assoc, self.prec_tab[prec][1] + [term])
        



    def add_rule(self, rule : function):
        '''
        Add a parsing rule to this `PLYParser` instance. The name will be automaticall extracted from the documentation of the rule function.
        '''

        if not isinstance(rule, FunctionType) or rule.__doc__ is None:
            raise REM_Error(f"Rem detected the invalid rule function '{rule}'.")
        
        doc = rule.__doc__
        pos = doc.index(":")
        name = doc[:pos].replace("\n","").replace(" ","").replace("\t", "")

        self.stack.append((name, rule))


    def build(self, plylexer : PLYLexer, start_symbol : str | None):
        '''
        - `plylexer` : `PLYLexer`, a built `PLYLexer` instance
        - `start_symbol` : `str | None`, 
            `str`: the start symbol,
            `None`: dry run, only process the parser information
        '''

        REM_type_check(plylexer, PLYLexer)

        self.__build_data = PLYParser.BuildData()


        # set the token
        self.build_data.tokens = plylexer.build_data.tokens

        # calculate precedence
        precedence : list[Tuple[str, ...]] = []
        for assoc, opts in self.prec_tab:
            if len(opts) == 0:
                continue
            # apply the default value
            if assoc is None:
                assoc = 'right'
            precedence.append((assoc,) + tuple(opts))
        self.build_data.precedence = tuple(precedence)

        for name, rule in self.stack:
            setattr(self.build_data, f"p_{name}", rule)

        # set the start symbol and build
        if start_symbol is not None:
            self.build_data.start = start_symbol
            self.__parser = yacc.yacc(module=self.build_data)

        self.plylexer = plylexer

    # interface
    def __call__(self, raw : str):
        return self.parser.parse(raw, lexer = self.plylexer.lexer)
    
    # fusion
    def fuse_append(self, other : PLYParser) -> None:
        '''
        Fuse the two parser definitions.
        It will update the definitions of `other` on `self`.
        It means that definitions from `other` will be used when conflicts happen.
        '''

        REM_type_check(other, PLYParser)

        # fuse the precedence table
        for i in range(PLYParser.MAX_PRECEDENCE):
            assoc : str | None
            if self.prec_tab[i][0] is None:
                if other.prec_tab[i][0] is None:
                    assoc = None
                else:
                    assoc = other.prec_tab[i][0]
            else:
                if other.prec_tab[i][0] is None:
                    assoc = self.prec_tab[i][0]
                else:
                    if self.prec_tab[i][0] != other.prec_tab[i][0]:
                        raise REM_Error(f"Rem cannot fuse the two parsing rule sets because of precedence conflicts: for precedence {i}, one rule set has associativity '{self.prec_tab[i][0]}' and the other has '{other.prec_tab[i][0]}'.")
                    assoc = self.prec_tab[i][0]
                
            
            self.prec_tab[i] = (assoc, self.prec_tab[i][1] + other.prec_tab[i][1])

        self.stack = self.stack + other.stack

        


