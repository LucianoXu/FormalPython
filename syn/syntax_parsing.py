

from __future__ import annotations

from typing import Tuple, List, Dict
from types import FunctionType

from ply import lex, yacc
from ply.lex import TOKEN

from .syntax_rules import *

from ..rem_error import REM_Parser_Building_Error, REM_type_check, REM_other_check


###################################
# Lexer
###################################

meta_reserved_token = ['ignore', 'COMMENT']

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



    def __init__(self, master : object):
        '''
        Construct a basic lexer.
        '''
        self.__lexer = None

        # integrity : whether there are modifications after build
        self.__integrity = False

        # the master of this lexer
        self.__master = master

        # `token_source` keep records of the objects that has defined the tokens.
        self.token_source : dict[str, list[object]] = {}

        # lexing rule stack
        self.reserved : dict[str, str] = {}
        self.rule_stack : dict[str, str | function] = {}
        self.literals : set[str] = set()

        self.__build_data : PLYLexer.BuildData | None = None

    def copy(self) -> PLYLexer:
        res = PLYLexer(self.master)
        res.__integrity = self.__integrity
        res.__master = self.__master
        res.token_source = self.token_source.copy()
        res.reserved = self.reserved.copy()
        res.rule_stack = self.rule_stack.copy()

        # this two information can be reused
        res.__lexer = self.__lexer
        res.__build_data = self.__build_data

        return res


    @property
    def lexer(self):
        if self.__lexer is None:
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}'): Lexer not built.")
        if not self.integrity:
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}'): Lack of integrity. Rebuild the lexer after modifying it.")
        
        return self.__lexer
    
    @property
    def integrity(self) -> bool:
        return self.__integrity
    
    @property
    def unreserved_tokens(self) -> list[str]:
        '''
        return the tokens defined not as reserved (meta-reserved tokens like "ignore" and "COMMENT" are ruled out)
        '''
        res = list(self.rule_stack.keys())
        for token in meta_reserved_token:
            res.remove(token)
        return res

    @property
    def master(self) -> object:
        return self.__master

    @property
    def build_data(self) -> PLYLexer.BuildData:
        if self.__build_data is None:
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}'): Lexer not built.")
        if not self.integrity:
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}'): Lack of integrity. Rebuild the lexer after modifying it.")
        
        return self.__build_data
    
    def __append_source(self, token : str, source : object):
        if token not in self.token_source:
            self.token_source[token] = [source]
        else:
            self.token_source[token].append(source)

    def get_reserved_key(self, reserved_token) -> str:
        '''
        return the corresponding reserved key for the given reserved token
        '''
        return list(self.reserved.keys())[list(self.reserved.values()).index(reserved_token)]

    def add_reserved(self, reserved_type : str, reserved_key : str, source : object):
        '''
        Reserved keywords will be detected before `t_ID`.
        - `reserved_type` : The type of the reserved token.
        - `reserved_key` : The reserved keyword.
        - `source` : the source of this reserved word.
        '''
        REM_type_check(reserved_key, str, REM_Parser_Building_Error)
        REM_type_check(reserved_type, str, REM_Parser_Building_Error)

        if reserved_type in self.rule_stack:
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}')(source '{source}'): The token '{reserved_type}' has been defined as the rule '{self.rule_stack[reserved_type]}'.")

        # consistent keyword for tokens
        if reserved_type in self.reserved.values():
            existing_key = self.get_reserved_key(reserved_type)
            REM_other_check(existing_key == reserved_key, f"(lexer of '{self.master}')(source '{source}'): Token '{reserved_type}' bas been defined as '{existing_key}', which is not consistent with the subsequent definition '{reserved_key}'.", REM_Parser_Building_Error)

        # unique token for keywords
        elif reserved_key in self.reserved:
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}')(source '{source}'): The reserved word '{reserved_key}' has been defined for token '{self.reserved[reserved_key]}'.")
        
        # record the source
        self.__append_source(reserved_type, source)      

        self.reserved[reserved_key] = reserved_type

        self.__integrity = False

    def add_rule(self, token : str, rule : str | function, source : object):
        REM_type_check(token, str, REM_Parser_Building_Error)
        REM_type_check(rule, (str, FunctionType), REM_Parser_Building_Error)

        if token in self.rule_stack:
            REM_other_check(self.rule_stack[token] == rule,
                f"(lexer of '{self.master}')(source '{source}'): The token '{token}' has been defined as '{self.rule_stack[token]}', which is not consistent with the subsequent definition '{rule}'.", REM_Parser_Building_Error)
        
        # consistent rules for tokens
        if token in self.reserved.values():
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}')(source '{source}'): The token '{token}' has been defined as a reserved word for '{self.get_reserved_key(token)}'.")
            
        # record the source
        self.__append_source(token, source)

        if isinstance(rule, FunctionType):
            rule.__name__ = f"t_{token}"

        self.rule_stack[token] = rule

        self.__integrity = False

        
    def add_literals(self, literal : str | set[str], source : object):
        REM_type_check(literal, (str, set), REM_Parser_Building_Error)
        
        if isinstance(literal, str):
            self.literals.add(literal)
            self.__append_source(literal, source)

        elif isinstance(literal, set):
            self.literals |= literal
            for l in literal:
                self.__append_source(l, source)

        self.__integrity = False

    def remove_rule(self, token : str):
        REM_other_check(token in self.rule_stack, 
                        f"(lexer of '{self.master}'): The token '{token}' is not defined and cannot be removed.",
                        REM_Parser_Building_Error)
        del self.rule_stack[token]
        del self.token_source[token]
        self.__integrity = False

    def update_rule(self, token : str, rule : str | function, source : object):
        try:
            self.add_rule(token, rule, source)

        except REM_Parser_Building_Error:
            if token in self.rule_stack:
                self.remove_rule(token)

            self.add_rule(token, rule, source)
        self.__integrity = False

    
    def rule_t_ID(self, regex = regex_ID) -> function:
        '''
        Get the `t_ID` rule for this lexer.
        Notice: the return funtions are not equal to each other.
        - `regex` : `str`, the regular expression for `ID` token.
        '''
        @TOKEN(regex)
        def t_ID(t):
            t.type = self.reserved.get(t.value, "ID")
            return t 
        return t_ID           

    def build(self):

        self.__build_data = self.BuildData()
        self.build_data.literals = list(self.literals)

        for token in self.rule_stack:
            setattr(self.build_data, f"t_{token}", self.rule_stack[token])

        self.build_data.tokens = list(self.reserved.values()) + self.unreserved_tokens

        self.__lexer = lex.lex(self.build_data)
        self.__integrity = True

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
        Strict equivalence checking is applied on the token definitions to rule out possible ambiguity.
        '''
        REM_type_check(other, PLYLexer, REM_Parser_Building_Error)

        # consistency check
        for reserved_key in other.reserved:
            if reserved_key in self.reserved:
                REM_other_check(other.reserved[reserved_key] == self.reserved[reserved_key], 
                                f"Fusion error. The reserved keyword '{reserved_key}' is defined inconsistently: token '{other.reserved[reserved_key]}' in lexer of '{other.master}' and token '{self.reserved[reserved_key]}' in lexer of '{self.master}'.",
                                REM_Parser_Building_Error)
                
        for reserved_type in other.reserved.values():
            if reserved_type in self.reserved.values():
                self_existing_key = self.get_reserved_key(reserved_type)
                other_existing_key = other.get_reserved_key(reserved_type)
                REM_other_check(self_existing_key == other_existing_key, f"Fusion error. The reserved token '{reserved_type}' is defined inconsistently: keyword '{other_existing_key}' for lexer of '{other.master}' and keyword '{self_existing_key}' for lexer of '{self.master}'.", REM_Parser_Building_Error)

        for token in other.rule_stack:
            if token in self.rule_stack:
                REM_other_check(other.rule_stack[token] == self.rule_stack[token], 
                                f"Fusion error. The token '{token}' is defined inconsistently: rule '{other.rule_stack[token]}' in lexer of '{other.master}' and rule '{self.rule_stack[token]}' in lexer of '{self.master}'.",
                                REM_Parser_Building_Error)


        # fuse the definitions
        self.reserved.update(other.reserved)

        self.rule_stack.update(other.rule_stack)

        self.literals |= other.literals


        # fuse the source information
        for token in other.token_source:
            if token in self.token_source:
                self.token_source[token] += other.token_source[token]
            else:
                self.token_source[token] = other.token_source[token].copy()

        self.__integrity = False






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




    def __init__(self, master : object):
        '''
        About precedence: items with higher precedence will be matched first.
        '''

        self.__parser = None

        # integrity : whether there are modifications after build
        self.__integrity = False

        # the master of this parser
        self.__master = master

        # `rule_source` keep records of the objects that has defined the rules.
        self.rule_source : dict[str, list[object]] = {}

        # `prec_source` keep records of the objects that has defined the precedence.
        self.prec_source : dict[str, list[object]] = {}

        # the record of precedence definitions
        # key: symbol, value: pair of (associativity, precedence)
        self.symbol_prec : dict[str, Tuple[str, int]] = {}

        # the associativity of different precedence
        self.prec_assoc : dict[int, str] = {}


        # the parsing rule stack. A dictionary of (item_name, item_func)
        self.rule_stack : dict[str, FunctionType] = {}
        
        self.__build_data : PLYParser.BuildData | None = None

    @property
    def parser(self):
        if self.__parser is None:
            raise REM_Parser_Building_Error(f"(parser of '{self.master}'): Parser not built.")
        if not self.integrity:
            raise REM_Parser_Building_Error(f"(parser of '{self.master}'): Lack of integrity. Rebuild the parser after modifying it.")
        return self.__parser
    
    @property
    def integrity(self) -> bool:
        return self.__integrity
    
    @property
    def master(self) -> object:
        return self.__master

    @property
    def build_data(self) -> PLYParser.BuildData:
        if self.__build_data is None:
            raise REM_Parser_Building_Error(f"(parser of '{self.master}'): Parser not built.")
        if not self.integrity:
            raise REM_Parser_Building_Error(f"(parser of '{self.master}'): Lack of integrity. Rebuild the parser after modifying it.")

        return self.__build_data
    
    
    def set_precedence(self, symbol : str, prec : int, assoc : str, source : object):
        '''
        Set the precedence of the symbol. #TODO #8
        '''
        REM_type_check(symbol, str, REM_Parser_Building_Error)
        REM_type_check(prec, int, REM_Parser_Building_Error)
        REM_type_check(assoc, str, REM_Parser_Building_Error)

        # valid precedence
        REM_other_check(0 <= prec < PLYParser.MAX_PRECEDENCE, 
                        f"(parser of '{self.master}')(source '{source}'): Rem detected invalid precedence number {prec}. It should be between 0 and {PLYParser.MAX_PRECEDENCE-1}.",
                        REM_Parser_Building_Error)
        
        # valid associativity
        REM_other_check(assoc in ("left", "right", "nonassoc"), 
                        f"(parser of '{self.master}')(source '{source}'): Rem detected invalid associativity '{assoc}'. It should be 'left', 'right' or 'nonassoc'.",
                        REM_Parser_Building_Error)
        
        # consistent associativity
        REM_other_check(self.prec_assoc[prec] == assoc, 
                        f"(parser of '{self.master}')(source '{source}'): The precedence {prec} has been defined with '{self.prec_assoc}' associativity, which is not consistent with the subsequent specification '{assoc}'.",
                        REM_Parser_Building_Error)
        
        # consistent precedence for the symbol
        if symbol in self.symbol_prec:
            REM_other_check(self.symbol_prec[symbol][1] == prec, 
                            f"(parser of '{self.master}')(source '{source}'): The symbol '{symbol}' has been defined with precedence '{self.symbol_prec[symbol][1]}', which is inconsistent with the subsequent specification '{prec}'.",
                            REM_Parser_Building_Error)
        
        # record the source
        if symbol in self.prec_source:
            self.prec_source[symbol].append(source)
        else:
            self.prec_source[symbol] = [source]
        
        # update the precedence setting
        self.symbol_prec[symbol] = (assoc, prec)

        self.__integrity = False
        



    def add_rule(self, rule : function | List[function], source : object):
        '''
        Add a parsing rule to this `PLYParser` instance. The symbol will be automatically extracted from the documentation of the rule function.
        '''

        REM_type_check(rule, (FunctionType, list), REM_Parser_Building_Error)

        if isinstance(rule, FunctionType):

            REM_other_check(rule.__doc__ is not None,
                            f"(parser of '{self.master}')(source '{source}'): Invalid rule function '{rule}'.",
                            REM_Parser_Building_Error)
            
            # extract the symbol automatically
            doc = rule.__doc__
            pos = doc.index(":")
            symbol = doc[:pos].replace("\n","").replace(" ","").replace("\t", "")

            # consistent rule check
            if symbol in self.rule_stack:
                REM_other_check(self.rule_stack[symbol] == rule,
                                f"(parser of '{self.master}')(source '{source}'): The symbol '{symbol}' has the rule definition '{self.rule_stack[symbol]}', which is inconsistent with the subsequent definition '{rule}'.",
                                REM_Parser_Building_Error)
                
            
            # record the source
            if symbol in self.rule_source:
                self.rule_source[symbol].append(source)
            else:
                self.rule_source[symbol] = [source]
                
            self.rule_stack[symbol] = rule

        elif isinstance(rule, list):

            for term in rule:
                self.add_rule(term, source)
            
        self.__integrity = False

            


    def build(self, plylexer : PLYLexer, start_symbol : str | None):
        '''
        - `plylexer` : `PLYLexer`, a built `PLYLexer` instance. `PLYParser` instance will keep a copy of it.
        - `start_symbol` : `str | None`, 
            `str`: the start symbol,
            `None`: dry run, only process the parser information
        '''

        REM_type_check(plylexer, PLYLexer)

        # get a copy
        plylexer = plylexer.copy()


        self.__build_data = PLYParser.BuildData()


        # set the token
        self.build_data.tokens = plylexer.build_data.tokens

        # prepare precedence tab (intermediate representation)
        prec_tab : list[Tuple[str | None, list[str]]] = [(None, [])] * PLYParser.MAX_PRECEDENCE
        for symbol in self.symbol_prec:
            assoc, prec = self.symbol_prec[symbol]
            prec_tab[prec] = (assoc, prec_tab[prec][1] + [symbol])

        # prepare precedence tab (for PLY)
        precedence : list[Tuple[str, ...]] = []
        for assoc, opts in prec_tab:
            if len(opts) == 0:
                continue
            # apply the default value
            if assoc is None:
                assoc = 'right'
            precedence.append((assoc,) + tuple(opts))
        self.build_data.precedence = tuple(precedence)

        for symbol in self.rule_stack:
            setattr(self.build_data, f"p_{symbol}", self.rule_stack[symbol])

        # set the start symbol and build
        if start_symbol is not None:
            self.build_data.start = start_symbol
            self.__parser = yacc.yacc(module=self.build_data)

        # should not be modified after building of parser
        self.__plylexer = plylexer

        self.__integrity = True

    # interface
    def __call__(self, raw : str):
        return self.parser.parse(raw, lexer = self.__plylexer.lexer)
    
    # fusion
    def fuse_append(self, other : PLYParser) -> None:
        '''
        Fuse the two parser definitions.
        It will update the definitions of `other` on `self`.
        Strict equivalence checking is applied on the token definitions to rule out possible ambiguity.
        '''

        REM_type_check(other, PLYParser)

        # consistent precedence associativity
        for prec in other.prec_assoc:
            if prec in self.prec_assoc:
                REM_other_check(other.prec_assoc[prec] == self.prec_assoc[prec], 
                                f"Fusion error. Inconsistent associativity for '{prec}': '{other.prec_assoc[prec]}' in parser of '{other.master}' and '{self.prec_assoc[prec]}' in parser of '{self.master}'.",
                                REM_Parser_Building_Error)
        
        # consistent symbol precedence
        for symbol in other.symbol_prec:
            if symbol in self.symbol_prec:
                REM_other_check(other.symbol_prec[symbol][1] == self.symbol_prec[symbol][1],
                                f"Fusion error. Inconsistent precedence for symbol '{symbol}': '{other.symbol_prec[symbol][1]}' in parser of '{other.master}' and '{self.symbol_prec[symbol][1]}' in parser of '{self.master}'.",
                                REM_Parser_Building_Error)
                
        # consistent rules
        for symbol in other.rule_stack:
            if symbol in self.rule_stack:
                REM_other_check(other.rule_stack[symbol] == self.rule_stack[symbol], 
                                f"Fusion error. The symbol '{symbol}' is defined inconsistently: rule '{other.rule_stack[symbol]}' in parser of '{other.master}' and rule '{self.rule_stack[symbol]}' in parser of '{self.master}'.",
                                REM_Parser_Building_Error)



        # fuse the definitions
        self.symbol_prec.update(other.symbol_prec)
        self.prec_assoc.update(other.prec_assoc)
        self.rule_stack.update(other.rule_stack)

        # fuse the source information
        for symbol in other.prec_source:
            if symbol in self.prec_source:
                self.prec_source[symbol] += other.prec_source[symbol]
            else:
                self.prec_source[symbol] = other.prec_source[symbol].copy()
        for symbol in other.rule_source:
            if symbol in self.rule_source:
                self.rule_source[symbol] += other.rule_source[symbol]
            else:
                self.rule_source[symbol] = other.rule_source[symbol].copy()

        self.__integrity = False


