

from __future__ import annotations

from typing import Tuple, List, Dict
from types import FunctionType
from graphviz import Digraph


from ply import lex, yacc
from ply.lex import TOKEN

from .syntax_rules import *

from ..rem_error import REM_Parser_Building_Error, REM_type_check, REM_other_check

import os


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
        self.__lexer : lex.Lexer | None = None

        # whether the lexer is modified after preparing build data
        self.__modified : bool = True

        # the master of this lexer
        self.__master = master

        # `token_source` keep records of the objects that has defined the tokens.
        self.token_source : dict[str, list[object]] = {}

        # lexing rule stack
        self.reserved : dict[str, str] = {}
        self.normal_token_stack : dict[str, str | function] = {}
        self.literals : set[str] = set()

        self.__build_data : PLYLexer.BuildData | None = None


    @property
    def lexer(self) -> lex.Lexer:
        if self.modified or self.__lexer is None:
            self.build()

        assert self.__lexer is not None

        return self.__lexer
    
    @property
    def modified(self) -> bool:
        return self.__modified
    
    @property
    def unreserved_tokens(self) -> list[str]:
        '''
        return the tokens defined not as reserved (meta-reserved tokens like "ignore" and "COMMENT" are ruled out)
        '''
        res = list(self.normal_token_stack.keys())
        for token in res:
            if token in meta_reserved_token:
                res.remove(token)
        return res

    @property
    def master(self) -> object:
        return self.__master

    @property
    def build_data(self) -> PLYLexer.BuildData:
        if self.modified:
            self.prepare_build_data()

        assert self.__build_data is not None

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

    def add_reserved(self, reserved_type : str, reserved_key : str):
        '''
        Reserved keywords will be detected before `t_ID`.
        - `reserved_type` : The type of the reserved token.
        - `reserved_key` : The reserved keyword.
        '''
        REM_type_check(reserved_key, str, REM_Parser_Building_Error)
        REM_type_check(reserved_type, str, REM_Parser_Building_Error)

        if reserved_type in self.normal_token_stack:
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}'): The token '{reserved_type}' has been defined as the rule '{self.normal_token_stack[reserved_type]}'.")

        # consistent keyword for tokens
        if reserved_type in self.reserved.values():
            existing_key = self.get_reserved_key(reserved_type)
            REM_other_check(existing_key == reserved_key, f"(lexer of '{self.master}'): Token '{reserved_type}' bas been defined as '{existing_key}', which is not consistent with the subsequent definition '{reserved_key}'.", REM_Parser_Building_Error)

        # unique token for keywords
        elif reserved_key in self.reserved:
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}'): The reserved word '{reserved_key}' has been defined for token '{self.reserved[reserved_key]}'.")
        
        # record the source
        self.__append_source(reserved_type, self.master)      

        self.reserved[reserved_key] = reserved_type

        self.__modified = True

    def add_normal_token(self, token : str, rule : str | function):
        REM_type_check(token, str, REM_Parser_Building_Error)
        REM_type_check(rule, (str, FunctionType), REM_Parser_Building_Error)

        if token in self.normal_token_stack:
            REM_other_check(self.normal_token_stack[token] == rule,
                f"(lexer of '{self.master}'): The token '{token}' has been defined as '{self.normal_token_stack[token]}', which is not consistent with the subsequent definition '{rule}'.", REM_Parser_Building_Error)
        
        # consistent rules for tokens
        if token in self.reserved.values():
            raise REM_Parser_Building_Error(f"(lexer of '{self.master}'): The token '{token}' has been defined as a reserved word for '{self.get_reserved_key(token)}'.")
            
        # record the source
        self.__append_source(token, self.master)

        if isinstance(rule, FunctionType):
            rule.__name__ = f"t_{token}"

        self.normal_token_stack[token] = rule

        self.__modified = True

        
    def add_literals(self, literal : str | set[str]):
        REM_type_check(literal, (str, set), REM_Parser_Building_Error)
        
        if isinstance(literal, str):
            self.literals.add(literal)
            self.__append_source(literal, self.master)

        elif isinstance(literal, set):
            self.literals |= literal
            for l in literal:
                self.__append_source(l, self.master)

        self.__modified = True

    def remove_token(self, token : str):
        '''
        Removes the reserved, normal or literal token.
        '''
        if token in self.reserved.values():
            del self.reserved[self.get_reserved_key(token)]
        elif token in self.normal_token_stack:
            del self.normal_token_stack[token]
        elif token in self.literals:
            self.literals -= {token}
        else:
            REM_other_check(False, 
                        f"(lexer of '{self.master}'): The token '{token}' is not defined and cannot be removed.",
                        REM_Parser_Building_Error)
        
        del self.token_source[token]
        self.__modified = True

    
    def token_t_ID(self, regex = regex_ID) -> function:
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

    def prepare_build_data(self):
        self.__build_data = self.BuildData()
        self.__build_data.literals = list(self.literals)

        for token in self.normal_token_stack:
            setattr(self.__build_data, f"t_{token}", self.normal_token_stack[token])

        self.__build_data.tokens = list(self.reserved.values()) + self.unreserved_tokens

        self.__modified = False

    def build(self):
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

        for token in other.normal_token_stack:
            if token in self.normal_token_stack:
                REM_other_check(other.normal_token_stack[token] == self.normal_token_stack[token], 
                                f"Fusion error. The token '{token}' is defined inconsistently: rule '{other.normal_token_stack[token]}' in lexer of '{other.master}' and rule '{self.normal_token_stack[token]}' in lexer of '{self.master}'.",
                                REM_Parser_Building_Error)


        # fuse the definitions
        self.reserved.update(other.reserved)

        self.normal_token_stack.update(other.normal_token_stack)

        self.literals |= other.literals


        # fuse the source information
        for token in other.token_source:
            if token in self.token_source:
                self.token_source[token] += other.token_source[token]
            else:
                self.token_source[token] = other.token_source[token].copy()

        self.__modified = True






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
    # About precedence: items with higher precedence will be matched first.

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




    def __init__(self, plylexer : PLYLexer | None, start_symbol : str | None, master : object):
        '''
        - `start_symbol` : `str | None`, 
            `str`: the start symbol,
            `None`: dry run, only process the parser information
        '''

        self.__parser = None

        # integrity : whether the parser is modified after preparing build data
        self.__modified = True

        # the lexer bound to this parser

        REM_type_check(plylexer, (PLYLexer, type(None)), REM_Parser_Building_Error)
        self.__plylexer = plylexer

        REM_type_check(start_symbol, (str, type(None)), REM_Parser_Building_Error)
        self.__start_symbol = start_symbol


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
        self.rule_stack : List[FunctionType] = []
        
        self.__build_data : PLYParser.BuildData | None = None

    @property
    def bound_plylexer(self) -> PLYLexer:
        REM_other_check(self.__plylexer is not None,
                        f"(parser of '{self.master}'): No lexer bound to this parser.",
                        REM_Parser_Building_Error)
        assert self.__plylexer is not None
        return self.__plylexer

    @property
    def parser(self):
        REM_other_check(self.__start_symbol is not None,
                        f"(parser of '{self.master}'): The start symbol of this parser is 'None'.",
                        REM_Parser_Building_Error)
        if self.modified:
            self.build()

        assert self.__parser is not None
        return self.__parser
    
    @property
    def modified(self) -> bool:
        if self.__plylexer is None:
            return self.__modified
        return self.__plylexer.modified or self.__modified
    
    @property
    def master(self) -> object:
        return self.__master

    @property
    def build_data(self) -> PLYParser.BuildData:
        if self.modified:
            self.prepare_build_data()

        assert self.__build_data is not None
        return self.__build_data
    
    @property
    def start_symbol(self) -> str | None:
        return self.__start_symbol
    
    def set_start_symbol(self, start_symbol : str | None):
        self.__start_symbol = start_symbol
        self.__modified = True
    
    def set_precedence(self, symbol : str, prec : int, assoc : str):
        '''
        Set the precedence of the symbol.
        '''
        REM_type_check(symbol, str, REM_Parser_Building_Error)
        REM_type_check(prec, int, REM_Parser_Building_Error)
        REM_type_check(assoc, str, REM_Parser_Building_Error)

        # valid precedence
        REM_other_check(0 <= prec < PLYParser.MAX_PRECEDENCE, 
                        f"(parser of '{self.master}'): Rem detected invalid precedence number {prec}. It should be between 0 and {PLYParser.MAX_PRECEDENCE-1}.",
                        REM_Parser_Building_Error)
        
        # valid associativity
        REM_other_check(assoc in ("left", "right", "nonassoc"), 
                        f"(parser of '{self.master}'): Rem detected invalid associativity '{assoc}'. It should be 'left', 'right' or 'nonassoc'.",
                        REM_Parser_Building_Error)
        
        # consistent associativity
        if prec in self.prec_assoc:
            REM_other_check(self.prec_assoc[prec] == assoc, 
                        f"(parser of '{self.master}'): The precedence {prec} has been defined with '{self.prec_assoc}' associativity, which is not consistent with the subsequent specification '{assoc}'.",
                        REM_Parser_Building_Error)
        
        # consistent precedence for the symbol
        if symbol in self.symbol_prec:
            REM_other_check(self.symbol_prec[symbol][1] == prec, 
                            f"(parser of '{self.master}'): The symbol '{symbol}' has been defined with precedence '{self.symbol_prec[symbol][1]}', which is inconsistent with the subsequent specification '{prec}'.",
                            REM_Parser_Building_Error)
        
        # record the source
        if symbol in self.prec_source:
            self.prec_source[symbol].append(self.master)
        else:
            self.prec_source[symbol] = [self.master]
        
        # update the precedence setting
        self.symbol_prec[symbol] = (assoc, prec)
        self.prec_assoc[prec] = assoc

        self.__modified = True
        



    def add_rule(self, rule : function | List[function]):
        '''
        Add a parsing rule to this `PLYParser` instance. The symbol will be automatically extracted from the documentation of the rule function.
        '''

        REM_type_check(rule, (FunctionType, list), REM_Parser_Building_Error)

        if isinstance(rule, FunctionType):

            REM_other_check(rule.__doc__ is not None,
                            f"(parser of '{self.master}'): Invalid rule function '{rule}'.",
                            REM_Parser_Building_Error)
            
            # extract the symbol automatically
            doc = rule.__doc__
            pos = doc.index(":")
            symbol = doc[:pos].replace("\n","").replace(" ","").replace("\t", "")                
            
            # record the source
            if symbol in self.rule_source:
                self.rule_source[symbol].append(self.master)
            else:
                self.rule_source[symbol] = [self.master]
                
            self.rule_stack.append(rule)

        elif isinstance(rule, list):

            for term in rule:
                self.add_rule(term)
            
        self.__modified = True

            
    def prepare_build_data(self):

        self.__build_data = PLYParser.BuildData()

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
        self.__build_data.precedence = tuple(precedence)

        for i in range(len(self.rule_stack)):
            setattr(self.__build_data, f"p_rule{i}", self.rule_stack[i])

    def build(self):


        REM_other_check(self.__start_symbol is not None,
                        f"(parser of '{self.master}'): The start symbol is set to 'None'.",
                        REM_Parser_Building_Error)
        assert self.__start_symbol is not None
        
        self.prepare_build_data()
        assert self.__build_data is not None

        # set the token
        self.__build_data.tokens = self.bound_plylexer.build_data.tokens

        # set the start symbol and build
        self.__build_data.start = self.__start_symbol

        #########################
        # BUILD PARSER

        self.__parser = yacc.yacc(
            module=self.__build_data, 
            check_recursion=False, 
            write_tables=False )

        self.__modified = False

    # interface
    def __call__(self, raw : str):
        return self.parser.parse(raw, lexer = self.bound_plylexer.lexer)
    
    # fusion
    def fuse_append(self, other : PLYParser) -> None:
        '''
        Fuse the two parser definitions.
        It will update the definitions of `other` on `self`.
        '''

        REM_type_check(other, PLYParser, REM_Parser_Building_Error)

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
                

        # fuse the definitions
        self.symbol_prec.update(other.symbol_prec)
        self.prec_assoc.update(other.prec_assoc)

        # rules are kept unique
        for rule in other.rule_stack:
            if rule not in self.rule_stack:
                self.rule_stack.append(rule)

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

        self.__modified = True


from ..network import NetworkNode

class ParserNode(NetworkNode["ParserNode"]):

    def __init__(self, start_symbol : str | None, master : object):
        '''
        If `start_symbol` is set to `None`, then the ParserNode is a rule set and cannot be compiled.
        '''

        # create an isolated parser node
        super().__init__(set())


        self.__master = master

        self.set_start_symbol(start_symbol)

        self.__node_plylexer = PLYLexer(master)
        self.__node_plyparser = PLYParser(None, None, master)

        self.__plylexer : PLYLexer | None = None
        self.__plyparser : PLYParser | None = None

        self.__modified = True

    def __str__(self) -> str:
        return f"Parser: {self.__master}"


    def set_start_symbol(self, start_symbol : str | None):
        REM_type_check(start_symbol, (str, type(None)), REM_Parser_Building_Error)
        self.__start_symbol = start_symbol
        self.__modified = True

    @property
    def modified(self) -> bool:
        for node in self.downstream_nodes:
            if node.__node_plylexer.modified or node.__node_plyparser.modified or node.__modified:
                return True
            
        return False
    
    @property
    def node_plylexer(self) -> PLYLexer:
        return self.__node_plylexer
    
    @property
    def node_plyparser(self) -> PLYParser:
        return self.__node_plyparser
    
    @property
    def plylexer(self) -> PLYLexer:
        if self.modified:
            self.build()

        assert self.__plylexer is not None
        return self.__plylexer

    @property
    def plyparser(self) -> PLYParser:
        if self.modified:
            self.build()
        
        assert self.__plyparser is not None
        return self.__plyparser

    def build(self, traveled : Tuple[ParserNode, ...] = ()) -> None:

        # change modification tag at the beginning to avoid the spread of modified node detection due to loops.

        # self.connected_nw().draw(self, "output")

        self.__modified = False


        self.__plylexer = PLYLexer(self.__master)
        self.__plyparser = PLYParser(self.__plylexer, self.__start_symbol, self.__master)


        if self not in traveled:
            for node in self.sub_nodes:

                if node.modified:
                    node.build(traveled + (self,))

                assert node.__plylexer is not None
                assert node.__plyparser is not None

                self.__plylexer.fuse_append(node.__plylexer)
                self.__plyparser.fuse_append(node.__plyparser)

                # add the bridge generation rule between parser nodes
                # for those with start symbol specified
                if self.__start_symbol and node.__start_symbol is not None:

                    # the bridge function
                    def bridge_rule(p):
                        p[0] = p[1]

                    bridge_rule.__doc__ = f"{self.__start_symbol} : {node.__start_symbol}"

                    self.__plyparser.add_rule(bridge_rule)



        self.__plylexer.fuse_append(self.__node_plylexer)
        self.__plyparser.fuse_append(self.__node_plyparser)

    def get_doc(self) -> str:
        res = ""
        for rule in self.plyparser.rule_stack:
            res += f"\n{rule.__doc__}\n"

        return res




class ParserHost:
    def __init__(self, symbol : str | None):
        self._parser_node = ParserNode(symbol, self)


    @property
    def parser_node(self) -> ParserNode:
        return self._parser_node
    
    @property
    def lexer(self) -> PLYLexer:
        return self.parser_node.plylexer
    
    @property
    def parser(self) -> PLYParser:
        '''
        The integrated parser.
        This `PLYParser` property is callable (as a parser).
        '''
        return self.parser_node.plyparser
    
    # for node lexer

    def add_reserved(self, reserved_type : str, reserved_key : str):
        self._parser_node.node_plylexer.add_reserved(reserved_type, reserved_key)

    def add_normal_token(self, token : str, rule : str | function):
        self._parser_node.node_plylexer.add_normal_token(token, rule)

    def add_literals(self, literal : str | set[str]):
        self._parser_node.node_plylexer.add_literals(literal)

    def remove_token(self, token : str):
        self._parser_node.node_plylexer.remove_token(token)

    def token_t_ID(self, regex = regex_ID):
        self._parser_node.node_plylexer.token_t_ID(regex)

    # for node parser

    def set_precedence(self, symbol : str, prec : int, assoc : str):
        self._parser_node.node_plyparser.set_precedence(symbol, prec, assoc)

    def add_rule(self, rule : function | List[function]):
        self._parser_node.node_plyparser.add_rule(rule)

    # for ParserNode
    
    def set_start_symbol(self, start_symbol : str | None):
        self._parser_node.set_start_symbol(start_symbol)

    def get_parser_doc(self) -> str:
        return self._parser_node.get_doc()

