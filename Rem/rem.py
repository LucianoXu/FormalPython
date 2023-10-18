'''
R.E.M. Reliable Encode Mechanism
レム、ゼロから新世代の形式化ツール！

'''

from __future__ import annotations

from typing import Type, Tuple, Any, TypeVar
from types import FunctionType

import inspect
import os

from .rem_error import REM_Error


# a set of default lexing/parsing rules
from . import syntax_parsing as syn



class REMSystem:
    '''
    Every instance represents a REM system.
    '''
    def __init__(self):
        self.counter = 2
        self.registered : list[Type[RemTerm]] = [RemTerm, RemProof]

        self.lexer : syn.PLYLexer = syn.PLYLexer(empty_mode=True)
        self.parser : syn.PLYParser = syn.PLYParser(empty_mode=True)

    def lexer_reserved(self, reserved_type : str, reserved_key : str):
        self.lexer.add_reserved(reserved_type, reserved_key)

    def lexer_token(self, token : str, rule : str | Any):
        self.lexer.add_rule(token, rule)
        
    def lexer_literals(self, literal : str | list[str]):
        self.lexer.add_literals(literal)

    def parser_set_start(self, start : str):
        self.parser.set_start(start)

    def parser_set_precedence(self, term : str, prec : int, assoc : str):
        self.parser.set_precedence(term, prec, assoc)

    def parser_rule(self, rule : Any):
        self.parser.add_rule(rule)


    def get_doc(self) -> str:
        '''
        Return the documentation of this Rem system.
        '''

        res = ""
        for item in self.registered:
            res += Rem_term_describe(item) + "\n\n"

        return res

    



class RemTerm:
    '''
    Rem-term
    ```
    _
    ```

    The meta term for objects in REM itself.
    All objects are by default abstract and cannot be instantiated.
    Use `@concrete_Rem_term` decorator to transform a class to concrete one.
    '''
    Rem_term_name : str = 'Rem-term'
    Rem_term_def : str  = '_'
    term_order : int    = 0

    # if this parsing rule (a function for ply) is given, it will be used to automatically construct the parsing system for this term.
    # reload this object as a staticmethod to define the parsing rule for subterms.
    parsing_rule : None | FunctionType = None

    @property
    def describe(self) -> str:
        '''
        Output a description for the Rem term.
        '''
        return Rem_term_describe(self)

    def __new__(cls, *args, **kwargs):
        raise REM_Error(f"Cannot instantiate abstract proof object {cls}.")

    def is_concrete(self) -> bool:
        return False
    
    def Rem_type_check(self, obj, T : Type | Tuple[Type, ...], term : str) -> None:
        '''
        Checks whether object `obj` has the type `T`. It should serve as the term for `term` in the meta system.
        Raise a `REM_Error` when the type does not match.
        This is intended for the check for correct operations.
        '''

        if isinstance(T, tuple):
            for t in T:
                if isinstance(obj, t):
                    return
            
            raise REM_Error("\n({}): The term '{}' should have the type in \n\n'{}'\n\nbut Rem found the instantiation \n\n'{}'\n\nactually has type \n\n'{}'\n\n Rem reminds you of the rule.\n{}".format(self.Rem_term_name, term, T, obj, type(obj), self.Rem_term_def))

        elif not isinstance(obj, T):
            raise REM_Error("\n({}): The term '{}' should have the type \n\n'{}'\n\nbut Rem found the instantiation \n\n'{}'\n\nactually has type \n\n'{}'\n\n Rem reminds you of the rule.\n{}".format(self.Rem_term_name, term, T, obj, type(obj), self.Rem_term_def))
        

    def Rem_consistency_check(self, a, b, term : str) -> None:
        '''
        Checks whether `a == b` holds. They should both serve as the terms for `term` in the meta system.
        Raise a `REM_Error` when `a != b`.
        This is intended for the check of object consistency for correct operations.
        '''

        if a != b:
            raise REM_Error("\n({}): Rem found the instantiations for the term '{}' are not consistent: \n\n'{}'\n\nand\n\n'{}'\n\nRem reminds you of the rule.\n{}".format(self.Rem_term_name, term, a, b, self.Rem_term_def))
        
    def Rem_other_check(self, expr : bool, reason : str) -> None:
        '''
        If the `expr` does not hold, it will raise a formated error with information `reason`.
        This is intended for the check for correct operations.
        '''
        if not expr:
            raise REM_Error("\n({}): Rem does not accept because: \n\n{}\n\nRem reminds you of the rule.\n{}".format(self.Rem_term_name, reason, self.Rem_term_def))

    
T = TypeVar('T', bound = RemTerm)
def Rem_term(rem_sys : REMSystem):
    def real_dec(cls : Type[T]) -> Type[T]:
        '''
        Parse Rem term information from the docstring of `RemTerm` subclasses.
        The docstring should be of form:
        ```
        Rem-term-name
        "```"
        Rem-term-def
        "```"
        intro-string ...
        ```
        '''
        
        # register
        cls.term_order = rem_sys.counter
        rem_sys.counter += 1
        rem_sys.registered.append(cls)

        doc : str| None = cls.__doc__
        try:
            if doc is None:
                raise ValueError()
            pos1 = doc.index("```")
            cls.Rem_term_name = doc[:pos1].replace("\n","").replace("\t","").replace(" ","")

            doc = doc[pos1 + len("```"):]
            pos2 = doc.index("```")
            cls.Rem_term_def = doc[:pos2]
        except ValueError:
            raise Exception(f"Cannot process the Rem-term information of class {cls}.")


        return cls
    return real_dec    


def concrete_Rem_term(rem_sys : REMSystem):
    def real_dec(cls : Type[T]) -> Type[T]:
        '''
        Decorator for concrete Rem terms: reload the definition for `__new__` in the class definition by:
        ```Python
        def __new__(cls, *args, **kwargs):
            return object.__new__(cls)
        ```
        '''

        # process Rem_term informations
        cls = Rem_term(rem_sys)(cls)

        def concrete_new(cls, *args, **kwargs):
            return object.__new__(cls)

        cls.__new__ = concrete_new
        cls.is_concrete = lambda self: True
        
        return cls
    
    return real_dec


class RemProof(RemTerm):
    '''
    Rem-proof
    ```
    _
    ```
    The proof objects in REM.
    '''
    Rem_term_name   = 'Rem-proof'
    Rem_term_def    = '_'
    term_order      = 1

    def premises(self) -> str:
        raise NotImplementedError()
    
    def conclusion(self) -> str:
        raise NotImplementedError()
    
    def full_proof(self) -> str:
        space_len = len(self.Rem_term_name) + 3

        # indent, premise
        res = " " * space_len + self.premises()
        if res[-1] == "\n":
            res = res[:-1]
        res = res.replace("\n", "\n" + " " * space_len)
        res += "\n"

        # line
        res += f"({self.Rem_term_name}) " + "-"*40 + "\n" 

        # indent conclusion
        res += " " * space_len + self.conclusion() 
        return res
    
    def __str__(self) -> str:
        return self.conclusion()
    


####################################################################
# tools for organizing layered lexing/parsing
# powered by ply

from ply import lex, yacc




####################################################################
# methods on Rem system

def Rem_term_describe(mt : RemTerm | Type[RemTerm]) -> str:
    '''
    Output a description for the Rem term.
    '''
    return f"({mt.Rem_term_name}):" + "\n" + mt.Rem_term_def


def get_Rem_subclass(GLOBAL : dict[str, Any]) -> list[Type[RemTerm]]:
    '''
    For the given global namespace `GLOBAL`, it return all `RemTerm` subclasses in a sorted list.
    '''
    Rem_terms = list(filter(
        lambda obj : inspect.isclass(obj) and issubclass(obj, RemTerm),GLOBAL.values()
    ))
    Rem_terms.sort(key=lambda x: x.term_order)
    return Rem_terms


def Rem_system_build(rem_sys : REMSystem, file : str = "", build_parser : bool = False) -> None:
    '''
    Checks whether the Rem system given by `rem_sys` is well formed, prepare the lexer/parser components and generate the doc.

    - `rem_sys` : `REMSystem`.
    - `file` : should pass in the `__file__` result
    - `build_parser` : `bool`, whether to build the parser.
    '''        

    if build_parser:
        # build the lexer
        rem_sys.lexer.build()

        # collect the parsing rules
        for cls in rem_sys.registered:
            if cls.parsing_rule is not None:
                rem_sys.parser_rule(cls.parsing_rule)
        
        # build the parser
        rem_sys.parser.build(rem_sys.lexer)


    # produce the rule doc
    with open(os.path.join(os.path.dirname(file),"REM_rule.txt"), "w", encoding="utf-8") as p:
        p.write(rem_sys.get_doc())
