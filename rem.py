'''
R.E.M. Reliable Encode Mechanism
レム、ゼロから新世代の形式化ツール！

'''

from __future__ import annotations

from typing import Type, Tuple, Any, TypeVar, Sequence, List
from types import FunctionType

import inspect
import os

from .rem_error import REM_Error, REM_type_check, REM_other_check


# a set of default lexing/parsing rules
from . import syntax_parsing as syn

    

def is_subterm_class(A : Type, B : Type) -> bool:
    '''
    Recursively decides whether `A` is a subterm class of `B`.
    '''
    if issubclass(A, B):
        return True
    
    if issubclass(A, RemTerm) and issubclass(B, RemTerm):
        for cls in A.super_term:
            if is_subterm_class(cls, B):
                return True
        
    return False

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
    Rem_term_name : str
    Rem_term_def : str
    term_order : int
    Rem_term_count : int = 0

    # if this parsing rule (a function for ply) is given, it will be used to automatically construct the parsing system for this term.
    # reload this object as a staticmethod to define the parsing rule for subterms.
    parsing_rule : None | function = None

    # if not `None`, it will add the literals to the `REMTheory` lexer.
    lexing_literals : None | List[str] = None

    # this attribute contains all the super terms of the current term. It will be used in type check of term instances and REM system fusion.
    super_term : set[Type[RemTerm]] = set()


    def __eq__(self, other) -> bool:
        '''
        Disable default equivalence judgement.
        '''
        raise NotImplementedError()


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
    
    def is_subterm(self, superterm : Type) -> bool:
        '''
        Check whether this term is a subterm of `superterm` class.
        It is decided by `super_term` attribute of the current class.
        '''
        return is_subterm_class(self.__class__, superterm)
    
    def Rem_type_check(self, obj, T : Type | Tuple[Type, ...], term : str) -> None:
        '''
        Checks whether object `obj` is a subterm of the type `T`.
        Raise a `REM_Error` when the type does not match.
        This is intended for the check for correct operations.
        '''
        # for `RemTerm` subclasses
        if inspect.isclass(obj):
            if isinstance(T, tuple):
                for t in T:
                    if is_subterm_class(obj, t):
                        return
                
                raise REM_Error("\n({}): The term '{}' should be a subclass of some type in \n\n'{}'\n\nbut Rem found the instantiation \n\n'{}\n\n'{}'\n\n Rem reminds you of the rule.\n{}".format(self.Rem_term_name, term, T, obj, self.Rem_term_def))
            
            elif not is_subterm_class(obj, T):
                raise REM_Error("\n({}): The term '{}' should be a subclass of \n\n'{}'\n\nbut Rem found the instantiation \n\n'{}'\n\n\n\n Rem reminds you of the rule.\n{}".format(self.Rem_term_name, term, T, obj, self.Rem_term_def))

        # for `RemTerm` terms, we do the subterm check
        else:
            if isinstance(T, tuple):
                for t in T:
                    if is_subterm_class(type(obj), t):
                        return
                
                raise REM_Error("\n({}): The term '{}' should be a subterm of some type in \n\n'{}'\n\nbut Rem found the instantiation \n\n'{}'\n\nactually has type \n\n'{}'\n\n Rem reminds you of the rule.\n{}".format(self.Rem_term_name, term, T, obj, type(obj), self.Rem_term_def))
            
            elif not is_subterm_class(type(obj), T):
                raise REM_Error("\n({}): The term '{}' should be a subterm of \n\n'{}'\n\nbut Rem found the instantiation \n\n'{}'\n\nactually has type \n\n'{}'\n\n Rem reminds you of the rule.\n{}".format(self.Rem_term_name, term, T, obj, type(obj), self.Rem_term_def))
        

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
        

###################################################################
# methods on RemTerm


def Rem_term_describe(mt : RemTerm | Type[RemTerm]) -> str:
    '''
    Output a description for the Rem term.
    '''
    return f"({mt.Rem_term_name}):" + "\n" + mt.Rem_term_def


###################################################################
# decorators for initialization pocessing
    
T = TypeVar('T', bound = RemTerm)
def Rem_term(cls : Type[T]) -> Type[T]:
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

    # the automated ordering of `RemTerm` subclass definitions
    cls.term_order = RemTerm.Rem_term_count
    RemTerm.Rem_term_count += 1    

    # automatically add the super term, only `RemTerm` superclasses are considered.
    cls.super_term = cls.super_term | set(
        filter(
            lambda x: issubclass(x, RemTerm), 
            cls.__bases__
        )
    )

    doc : str| None = cls.__doc__
    try:
        if doc is None:
            raise Exception(f"Cannot introduce the class {cls.__name__} into Rem-system: no documentation string provided.")
        
        pos1 = doc.index("```")
        cls.Rem_term_name = doc[:pos1].replace("\n","").replace("\t","").replace(" ","")

        doc = doc[pos1 + len("```"):]
        pos2 = doc.index("```")
        cls.Rem_term_def = doc[:pos2]
    except ValueError:
        raise Exception(f"Cannot process the Rem-term information of class {cls}.")


    return cls

# process superclass `RemTerm`
RemTerm = Rem_term(RemTerm)

def concrete_Rem_term(cls : Type[T]) -> Type[T]:
    '''
    Decorator for concrete Rem terms: reload the definition for `__new__` in the class definition by:
    ```Python
    def __new__(cls, *args, **kwargs):
        return object.__new__(cls)
    ```
    '''

    # process Rem_term informations
    cls = Rem_term(cls)

    def concrete_new(cls, *args, **kwargs):
        return object.__new__(cls)

    cls.__new__ = concrete_new
    cls.is_concrete = lambda self: True
    
    return cls



##############################################################################
# Theory and functor

@Rem_term
class REMTheory(RemTerm):
    '''
    rem-theory
    ```
        theory1, theory2, ...
        ---------------------
        theory
    ```
    A `REMTheory` subclass represents a theory type in REM.
    
    Every instance of `REMTheory` subclasses represents an instance of this theory.

    All `RemTerm` subclass attributes of `REMTheory` subclasses will be considered as terms in the corresponding theory.
    '''
    def __init__(self):

        self.__lexer : syn.PLYLexer = syn.PLYLexer(empty_mode=True)
        self.__parser : syn.PLYParser = syn.PLYParser(empty_mode=True)

    @property
    def theories(self) -> list[Type[RemTerm]]:
        Rem_terms = list(filter(
            lambda obj : (inspect.isclass(obj) and issubclass(obj, RemTerm)),
            self.__dict__.values()
        ))
        Rem_terms.sort(key=lambda x: x.term_order)
        return Rem_terms

    @property
    def lexer(self) -> syn.PLYLexer:
        return self.__lexer
    
    @property
    def parser(self) -> syn.PLYParser:
        return self.__parser

    
    def build_parser(self, parser_start : str | None) -> None:
        '''
        Prepare the lexer/parser components.

        - `start_symbol` : `str | None`, 
            `str`: the start symbol,
            `None`: dry run, only process the parser information
        '''        

        # collect the parsing rules
        for cls in self.theories:
            # literals for lexer
            if cls.lexing_literals is not None:
                self.lexer.add_literals(cls.lexing_literals)

            # rules for parser
            if cls.parsing_rule is not None:
                self.parser.add_rule(cls.parsing_rule)
                
        # build the lexer
        self.lexer.build()
        
        # build the parser
        self.parser.build(self.lexer, parser_start)


    def fuse_append(self, other : REMTheory) -> None:
        '''
        Fuse two `REMSystem` instances.
        '''

        for term in other.theories:
            self.__setattr__(term.__name__, term)

        # fuse the lexing/parsing rule set
        self.__lexer.fuse_append(other.lexer)
        self.__parser.fuse_append(other.parser)


    def get_doc(self) -> str:
        '''
        Return the documentation of this Rem system.
        '''

        res = ""
        for item in self.theories:
            res += Rem_term_describe(item) + "\n\n"

        return res
    
    def gen_doc(self, path : str) -> None:
        '''
        Produce the rule documentation.

        - `path` : `str`, the path to the output file.
        '''
        with open(path, "w", encoding="utf-8") as p:
            p.write(self.get_doc())