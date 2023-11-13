'''
R.E.M. Reliable Encode Mechanism
レム、ゼロから新世代の形式化ツール！

[formalization framework based on order-sorted universal algebra]
'''

from __future__ import annotations

from typing import Type, Tuple, Any, TypeVar, Sequence, List, Generic, Callable

from types import FunctionType

import inspect
import os
import copy

from . import syn

from .rem_error import REM_META_Error, REM_CONSTRUCTION_Error, REM_type_check, REM_other_check, REM_warning

from .network import NetworkNode

class RemSort(NetworkNode, syn.ParserHost):
    '''
    The sorts in Rem system.
    One important feature is that every sort itself can also be a signature.
    '''
    def __init__(self, name : str, symbol : str | None = None, super_sorts : Tuple[RemSort, ...] = ()):

        syn.ParserHost.__init__(self, symbol)
        NetworkNode.__init__(self, super_sorts)

        if not isinstance(name, str):
            raise REM_META_Error(f"The object '{name}' is not a valid name for this sort. It should be a string.")
        self.__name : str = name
        
        if not isinstance(super_sorts, tuple):
            raise REM_META_Error(f"({self.name}): The super sorts should be a tuple.")
        
        for sort in super_sorts:
            if not isinstance(sort, RemSort):
                raise REM_META_Error(f"({self.name}): The super sort '{sort}' is not an instance of class RemSort.")
            

        self.__name : str = name

        # the documentation attribute
        self.doc : str | None = None


    @property
    def name(self) -> str:
        return self.__name
    
    
    #############################################
    # Manipulation of sort network

    def append_super_sort(self, super_sort : RemSort):
        self.set_super_node(super_sort)
        self.parser_node.set_super_node(super_sort.parser_node)


    #############################################
    # checkings


    def well_typed(self, term : RemTerm) -> bool:
        '''
        Return whether the `RemTerm` term is of type `self`.
        The judgement depends on the calculated reflexive, transitive closure of super sorts.
        '''
        if not isinstance(term, RemTerm):
            raise REM_META_Error(f"The term '{term}' is not an instance of RemTerm class.")
        
        return self in term.sort.upstream_nodes
    
    def __str__(self) -> str:
        return self.name

    def __eq__(self, __value: object) -> bool:
        '''
        Two sorts are considered identical only if they are the same Python object.
        '''
        return __value is self
    

# the type variable suggesting different types of sort-term-functions
T_Sort = TypeVar("T_Sort", bound = RemSort)
T_Term = TypeVar("T_Term", bound = "RemTerm")

class RemTerm(Generic[T_Sort, T_Term]):
    '''
    A term in the signature.
    '''
    def __init__(self, fun : RemFun[T_Sort, T_Term], *paras : T_Term):
        self.__fun = fun
        self.__paras = paras

    @property
    def fun(self) -> RemFun[T_Sort, T_Term]:
        return self.__fun
    
    @property
    def paras(self) -> Tuple[T_Term, ...]:
        return self.__paras

    @property
    def sort(self) -> T_Sort:
        return self.__fun.domain_sort
    
    def __eq__(self, __value: object) -> bool:
        if __value is self:
            return True
        elif isinstance(__value, RemTerm):
            return __value.__fun == self.__fun and __value.__paras == self.__paras
        else:
            return False

    # reassign this attribute to define the custom printing
    format_str : None | Callable[[RemTerm[T_Sort, T_Term]],str] = None

    def __str__(self) -> str:
        # default printing
        if self.format_str is None:
            res = f"{self.fun.name}()"
            if self.fun.arity > 0:
                res += f"({self.paras[0]}"
                for i in range(1, len(self.paras)):
                    res += f", {self.paras[i]}"
                res += ")"
            return res
        
        # custom printing
        else:
            return self.format_str(self)
        


    ###########################################################
    # printing

    def ctx_str(self, super_fun : RemFun[T_Sort, T_Term], left : bool = True) -> str:
        '''
        Use `ctx_str` instead of `__str__` to compose the printing when this term may need enclosing.

        According to the context of `super_fun`, decide whether enclose the string of itself, and return the result.
        - `left`: for binary operators only. whether this term is the left one or the right one.
        '''

        if super_fun.precedence is None or self.fun.precedence is None:
            return str(self)
        elif super_fun.precedence[1] > self.fun.precedence[1]:
            return self.fun.enclosed(str(self))
        elif super_fun.precedence[1] < self.fun.precedence[1]:
            return str(self)
        else:
            # equal precedence
            if (self.fun.precedence[2] == 'left' and left == False)\
            or (self.fun.precedence[2] == 'right' and left == True):
                return self.fun.enclosed(str(self))
            else:
                return str(self)



class RemFun(syn.ParserHost, Generic[T_Sort, T_Term]):
    '''
    The functions in Rem system.
    '''

    # this static attribute controls the type of constructed term
    sort_type : Type[RemSort] = RemSort
    term_type : Type[RemTerm] = RemTerm

    def __init__(self, name : str, para_sorts : Tuple[T_Sort, ...], domain_sort : T_Sort):
        '''
        '''
        if not isinstance(name, str):
            raise REM_META_Error(f"The object '{name}' is not a valid name for this function. It should be a string.")
        
        self.name = name
        
        if not isinstance(para_sorts, tuple):
            raise REM_META_Error(f"({self.name}): The parameter sorts should be a tuple.")
        
        for sort in para_sorts:
            if not isinstance(sort, self.sort_type):
                raise REM_META_Error(f"({self.name}): The parameter sort '{sort}' is not an instance of class '{self.sort_type.__name__}'.")

        self.para_sorts : Tuple[T_Sort, ...] = para_sorts

        if not isinstance(domain_sort, RemSort):
            raise REM_META_Error(f"({self.name}): The domain sort '{domain_sort}' is not an instance of class RemSort.")
        
        self.domain_sort   : T_Sort = domain_sort


        syn.ParserHost.__init__(self, None)

        # the precedence of this term. applied in parsing and printing
        self.precedence : None | Tuple[str, int, str] = None

        # the documentation attributes
        self.doc : str | None = None
        self.rule_doc : str | None = None
        self.__para_doc : Tuple[str, ...] = tuple([f"para[{i}]" for i in range(self.arity)])

    @property
    def arity(self) -> int:
        return len(self.para_sorts)
    
    def set_para_doc(self, *para_doc : str) -> None:
        if len(para_doc) != self.arity:
            raise REM_META_Error(f"({self.name}): The parameter doc has {len(para_doc)} elements, which is inconsistent with the arity {self.arity}.")
        
    ############################################################
    # parser setting

    def set_precedence(self, symbol: str, prec: int, assoc: str):
        super().set_precedence(symbol, prec, assoc)
        self.precedence = (symbol, prec, assoc)
    

    ############################################################
    # common checkings

    def type_check(self, obj, T : Type | T_Sort, term : str) -> None:
        '''
        Checks whether object `obj` is a subterm of the type `T`.
        Raise a `REM_CONSTRUCTION_Error` when the type does not match.
        This is intended for the check for correct operations.
        '''
        if isinstance(T, RemSort):
            if T.well_typed(obj):
                return
            
            msg = f"\n({self.name}): The parameter '{term}' should be of sort\n\n'{T}'\n\nbut Rem found the term \n\n'{obj}'\n\nactually has sort \n\n'{obj.sort}'"
                        
        elif isinstance(T, Type):
            if isinstance(obj, T):
                return 
            
            msg = f"\n({self.name}): The parameter '{term}' should have Python type \n\n'{T}'\n\nbut Rem found the object \n\n'{obj}'\n\nactually has type \n\n'{type(obj)}'"
            
        else:
            raise REM_META_Error(f"({self.name}): Invalid parameter type/sort '{T}'.")
        
        if self.rule_doc is not None:
            msg += f"\n\n Rem reminds you of the rule.\n{self.rule_doc}"
        
        raise REM_CONSTRUCTION_Error(msg)
            

    def consistency_check(self, a, b, term : str) -> None:
        '''
        Checks whether `a == b` holds. They should both serve as the terms for `term` in the meta system.
        Raise a `REM_CONSTRUCTION_Error` when `a != b`.
        This is intended for the check of object consistency for correct operations.
        '''

        if a != b:
            msg = f"\n({self.name}): Rem found the instantiations for the parameter '{term}' are not consistent: \n\n'{a}'\n\nand\n\n'{b}'"
            if self.rule_doc is not None:
                msg += f"\n\nRem reminds you of the rule.\n{self.rule_doc}"
            raise REM_CONSTRUCTION_Error(msg)
        
    def other_check(self, expr : bool, reason : str) -> None:
        '''
        If the `expr` does not hold, it will raise a formated error with information `reason`.
        This is intended for the check for correct operations.
        '''
        if not expr:
            msg = f"\n({self.name}): Rem does not accept because: \n\n{reason}"

            if self.rule_doc is not None:
                msg += f"\n\nRem reminds you of the rule.\n{self.rule_doc}"
            raise REM_CONSTRUCTION_Error(msg)
    
    def __call__(self, *paras : T_Term, **kwparas) -> T_Term:
        '''
        Create a `RemTerm` instance with the parameters.
        '''
        if len(paras) != self.arity:
            raise REM_CONSTRUCTION_Error(f"({self.name}): Invalid argument number. The function arity is {self.arity} but {len(paras)} arguments are provided.")
        
        for i in range(self.arity):                
            self.type_check(paras[i], self.para_sorts[i], self.__para_doc[i])
            
        self.extra_check(self, *paras, **kwparas)

        term : T_Term = self.term_type(self, *paras)    # type: ignore

        self.modify(term, *paras, **kwparas)

        return term

    # common checkings
    ###########################################################
    
    def extra_check(self, fun : RemFun[T_Sort, T_Term], *paras : T_Term, **kwparas):
        '''
        Extra validity check when constructing this term.
        (redefine to enable)
        '''
        pass

    def modify(self, term : T_Term, *paras : T_Term, **kwparas):
        '''
        The modification on the term to be created.
        (redefine to enable)
        '''
        pass

    def __eq__(self, __value: object) -> bool:
        '''
        Two functions are considered identical only if they are the same Python object.
        '''
        return __value is self
    
    ##############################################
    # for pretty printing

    def enclosed(self, inner_str : str) -> str:
        '''
        Return the enclosed string of itself.
        Reload this method to redefine enclosing.
        '''
        return f"({inner_str})"
            
            
# we can consider variables here.

