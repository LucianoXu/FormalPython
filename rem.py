'''
R.E.M. Reliable Encode Mechanism
レム、ゼロから新世代の形式化ツール！

[formalization framework based on order-sorted universal algebra]
'''

from __future__ import annotations

from typing import Type, Tuple, Any, TypeVar, Sequence, List, Callable
from types import FunctionType

import inspect
import os
import copy

from . import syn

from .rem_error import REM_META_Error, REM_CONSTRUCTION_Error, REM_type_check, REM_other_check, REM_warning

from .network import NetworkNode

class RemSort(NetworkNode):
    '''
    The sorts in Rem system.
    One important feature is that every sort itself can also be a signature.
    '''
    def __init__(self, name : str, symbol : str | None = None, super_sorts : Tuple[RemSort, ...] = ()):

        if not isinstance(name, str):
            raise REM_META_Error(f"The object '{name}' is not a valid name for this sort. It should be a string.")
        
        if not isinstance(super_sorts, tuple):
            raise REM_META_Error(f"({self.name}): The super sorts should be a tuple.")
        
        for sort in super_sorts:
            if not isinstance(sort, RemSort):
                raise REM_META_Error(f"({self.name}): The super sort '{sort}' is not an instance of class RemSort.")
            
        super().__init__(super_sorts)

        self.__name : str = name

        self.__parser_node = syn.ParserNode(symbol, self)

        # the documentation attribute
        self.doc : str | None = None




    @property
    def name(self) -> str:
        return self.__name
    
    @property
    def parser_node(self) -> syn.ParserNode:
        return self.__parser_node
    
    @property
    def parser(self) -> syn.PLYParser:
        '''
        The integrated parser.
        This `PLYParser` property is callable (as a parser).
        '''
        return self.parser_node.plyparser
    
    #############################################
    # Manipulation of sort network

    def append_super_sort(self, super_sort : RemSort):
        self.set_super_node(super_sort)
        self.parser_node.set_super_node(super_sort.parser_node)

    
    def __setattr__(self, __name: str, __value: Any) -> None:

        if isinstance(__value, RemSort) or isinstance(__value, RemFun):
            # the attributes of `RemSort` class will be linked to the parser automatically
            self.parser_node.set_sub_node(__value.parser_node)

        return super().__setattr__(__name, __value)

    def __delattr__(self, __name: str) -> None:
        attr = self.__dict__[__name]
        if isinstance(attr, RemSort) or isinstance(attr, RemFun):
            self.parser_node.del_sub_node(attr.parser_node)

        return super().__delattr__(__name)

    #############################################
    # checkings


    def well_typed(self, term : RemTerm) -> bool:
        '''
        Return whether the `RemTerm` term is of type `self`.
        The judgement depends on the calculated reflexive, transitive closure of super sorts.
        '''
        if not isinstance(term, RemTerm):
            raise REM_META_Error(f"The term '{term}' is not an instance of RemTerm class.")
        
        return term.sort in self.super_nodes
    
    def __str__(self) -> str:
        return self.name

    def __eq__(self, __value: object) -> bool:
        '''
        Two sorts are considered identical only if they are the same Python object.
        '''
        return __value is self
    


class RemFun:
    '''
    The functions in Rem system.
    '''
    def __init__(self, name : str, para_sorts : Tuple[RemSort], domain_sort : RemSort, symbol : str | None = None):
        '''
        - `symbol` : the symbol for parser system
        '''
        if not isinstance(name, str):
            raise REM_META_Error(f"The object '{name}' is not a valid name for this function. It should be a string.")
        
        self.name = name
        
        if not isinstance(para_sorts, tuple):
            raise REM_META_Error(f"({self.name}): The parameter sorts should be a tuple.")
        
        for sort in para_sorts:
            if not isinstance(sort, RemSort):
                raise REM_META_Error(f"({self.name}): The parameter sort '{sort}' is not an instance of class RemSort.")

        self.para_sorts : Tuple[RemSort, ...] = para_sorts

        if not isinstance(domain_sort, RemSort):
            raise REM_META_Error(f"({self.name}): The domain sort '{domain_sort}' is not an instance of class RemSort.")
        
        self.domain_sort   : RemSort = domain_sort

        self.parser_node = syn.ParserNode(symbol, self)

        # the precedence of this term. applied in parsing and printing
        self.precedence : None | Tuple[str, int, str] = None

        # the documentation attributes
        self.doc : str | None = None
        self.rule_doc : str | None = None
        self.__para_doc : Tuple[str, ...] = tuple([f"para[{i}]" for i in range(self.arity)])

    @property
    def arity(self) -> int:
        return len(self.para_sorts)
    
    def set_para_doc(self, para_doc : Tuple[str, ...]) -> None:
        if len(para_doc) != self.arity:
            raise REM_META_Error(f"({self.name}): The parameter doc has {len(para_doc)} elements, which is inconsistent with the arity {self.arity}.")
    

    ############################################################
    # common checkings

    def type_check(self, obj, T : Type | RemSort, term : str) -> None:
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
    
    def __call__(self, *paras : RemTerm, **kwparas) -> RemTerm:
        '''
        Create a `RemTerm` instance with the parameters.
        '''
        if len(paras) != self.arity:
            raise REM_CONSTRUCTION_Error(f"({self.name}): Invalid argument number. The function arity is {self.arity} but {len(paras)} arguments are provided.")
        
        for i in range(self.arity):                
            self.type_check(paras[i], self.para_sorts[i], self.__para_doc[i])
            
        self.extra_check(*paras, **kwparas)

        term = RemTerm(self, *paras, **kwparas)

        self.modify(term, *paras, **kwparas)

        return term

    # common checkings
    ###########################################################
    
    def extra_check(self, *paras : RemTerm, **kwparas):
        '''
        Extra validity check when constructing this term.
        (redefine to enable)
        '''
        pass

    def modify(self, term : RemTerm, *paras : RemTerm, **kwparas):
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


class RemTerm:
    '''
    A term in the signature.
    '''
    def __init__(self, fun : RemFun, *paras : RemTerm):
        self.__fun = fun
        self.__paras = paras

    @property
    def fun(self) -> RemFun:
        return self.__fun
    
    @property
    def paras(self) -> Tuple[RemTerm, ...]:
        return self.__paras

    @property
    def sort(self) -> RemSort:
        return self.__fun.domain_sort
    
    def __eq__(self, __value: object) -> bool:
        if __value is self:
            return True
        elif isinstance(__value, RemTerm):
            return __value.__fun == self.__fun and __value.__paras == self.__paras
        else:
            return False

    # reassign this attribute to define the custom printing
    format_str : None | Callable[[],str] = None

    def __str__(self) -> str:
        # default printing
        if self.format_str is None:
            res = self.fun.name
            if self.fun.arity > 0:
                res += f"({self.paras[0]}"
                for i in range(1, len(self.paras)):
                    res += f", {self.paras[i]}"
                res += ")"
            return res
        
        # custom printing
        else:
            return self.format_str()
        


    ###########################################################
    # printing

    def ctx_str(self, super_fun : RemFun, left : bool = True) -> str:
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

