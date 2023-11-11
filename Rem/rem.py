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

from .rem_error import REM_Error, REM_type_check, REM_other_check, REM_warning


class RemSort:
    '''
    The sorts in Rem system.
    One important feature is that every sort itself can also be a signature.
    '''
    def __init__(self, name : str, super_sorts : Tuple[RemSort, ...]):
        self.__name = name
        self.__super_sorts  : Tuple[RemSort, ...] = ()
        self.__sub_sorts    : Tuple[RemSort, ...] = ()

        self.set_super_sorts(super_sorts)
        
    @property
    def name(self) -> str:
        return self.__name

    @property
    def super_sorts(self) -> Tuple[RemSort, ...]:
        return self.__super_sorts
    
    @property
    def rt_sub_sorts(self) -> Tuple[RemSort, ...]:
        '''
        Note that this property is dynamically calculated.
        '''
        return self.__calc_rt_sub_sorts()
    
    @property
    def rt_super_sorts(self) -> Tuple[RemSort, ...]:
        return self.__rt_super_sorts
    
    def __calc_rt_super_sorts(self) -> Tuple[RemSort, ...]:
        '''
        Calculate and return all the reflexive, transitive closure of super sorts.
        '''

        traveled : List[RemSort] = []
        rt_super_sorts : List[RemSort] = [self]

        while len(traveled) < len(rt_super_sorts):
            for sort in rt_super_sorts:
                if sort not in traveled:
                    traveled.append(sort)
                    for new_sort in sort.__super_sorts:
                        if new_sort not in rt_super_sorts:
                            rt_super_sorts.append(new_sort)
                    break

        return tuple(rt_super_sorts)
    

    def __calc_rt_sub_sorts(self) -> Tuple[RemSort, ...]:
        '''
        Calculate and return all the reflexive, transitive closure of sub sorts.
        '''

        traveled : List[RemSort] = []
        rt_sub_sorts : List[RemSort] = [self]

        while len(traveled) < len(rt_sub_sorts):
            for sort in rt_sub_sorts:
                if sort not in traveled:
                    traveled.append(sort)
                    for new_sort in sort.__sub_sorts:
                        if new_sort not in rt_sub_sorts:
                            rt_sub_sorts.append(new_sort)
                    break

        return tuple(rt_sub_sorts)
    

    def set_super_sorts(self, super_sorts : Tuple[RemSort, ...]):
        '''
        Reset the super sort, and calculate the reflexive, transitive closure of super sorts.
        '''

        # check uniqueness
        unique_sorts = []
        for sort in super_sorts:
            if sort not in unique_sorts:
                REM_type_check(sort, RemSort)
                unique_sorts.append(sort)
            else:
                REM_warning(f"The super sort setting '{tuple([sort.name for sort in super_sorts])}' for sort '{self.name}' is illegal. The super sort '{sort.name}' appears more than once.")

        # cancel the original sub_sort items
        for sort in self.__super_sorts:
            temp = list(sort.__sub_sorts)
            temp.remove(self)
            sort.__sub_sorts = tuple(temp)

        self.__super_sorts = tuple(unique_sorts)

        # create the new sub_sort items
        for sort in self.__super_sorts:
            sort.__sub_sorts = sort.__sub_sorts + (self,)

        # recalculate the reflexive, transitive closure of super sorts
        for sort in self.rt_sub_sorts:
            self.__rt_super_sorts = self.__calc_rt_super_sorts()


    def well_typed(self, term : RemTerm) -> bool:
        '''
        Return whether the `RemTerm` term is of type `self`.
        The judgement depends on the calculated reflexive, transitive closure of super sorts.
        '''
        return term.sort in self.__rt_super_sorts
    
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
    def __init__(self, name : str, para_sorts : List[RemSort], res_sort : RemSort):
        self.name = name
        self.para_sorts = para_sorts
        self.res_sort = res_sort


    @property
    def arity(self) -> int:
        return len(self.para_sorts)
    
    def __call__(self, *paras : RemTerm, **kwparas) -> RemTerm:
        '''
        Create a `RemTerm` instance with the parameters.
        '''
        if len(paras) != self.arity:
            raise REM_Error("Invalid parameter number.")
        
        for i in range(self.arity):
            if not self.para_sorts[i].well_typed(paras[i]):
                raise REM_Error("invalid parameter")
            
        self.extra_check(*paras, **kwparas)

        term = RemTerm(self, *paras, **kwparas)

        self.modify(term, *paras)

        return term


    
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
        return self.__fun.res_sort
    
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