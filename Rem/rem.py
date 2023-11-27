'''
R.E.M. Reliable Encode Mechanism
レム、ゼロから新世代の形式化ツール！

[formalization framework based on order-sorted universal algebra]
'''

from __future__ import annotations

from typing import Type, Tuple, Any, TypeVar, Sequence, List, Generic, Callable, Dict

from graphviz import Digraph

from types import FunctionType

import inspect
import os
import copy

from . import syn

from .rem_error import REM_META_Error, REM_CONSTRUCTION_Error, REM_type_check, REM_other_check, REM_warning

from .network import NetworkNode

class RemNamed:
    '''
    Named terms in Rem system.
    '''
    def __init__(self, name : str):

        if not isinstance(name, str):
            raise REM_META_Error(f"The object '{name}' is not a valid name for this function. It should be a string.")

        self.__name = name
        self.rule_doc : str | None = None

    @property
    def name(self) -> str:
        return self.__name
    
    def __str__(self) -> str:
        return self.__name

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


# the type variable suggesting different types of sort-term-functions
T_Sort = TypeVar("T_Sort", bound = "RemSort")
T_Term = TypeVar("T_Term", bound = "RemTerm")


class RemSort(NetworkNode, RemNamed):
    '''
    The sorts in Rem system.
    One important feature is that every sort itself can also be an algebra.
    '''
    def __init__(self, name : str, attr_pres : Dict[str, RemSort | Type] = {}, super_sorts : Tuple[RemSort, ...] = ()):
        
        RemNamed.__init__(self, name)
        NetworkNode.__init__(self, set())

        for sort in super_sorts:
            self.set_super_node(sort)

        if not isinstance(super_sorts, tuple):
            raise REM_META_Error(f"({self.name}): The super sorts should be a tuple.")
        
        for sort in super_sorts:
            if not isinstance(sort, RemSort):
                raise REM_META_Error(f"({self.name}): The super sort '{sort}' is not an instance of class RemSort.")
            

        # the prescription of term attributes
        if not isinstance(attr_pres, dict):
            raise REM_META_Error(f"({self.name}): The attribute prescription should be a dictionary.")
        
        self.__attr_pres = attr_pres.copy()

        # the documentation attribute
        self.doc : str | None = None

        # The extra check on term attributes. Reassign to redefine.
        self.attr_extra_check : Callable[[RemTerm], None] | None = None


    #######################################################
    # sort check - checking for valid terms of this sort

    def attr_pres_check(self, term : RemTerm):
        '''
        Checks that the term implements the attribute prescription of this sort.
        '''
        self.well_typed(term)

        for attr in self.__attr_pres:
            if attr not in term.__dict__:
                raise REM_META_Error(f"The term '{term}' does not implement the attribute prescription of '{self}':\n\nThe attribute '{attr}' is not defined.")
            
            self.type_check(term.__dict__[attr], self.__attr_pres[attr], attr)

    ########################################################
    # pretty printing
    def term_str(self, term : RemTerm[T_Sort, T_Term]) -> str:
        '''
        Return the default format string of the `term`.
        Reassign to modify.
        '''
        # default printing

        res = f"{term.fun.name}"
        if term.fun.arity == 0:
            res += f"()"
        else:
            res += f"({term[0]}"
            for i in range(1, term.fun.arity):
                res += f", {term[i]}"
            res += ")"
        return res
            
                

    #############################################
    # checkings


    def well_typed(self, term : RemTerm) -> bool:
        '''
        Return whether the `RemTerm` term is of type `self`.
        The judgement depends on the calculated reflexive, transitive closure of super sorts.
        '''
        if not isinstance(term, RemTerm):
            raise REM_CONSTRUCTION_Error(f"The term '{term}' is not an instance of RemTerm class.")
        
        return self in term.sort.upstream_nodes
    

    def __eq__(self, __value: object) -> bool:
        '''
        Two sorts are considered identical only if they are the same Python object.
        '''
        return __value is self
    
    def __hash__(self) -> int:
        return id(self)
    
    def __enter__(self) -> RemSort:
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        pass
            
    


class RemTerm(Generic[T_Sort, T_Term]):
    '''
    A term in the signature.
    '''
    def __init__(self, fun : RemFun[T_Sort, T_Term], *paras : T_Term):
        self.__fun = fun
        self.__paras = paras


    ############################################################
    # These two magic methods erase the type error for getting and setting attributes.
    def __setattr__(self, __name: str, __value: Any) -> None:
        return super().__setattr__(__name, __value)
    def __getattribute__(self, __name: str) -> Any:
        return super().__getattribute__(__name)
    ############################################################

    @property
    def fun(self) -> RemFun[T_Sort, T_Term]:
        return self.__fun
    
    @property
    def paras(self) -> Tuple[T_Term, ...]:
        return self.__paras
    
    def __getitem__(self, i) -> T_Term:
        '''
        This syntax sugar imitate the positioning in universal algebra
        '''
        return self.__paras[i]

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

    def __str__(self) -> str:
        '''
        The formatted string of a term is determined by the function.
        '''
        if self.fun.term_str is not None:
            return self.fun.term_str(self)
        else:
            return self.sort.term_str(self)
    
    def ctx_term_str(self, super_fun : RemFun[T_Sort, T_Term], left : bool = True) -> str:
        return self.fun.ctx_term_str(self, super_fun, left)

        



class RemFun(Generic[T_Sort, T_Term], RemNamed):
    '''
    The functions in Rem system.
    '''

    # this static attribute controls the type of constructed term
    term_type : Type[RemTerm] = RemTerm

    def __init__(self, name : str, para_sorts : Tuple[RemSort, ...], domain_sort : T_Sort):
        '''
        '''
        RemNamed.__init__(self, name)
        
        if not isinstance(para_sorts, tuple):
            raise REM_META_Error(f"({self.name}): The parameter sorts should be a tuple.")
        
        for sort in para_sorts:
            if not isinstance(sort, RemSort):
                raise REM_META_Error(f"({self.name}): The parameter sort '{sort}' is not an instance of class '{RemSort.__name__}'.")

        self.para_sorts : Tuple[RemSort, ...] = para_sorts

        if not isinstance(domain_sort, RemSort):
            raise REM_META_Error(f"({self.name}): The domain sort '{domain_sort}' is not an instance of class RemSort.")
        
        self.domain_sort   : T_Sort = domain_sort

        # the precedence of this term. applied in parsing and printing
        self.precedence : None | Tuple[str, int, str] = None

        # the documentation attributes
        self.doc : str | None = None
        self.rule_doc : str | None = None
        self.__para_doc : Tuple[str, ...] = tuple([f"para[{i}]" for i in range(self.arity)])


        # the function specific term printing. high priority. reassign to modify
        self.term_str : Callable[[RemTerm[T_Sort, T_Term]], str] | None = None


    @property
    def arity(self) -> int:
        return len(self.para_sorts)
    
    def set_para_doc(self, *para_doc : str) -> None:
        if len(para_doc) != self.arity:
            raise REM_META_Error(f"({self.name}): The parameter doc has {len(para_doc)} elements, which is inconsistent with the arity {self.arity}.")
        
    ############################################################
    # parser setting

    def set_precedence(self, symbol: str, prec: int, assoc: str):
        self.precedence = (symbol, prec, assoc)
    

    ############################################################
    # common checkings

    
    def __call__(self, *paras : T_Term, **kwparas) -> T_Term:
        '''
        Create a `RemTerm` instance with the parameters.
        '''
        if len(paras) != self.arity:
            raise REM_CONSTRUCTION_Error(f"({self.name}): Invalid argument number. The function arity is {self.arity} but {len(paras)} arguments are provided.")
        
        # check for parameters
        for i in range(self.arity):                
            self.type_check(paras[i], self.para_sorts[i], self.__para_doc[i])
        
        # extra check for parameters    
        self.extra_check(self, *paras, **kwparas)

        # construct the term
        term : T_Term = self.term_type(self, *paras)    # type: ignore

        #  modification
        self.modify(term, *paras, **kwparas)

        # check the implementation of attribute prescriptions
        self.domain_sort.attr_pres_check(term)

        # sort's extra check
        if self.domain_sort.attr_extra_check is not None:
            self.domain_sort.attr_extra_check(term)

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
    
    def __hash__(self) -> int:
        return id(self)

    ##############################################
    # for pretty printing

    def enclosed(self, inner_str : str) -> str:
        '''
        Return the enclosed string of itself.
        Reload this method to redefine enclosing.
        '''
        return f"({inner_str})"


    def ctx_term_str(self, term : RemTerm[T_Sort, T_Term], super_fun : RemFun[T_Sort, T_Term], left : bool = True) -> str:
        '''
        Use `ctx_str` instead of `__str__` to compose the printing when this term may need enclosing.

        According to the context of `super_fun`, decide whether enclose the string of itself, and return the result.
        - `left`: for binary operators only. whether this term is the left one or the right one.
        '''

        if super_fun.precedence is None or term.fun.precedence is None:
            return str(term)
        elif super_fun.precedence[1] > term.fun.precedence[1]:
            return term.fun.enclosed(str(term))
        elif super_fun.precedence[1] < term.fun.precedence[1]:
            return str(term)
        else:
            # equal precedence
            if (term.fun.precedence[2] == 'left' and left == False)\
            or (term.fun.precedence[2] == 'right' and left == True):
                return term.fun.enclosed(str(term))
            else:
                return str(term)


    ###################################################
    # drawing by Graphviz

    def vlayout(self, dot : Digraph, id : str, title : str):
        dot.node(id, title,
            shape = "box", style="filled", fillcolor = "lightyellow",
            fontname = "Consolas",
            labeljust="l")
        
    def vlayout_focus(self, dot : Digraph, id : str, title : str):
        dot.node(id, title,
            shape = "box", 
            style="filled, bold", color = "red", fillcolor = "lightyellow",
            fontname = "Consolas",
            labeljust="l")        
    
    ###################################################
    # context manager

    def __enter__(self) -> RemFun[T_Sort, T_Term]:
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        pass
            
            
# we can consider variables here.