'''
R. E. M.

Reliable Encode Mechanism
'''

from __future__ import annotations

from typing import Type, Tuple, Any, TypeVar

import inspect
import os


class REM_Error(Exception):
    pass


def REM_type_check(obj : object, target_type : Type | Tuple[Type, ...]) -> None:
    '''
    This method checks whether CIC systems works as expected.
    '''

    if isinstance(target_type, tuple):
        for t in target_type:
            if isinstance(obj, t):
                return
        
        raise REM_Error("The parameter expression '" + str(obj) + "' should be within type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

    elif not isinstance(obj, target_type):
        raise REM_Error("The parameter expression '" + str(obj) + "' should be of type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")


class __REM_SYS_INFO__:
    counter = 0
    registered : list[str] = []



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

    def __new__(cls, *args, **kwargs):
        raise REM_Error(f"Cannot instantiate abstract proof object {cls}.")

    def is_concrete(self) -> bool:
        return False
    
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
    
    # register
    cls.term_order = __REM_SYS_INFO__.counter
    __REM_SYS_INFO__.counter += 1
    __REM_SYS_INFO__.registered.append(cls.__name__)

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

# decorate the root term
RemTerm = Rem_term(RemTerm)

@Rem_term
class RemProof(RemTerm):
    '''
    Rem-proof
    ```
    _
    ```
    The proof objects in REM.
    '''

    def premises(self) -> str:
        raise NotImplementedError()
    
    def conclusion(self) -> str:
        raise NotImplementedError()
    
    def __str__(self) -> str:
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
    


####################################################################
# methods on Rem system


def Rem_term_describe(mt : RemTerm) -> str:
    '''
    Output a description for the Rem term.
    '''
    return f"({mt.Rem_term_name}):" + "\n" + mt.Rem_term_def



def get_Rem_system_def(GLOBAL : dict[str, Any]) -> str:
    '''
    Inspect the current package and extract all definitions of subclass of `RemTerm`, which finally form the system.

    `GLOBAL` : shoule pass in `global()` result
    '''

    # get the sorted terms
    Rem_terms = list(filter(
        lambda obj : inspect.isclass(obj) and issubclass(obj, RemTerm),GLOBAL.values()
    ))
    Rem_terms.sort(key=lambda x: x.term_order)

    res = ""
    for item in Rem_terms:
        res += Rem_term_describe(item) + "\n\n"

    return res

def Rem_system_check(GLOBAL : dict[str, Any], file : str = "") -> None:
    '''
    Checks whether the current Rem system is well formed and generate the form.

    `GLOBAL` : shoule pass in `global()` result
    `file` : should pass in `__file__` result
    '''

    # check whether Rem terms are properly registered by decorators `Rem_term` or `concrete_Rem_term`
    for obj in GLOBAL.values():
        if inspect.isclass(obj):
            if issubclass(obj, RemTerm) and obj.__name__ not in __REM_SYS_INFO__.registered:
                raise Exception(f"Class {obj} is subclass of RemTerm but not registered.")

    # produce the rule doc
    with open(os.path.join(os.path.dirname(file),"REM_rule.txt"), "w", encoding="utf-8") as p:
        p.write(get_Rem_system_def(GLOBAL=GLOBAL))