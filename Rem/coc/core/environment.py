'''

See (https://coq.inria.fr/refman/language/cic.html#global-environment).

'''

from __future__ import annotations

from .term import *
from ...rem import RemProof


##############################################################
# Global Environment
###

@Rem_term(rem_coc)
class GlobalDec(RemTerm):
    '''
    global-dec
    ```
    _
    ```
    '''
    def __eq__(self, other : GlobalDec) -> bool:
        '''
        This is the syntactical equivalence.
        '''
        raise NotImplementedError()
    
    def __init__(self, c : Const, T : Term):
        '''
        Parameters -> Rule Terms:
        - `c` -> `c`
        - `T` -> `T`
        '''
        self.Rem_type_check(c, Const, 'c')
        self.__c = c
        self.Rem_type_check(T, Term, 'T')
        self.__T = T

    @property
    def c(self) -> Const:
        return self.__c
    
    @property
    def T(self) -> Term:
        return self.__T

@concrete_Rem_term(rem_coc)
class GlobalTyping(GlobalDec):
    '''
    global-assum
    ```
    (c : T)
    ```
    '''

    def __eq__(self, other: GlobalDec) -> bool:
        if not isinstance(other, GlobalTyping):
            return False
        return self.c == other.c and self.T == other.T
    
    def __str__(self) -> str:
        return f"({self.c} : {self.T})"

@concrete_Rem_term(rem_coc)
class GlobalDef(GlobalDec):
    '''
    global-def
    ```
    (c := t : T)
    ```
    '''

    def __init__(self, c : Const, t : Term, T : Term):
        '''
        Parameters -> Rule Terms:
        - `c` -> `c`
        - `t` -> `t`
        - `T` -> `T`
        '''
        super().__init__(c, T)
        self.Rem_type_check(t, Term, 't')
        self.__t = t

    @property
    def t(self) -> Term:
        return self.__t
    
    def __eq__(self, other: GlobalDec) -> bool:
        if not isinstance(other, GlobalDef):
            return False
        return self.c == other.c and self.t == other.t and self.T == other.T
    
    def __str__(self) -> str:
        return f"({self.c} := {self.t} : {self.T})"
    

@concrete_Rem_term(rem_coc)
class Environment(RemTerm):
    '''
    global-environment
    ```
    _
    ```
    '''

    def __init__(self, ls : Tuple[GlobalDec, ...] = ()):
        self.Rem_type_check(ls, tuple, 'ls')
        self.__ls = ls

    @property
    def ls(self) -> Tuple[GlobalDec, ...]:
        return self.__ls
    
    def __eq__(self, other : Environment):
        # this will reduce the complexity of comparing
        if self is other:
            return True
        else:
            # # for complexity reason, here we narrow the definition of `E1 == E2`
            # return False
            if not isinstance(other, Environment):
                return False
            return self.ls == other.ls


    def __str__(self) -> str:
        if len(self.__ls) == 0:
            return "[]"
        else:
            res = "[" + str(self.__ls[0])
            for i in range(1, len(self.__ls)):
                res += "; " + str(self.__ls[i])
            res += "]"
            return res
        
    def push(self, dec : GlobalDec) -> Environment:
        '''
        Corresponds to `E; (...)`
        '''
        return Environment(self.__ls + (dec,))
    
    def get_typing(self, const : Const) -> Term | None:
        '''
        Return `T` for `const : T` or `const := t : T` in `self`.
        Return `None` when `const` is not contained in `self.
        '''
        for c_dec in self.ls:
            if c_dec.c == const:
                return c_dec.T
            
        return None


@concrete_Rem_term(rem_coc)
class Rem_Env_Not_Contain_Const(RemProof):
    '''
    not-in-global
    ```
    c ∉ E
    ```
    The proof object for `c ∉ E`.
    '''

    def __init__(self, c : Const, E : Environment):
        '''
        Parameters -> Rule Terms:
        - `c` -> `c`
        - `E` -> `E`
        '''
        self.Rem_type_check(c, Const, 'c')
        self.Rem_type_check(E, Environment, 'E')

        for c_dec in E.ls:
            self.Rem_other_check(c_dec.c != c, f"The constant '{c}' is contained in the environment.")
        
        self.__c = c
        self.__E = E

    @property
    def c(self) -> Const:
        return self.__c
    
    @property
    def E(self) -> Environment:
        return self.__E
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.c} ∉ {self.E}"


@concrete_Rem_term(rem_coc)
class Rem_Env_Contain_Const(RemProof):
    '''
    const-in-global
    ```
    c ∈ E
    ```
    The proof object for `c ∈ E`.
    '''

    def __init__(self, c : Const, E : Environment):
        '''
        Parameters -> Rule Terms:
        - `c` -> `c`
        - `E` -> `E`
        '''
        self.Rem_type_check(c, Const, 'c')
        self.Rem_type_check(E, Environment, 'E')

        contains = False
        for c_dec in E.ls:
            if c_dec.c == c:
                contains = True
                break

        self.Rem_other_check(contains, f"The constant '{c}' is not contained in the environment.")
        
        self.__c = c
        self.__E = E

    @property
    def c(self) -> Const:
        return self.__c
    
    @property
    def E(self) -> Environment:
        return self.__E
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.c} ∈ {self.E}"


@concrete_Rem_term(rem_coc)
class Rem_Env_Contain_Typing(RemProof):
    '''
    assum-in-global
    ```
    (c : T) ∈ E
    ```
    The proof object for `(c : T) ∈ E`.
    '''

    def __init__(self, c_typing : GlobalTyping, E : Environment):
        '''
        Parameters -> Rule Terms:
        - `c_typing` -> `c : T`
        - `E` -> `E`
        '''

        self.Rem_type_check(c_typing, GlobalTyping, 'c : T')
        self.Rem_type_check(E, Environment, 'E')

        contains = False
        for c_dec in E.ls:
            if isinstance(c_dec, GlobalTyping):
                if c_dec == c_typing:
                    contains = True
                    break
            elif isinstance(c_dec, GlobalDef):
                if c_dec.c == c_typing.c and c_dec.T == c_typing.T:
                    contains = True
                    break
            else:
                raise Exception()
                
        self.Rem_other_check(contains, f"The declaration '{c_typing}' is not contained in the environment.")
        
        self.__c_typing = c_typing
        self.__E = E

    @property
    def c_typing(self) -> GlobalTyping:
        return self.__c_typing
    
    @property
    def E(self) -> Environment:
        return self.__E

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.c_typing} ∈ {self.E}"
    

@concrete_Rem_term(rem_coc)
class Rem_Env_Contain_Def(RemProof):
    '''
    def-in-global
    ```
    (c := t : T) ∈ E
    ```
    The proof object for `(c := t : T) ∈ E`.
    '''
    
    def __init__(self, c_def : GlobalDef, E : Environment):
        '''
        Parameters -> Rule Terms:
        - `c_def` -> `c := t : T`
        - `E` -> `E`
        '''

        self.Rem_type_check(c_def, GlobalDef, 'c := t : T')
        self.Rem_type_check(E, Environment, 'E')

        self.Rem_other_check(c_def in E.ls, f"The definition '{c_def}' is not contained in the environment.")
        
        self.__c_def = c_def
        self.__E = E

    @property
    def c_def(self) -> GlobalDef:
        return self.__c_def
    
    @property
    def E(self) -> Environment:
        return self.__E

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.c_def} ∈ {self.E}"
