'''

See (https://coq.inria.fr/refman/language/cic.html#global-environment).

'''

from __future__ import annotations

from .term import *
from ...rem import RemProof

@Rem_term(rem_coc)
class LocalDec(RemTerm):
    '''
    local-dec
    ```
    _
    ```
    '''

    def __eq__(self, other : LocalDec) -> bool:
        '''
        This is the syntactical equivalence.
        '''
        raise NotImplementedError()
    
    def __init__(self, x : Var, T : Term):
        '''
        Parameters -> Rule Terms:
        - `x` -> `x`
        - `T` -> `T`
        '''
        self.Rem_type_check(x, Var, 'x')
        self.__x = x
        self.Rem_type_check(T, Term, 'T')
        self.__T = T

    @property
    def x(self) -> Var:
        return self.__x
    
    @property
    def T(self) -> Term:
        return self.__T

@concrete_Rem_term(rem_coc)
class LocalTyping(LocalDec):
    '''
    local-assum
    ```
    x : T
    ```
    '''

    def __eq__(self, other: LocalDec) -> bool:
        if not isinstance(other, LocalTyping):
            return False
        return self.x == other.x and self.T == other.T
    
    def __str__(self) -> str:
        return f"({self.x} : {self.T})"

@concrete_Rem_term(rem_coc)
class LocalDef(LocalDec):
    '''
    local-def
    ```
    x := t : T
    ```
    '''

    def __init__(self, x : Var, t : Term, T : Term):
        '''
        Parameters -> Rule Terms:
        - `x` -> `x`
        - `t` -> `t`
        - `T` -> `T`
        '''
        super().__init__(x, T)
        self.Rem_type_check(t, Term, 't')
        self.__t = t

    @property
    def t(self) -> Term:
        return self.__t
    
    def __eq__(self, other: LocalDec) -> bool:
        if not isinstance(other, LocalDef):
            return False
        return self.x == other.x and self.t == other.t and self.T == other.T
    
    def __str__(self) -> str:
        return f"({self.x} := {self.t} : {self.T})"
    

##############################################################
# Local Context
###

@concrete_Rem_term(rem_coc)
class Context(RemTerm):
    '''
    context
    ```
    _
    ```
    '''

    def __init__(self, ls : Tuple[LocalDec, ...] = ()):
        self.Rem_type_check(ls, tuple, 'ls')
        self.__ls = ls

    @property
    def ls(self) -> Tuple[LocalDec, ...]:
        return self.__ls
    
    def __eq__(self, other : Context):
        # this will reduce the complexity of comparing
        if self is other:
            return True
        else:
            # # for complexity reason, here we narrow the definition of `Γ1 == Γ2`
            # return False
            if not isinstance(other, Context):
                return False
            return self.ls == other.ls
        
    @property
    def is_empty(self) -> bool:
        return len(self.__ls) == 0

    def __str__(self) -> str:
        if len(self.__ls) == 0:
            return "[]"
        else:
            res = "[" + str(self.__ls[0])
            for i in range(1, len(self.__ls)):
                res += "; " + str(self.__ls[i])
            res += "]"
            return res
        
    def push(self, dec : LocalDec) -> Context:
        '''
        Corresponds to `Γ::(...)`
        '''
        return Context(self.__ls + (dec,))
    
    def pop(self) -> Tuple[Context, LocalDec]:
        self.Rem_other_check(not self.is_empty, "Cannot pop empty context.")
        return Context(self.__ls[:-1]), self.__ls[-1]
    

    def concatenate(self, other : Context) -> Context:
        '''
        Corresponds to the concatenation `Γ1; Γ2`
        '''
        return Context(self.__ls + other.__ls)
        
    def __getitem__(self, var : Var) -> LocalDec | None:
        '''
        Return `var : T` or `var := t : T` in `self`.
        Return `None` when `var` is not contained in `self.
        '''
        for var_dec in self.ls:
            if var_dec.x == var:
                return var_dec
            
        return None



@concrete_Rem_term(rem_coc)
class Rem_Cont_Not_Contain_Var(RemProof):
    '''
    not-in-local
    ```
    x ∉ Γ
    ```
    The proof object for `x ∉ Γ`.
    '''

    def __init__(self, x : Var, Gamma : Context):
        '''
        Parameters -> Rule Terms:
        - `x` -> `x`
        - `Gamma` -> `Γ`
        '''
        self.Rem_type_check(x, Var, 'x')
        self.Rem_type_check(Gamma, Context, 'Γ')

        for x_dec in Gamma.ls:
            self.Rem_other_check(x_dec.x != x, f"The variable '{x}' is contained in the context.")
        
        self.__x = x
        self.__Gamma = Gamma

    @property
    def x(self) -> Var:
        return self.__x
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.x} ∉ {self.Gamma}"


@concrete_Rem_term(rem_coc)
class Rem_Cont_Contain_Var(RemProof):
    '''
    var-in-local
    ```
    x ∈ Γ
    ```
    The proof object for `x ∈ Γ`.
    '''

    def __init__(self, x : Var, Gamma : Context):
        '''
        Parameters -> Rule Terms:
        - `x` -> `x`
        - `Gamma` -> `Γ`
        '''

        self.Rem_type_check(x, Var, 'x')
        self.Rem_type_check(Gamma, Context, 'Γ')

        contains = False
        for x_dec in Gamma.ls:
            if x_dec.x == x:
                contains = True
                break

        self.Rem_other_check(contains, f"The variable '{x}' is not contained in the context.")
        
        self.__x = x
        self.__Gamma = Gamma

    @property
    def x(self) -> Var:
        return self.__x
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.x} ∈ {self.Gamma}"


@concrete_Rem_term(rem_coc)
class Rem_Cont_Contain_Typing(RemProof):
    '''
    assum-in-local
    ```
    (x : T) ∈ Γ
    ```
    The proof object for `(x : T) ∈ Γ`.
    '''

    def __init__(self, x_typing : LocalTyping, Gamma : Context):
        '''
        Parameters -> Rule Terms:
        - `x_typing` -> `x : T`
        - `Gamma` -> `Γ`
        '''

        self.Rem_type_check(x_typing, LocalTyping, 'x : T')
        self.Rem_type_check(Gamma, Context, 'Γ')

        contains = False
        for x_dec in Gamma.ls:
            if isinstance(x_dec, LocalTyping):
                if x_dec == x_typing:
                    contains = True
                    break
            elif isinstance(x_dec, LocalDef):
                if x_dec.x == x_typing.x and x_dec.T == x_typing.T:
                    contains = True
                    break
            else:
                raise Exception()
                
        self.Rem_other_check(contains, f"The typing '{x_typing}' is not contained in the context.")
        
        self.__x_typing = x_typing
        self.__Gamma = Gamma

    @property
    def x_typing(self) -> LocalTyping:
        return self.__x_typing
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.x_typing} ∈ {self.Gamma}"

@concrete_Rem_term(rem_coc)
class Rem_Cont_Contain_Def(RemProof):
    '''
    def-in-local
    ```
    (x := t : T) ∈ Γ
    ```
    The proof object for `(x := t : T) ∈ Γ`.
    '''
    
    def __init__(self, x_def : LocalDef, Gamma : Context):
        '''
        Parameters -> Rule Terms:
        - `x_def` -> `x := t : T`
        - `Gamma` -> `Γ`
        '''
        self.Rem_type_check(x_def, LocalDef, 'x := t : T')
        self.Rem_type_check(Gamma, Context, 'Γ')


        self.Rem_other_check(x_def in Gamma.ls, f"The definition '{x_def}' is not contained in the context.")
        
        self.__x_def = x_def
        self.__Gamma = Gamma

    @property
    def x_def(self) -> LocalDef:
        return self.__x_def
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.x_def} ∈ {self.Gamma}"
