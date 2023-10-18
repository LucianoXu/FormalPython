
from __future__ import annotations

from typing import Dict, Type, List, Tuple

from .rem_sys_head import *
from ...rem import syn


#############################################################
# The definition for terms

@Rem_term(rem_coc)
class Term(RemTerm):
    '''
    term
    ```
    _
    ```
    '''


    def __eq__(self, other : Term) -> bool:
        '''
        This is the purely syntactical equivalence.
        '''
        raise NotImplementedError()

    def alpha_convertible(self, other : Term) -> bool:
        '''
        equivalence up to α-conversion

        Note: this method will inductively check whether two terms is α-convertible by an algorithm of unifying the bound variables.

        Reload this method for alpha-convertibility of extensions.
        '''
        raise NotImplementedError()

    def __str__(self) -> str:
        '''
        The printing of this term.
        '''
        raise NotImplementedError()
    
    def all_var(self) -> set[Var]:
        '''
        Return all the variables of the term `self` as a set.
        '''
        raise NotImplementedError()
    
    def free_var(self) -> set[Var]:
        '''
        Return the free variables of the term `self` as a set.
        '''
        raise NotImplementedError()
        
    
    def substitute(self, x : Var, t : Term) -> Term:
        '''
        Substitute the variable `x` with term `t` in the term `self`, and return the result.
        '''
        raise NotImplementedError()

############################
# The Sorts.
####

@Rem_term(rem_coc)
class Sort(Term):
    '''
    sort
    ```
    _
    ```
    '''
    def __eq__(self, other : Term) -> bool:
        return isinstance(other, type(self))
    
    def alpha_convertible(self, other: Term) -> bool:
        return self == other
        
    def all_var(self) -> set[Var]:
        return set()

    def free_var(self) -> set[Var]:
        return set()

    def substitute(self, x : Var, t : Term) -> Term:
        return self
    
    def dependent(self, x: Var) -> bool:
        return False


@concrete_Rem_term(rem_coc)
class SProp(Sort):
    '''
    term-SProp
    ```
    SProp
    ```
    '''

    def __str__(self) -> str:
        return "SProp"

@concrete_Rem_term(rem_coc)
class Prop(Sort):
    '''
    term-Prop
    ```
    Prop
    ```
    '''

    def __str__(self) -> str:
        return "Prop"

@concrete_Rem_term(rem_coc)
class Set(Sort):
    '''
    term-Set
    ```
    Set
    ```
    '''

    def __str__(self) -> str:
        return "Set"
        
@concrete_Rem_term(rem_coc)
class Type_i(Sort):
    '''
    term-Type
    ```
    Type(i)
    ```
    '''

    def __init__(self, i : int):
        self.Rem_type_check(i, int, 'i')
        self.Rem_other_check(0 < i, f"Invalid universe number {i}.")
        self.__i = i

    @property
    def i(self) -> int:
        return self.__i
    
    def __eq__(self, other : Term) -> bool:
        if not isinstance(other, Type_i):
            return False
        
        return self.i == other.i
    
    def __str__(self) -> str:
        return f"Type({self.i})"


############################
# Other term constructions.
###

@concrete_Rem_term(rem_coc)
class Var(Term):
    '''
    term-Var
    ```
    x
    ```
    '''

    def __init__(self, x : str):
        '''
        Parameters -> Rule Terms:
        - `x` -> `x`
        '''
        self.Rem_type_check(x, str, "x")
        self.__x = x

    def __hash__(self) -> int:
        return self.__x.__hash__()
    
    @property
    def x(self) -> str:
        return self.__x
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Var):
            return False
        
        return self.x == other.x

    def alpha_convertible(self, other: Term) -> bool:
        return self == other

    def __str__(self) -> str:
        return self.x
    
    def all_var(self) -> set[Var]:
        return {self}

    def free_var(self) -> set[Var]:
        return {self}
        
    def substitute(self, x: Var, t: Term) -> Term:
        if self == x:
            return t
        else:
            return self
        
    count = 0
    @staticmethod
    def fresh_var(terms : Tuple[Term, ...]) -> Var:
        '''
        This staticmethod returns a fresh variable not in any of `terms`, based on `count`.
        '''
        var_set = set()
        for term in terms:
            var_set.update(term.all_var())

        x = f"#{Var.count}"
        while Var(x) in var_set:
            Var.count += 1
            x = f"#{Var.count}"

        return Var(x)
    
@concrete_Rem_term(rem_coc)
class Const(Term):
    '''
    term-Const
    ```
    c
    ```
    '''

    def __init__(self, c : str):
        '''
        Parameters -> Rule Terms:
        - `c` -> `c`
        '''
        self.Rem_type_check(c, str, 'c')
        self.__c = c

    def __hash__(self) -> int:
        return self.__c.__hash__()
    
    @property
    def c(self) -> str:
        return self.__c
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Const):
            return False
        
        return self.c == other.c
    
    def alpha_convertible(self, other: Term) -> bool:
        return self == other

    def __str__(self) -> str:
        return self.c
    
    def all_var(self) -> set[Var]:
        return set()

    def free_var(self) -> set[Var]:
        return set()
        
    def substitute(self, x: Var, t: Term) -> Term:
        return self
    
###############################################################
# Terms that contain a bound variable.
###

@Rem_term(rem_coc)
class BoundTerm(Term):
    '''
    term-bound
    ```
    _
    ```
    '''

    def __init__(self, x : Var):
        # the bound variable
        self.Rem_type_check(x, Var, 'x')
        self.__x = x

    @property
    def x(self) -> Var:
        return self.__x
    
    def replace_bound(self, var : Var) -> BoundTerm:
        '''
        Replace the bound variable with a fresh `var` and return the result.
        Note: var should be fresh.
        '''
        raise NotImplementedError()

@concrete_Rem_term(rem_coc)
class Prod(BoundTerm):
    '''
    term-prod
    ```
    ∀x:T, U
    ```
    '''

    def __init__(self, x : Var, T : Term, U : Term):
        '''
        Parameters -> Rule Terms:
        - `x` -> `x`
        - `T` -> `T`
        - `U` -> `U`
        '''
        super().__init__(x)
        self.Rem_type_check(T, Term, 'T')
        self.__T = T
        self.Rem_type_check(U, Term, 'U')
        self.__U = U

    
    @property
    def T(self) -> Term:
        return self.__T
    
    @property
    def U(self) -> Term:
        return self.__U
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Prod):
            return False
        if self is other:
            return True
        
        return self.x == other.x and self.T == other.T and self.U == other.U
    
    def alpha_convertible(self, other: Term) -> bool:
        if not isinstance(other, Prod):
            return False
        
        fresh_var = Var.fresh_var((self, other))
        self_rep = self.replace_bound(fresh_var)
        other_rep = other.replace_bound(fresh_var)
        
        return self_rep.T.alpha_convertible(other_rep.T) and self_rep.U.alpha_convertible(other_rep.U)
    
    def __str__(self) -> str:

        if self.x in self.U.free_var() or self.x in self.U.free_var():

            return f"∀ {self.x}:{self.T}, {self.U}"
        
        else:

            return f"({self.T} → {self.U})"

    def all_var(self) -> set[Var]:
        return self.T.all_var() | self.U.all_var() | {self.x}
    
    def free_var(self) -> set[Var]:
        return (self.T.free_var() | self.U.free_var()) - {self.x}
    
    def substitute(self, x: Var, t: Term) -> Term:
        '''
        Note: Substitutions in such terms:
        ```
            forall (x : x), ...
        ```
        is invalid and will not be considered.
        '''

        if x != self.x:
            T_sub = self.T.substitute(x, t)
            U_sub = self.U.substitute(x, t)
            return Prod(self.x, T_sub, U_sub)
        else:
            return self
        
    def replace_bound(self, var : Var) -> Prod:
        
        return Prod(var, self.T.substitute(self.x, var), self.U.substitute(self.x, var))
        
@concrete_Rem_term(rem_coc)
class Abstract(BoundTerm):
    '''
    term-lambda
    ```
    λx:T,u
    ```
    '''

    def __init__(self, x : Var, T : Term, u : Term):
        '''
        Parameters -> Rule Terms:
        - `x` -> `x`
        - `T` -> `T`
        - `u` -> `u`
        '''
        super().__init__(x)
        self.Rem_type_check(T, Term, 'T')
        self.__T = T
        self.Rem_type_check(u, Term, 'u')
        self.__u = u
    
    @property
    def T(self) -> Term:
        return self.__T
    
    @property
    def u(self) -> Term:
        return self.__u
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Abstract):
            return False
        if self is other:
            return True
        
        return self.x == other.x and self.T == other.T and self.u == other.u

    def alpha_convertible(self, other: Term) -> bool:
        if not isinstance(other, Abstract):
            return False
        
        fresh_var = Var.fresh_var((self, other))
        self_rep = self.replace_bound(fresh_var)
        other_rep = other.replace_bound(fresh_var)
        
        return self_rep.T.alpha_convertible(other_rep.T) and self_rep.u.alpha_convertible(other_rep.u)

    def __str__(self) -> str:
        return f"λ{self.x}:{self.T},{self.u}"
    
    def all_var(self) -> set[Var]:
        return self.T.all_var() | self.u.all_var() | {self.x}

    def free_var(self) -> set[Var]:
        return (self.T.free_var() | self.u.free_var()) - {self.x}

    def substitute(self, x: Var, t: Term) -> Term:
        '''
        Note: the occurrence of `x` in `T` are similar to the situation in `Prod`.
        '''

        if x != self.x:
            T_sub = self.T.substitute(x, t)
            u_sub = self.u.substitute(x, t)
            return Prod(self.x, T_sub, u_sub)
        else:
            return self
        
    def replace_bound(self, var : Var) -> Abstract:
        return Abstract(var, self.T.substitute(self.x, var), self.u.substitute(self.x, var))
        


@concrete_Rem_term(rem_coc)
class Apply(Term):
    '''
    term-apply
    ```
    t u
    ```
    '''

    def __init__(self, t : Term, u : Term):
        '''
        Parameters -> Rule Terms:
        - `t` -> `t`
        - `u` -> `u`
        '''
        self.Rem_type_check(t, Term, 't')
        self.__t = t
        self.Rem_type_check(u, Term, 'u')
        self.__u = u

    @property
    def t(self) -> Term:
        return self.__t
    
    @property
    def u(self) -> Term:
        return self.__u
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Apply):
            return False
        if self is other:
            return True
        
        return self.t == other.t and self.u == other.u
    
    def alpha_convertible(self, other: Term) -> bool:
        if not isinstance(other, Apply):
            return False
        return self.t.alpha_convertible(other.t) and self.u.alpha_convertible(other.u)

    def __str__(self) -> str:
        return f"({self.t} {self.u})"
    
    def all_var(self) -> set[Var]:
        return self.t.all_var() | self.u.all_var()

    def free_var(self) -> set[Var]:
        return self.t.free_var() | self.u.free_var()
    
    def substitute(self, x: Var, t: Term) -> Term:
        return Apply(self.t.substitute(x, t), self.u.substitute(x, t))
    

@concrete_Rem_term(rem_coc)
class Let_in(BoundTerm):
    '''
    term-let-in
    ```
    let x:=t:T in u
    ```
    '''

    def __init__(self, x : Var, t : Term, T : Term, u : Term):
        '''
        Parameters -> Rule Terms:
        - `x` -> `x`
        - `t` -> `t`
        - `T` -> `T`
        - `u` -> `u`
        '''
        super().__init__(x)
        self.Rem_type_check(t, Term, 't')
        self.__t = t
        self.Rem_type_check(T, Term, 't')
        self.__T = T
        self.Rem_type_check(u, Term, 't')
        self.__u = u

    @property
    def t(self) -> Term:
        return self.__t
    
    @property
    def T(self) -> Term:
        return self.__T
    
    @property
    def u(self) -> Term:
        return self.__u
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Let_in):
            return False
        if self is other:
            return True
        
        return self.x == other.x and self.t == other.t and self.T == other.T and self.u == other.u

    def alpha_convertible(self, other: Term) -> bool:
        if not isinstance(other, Let_in):
            return False
        
        fresh_var = Var.fresh_var((self, other))
        self_rep = self.replace_bound(fresh_var)
        other_rep = other.replace_bound(fresh_var)

        return self_rep.t.alpha_convertible(other_rep.t) and self_rep.T.alpha_convertible(other_rep.T) and self.u.alpha_convertible(other_rep.u)

    def __str__(self) -> str:
        return f"let {self.x}:={self.t}:{self.T} in {self.u}"
    
    def all_var(self) -> set[Var]:
        return self.t.all_var() | self.T.all_var() | self.u.all_var() | {self.x}

    def free_var(self) -> set[Var]:
        return (self.t.free_var() | self.T.free_var() | self.u.free_var()) - {self.x}
    
    def substitute(self, x: Var, t: Term) -> Term:
        if x != self.x:
            t_sub = self.t.substitute(x, t)
            T_sub = self.T.substitute(x, t)
            u_sub = self.u.substitute(x, t)
            return Let_in(self.x, t_sub, T_sub, u_sub)
        else:
            return self

    def replace_bound(self, var : Var) -> Let_in:
        return Let_in(var, self.t.substitute(self.x, var), self.T.substitute(self.x, var), self.u.substitute(self.x, var))
        



#####################################################################
# Rem proof objects
###

@concrete_Rem_term(rem_coc)
class Rem_IsSort(RemProof):
    '''
    is-sort
    ```
    s ∈ S
    ```

    The proof for `s ∈ S`.
    '''

    def __init__(self, s : Sort):
        '''
        Parameters -> Rule Terms:
        - `s` -> `s`
        '''
        self.Rem_type_check(s, Sort, 's')
        self.__s = s

    @property
    def s(self) -> Sort:
        return self.__s
    
    def premises(self) -> str:
        return ""
    
    def conclusion(self) -> str:
        return f"{self.s} ∈ S"

