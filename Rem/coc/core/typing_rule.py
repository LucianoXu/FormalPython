'''

See (https://coq.inria.fr/refman/language/cic.html#global-environment).

'''


from __future__ import annotations

from .context import *
from .environment import *


################################################################
# rule framework

@Rem_term(rem_coc)
class Rem_WF(RemProof):
    '''
    well-formed
    ```
        WF(E)[Γ]
    ```
    The proof of well-formed environment and valid contex.
    '''
    def __init__(self, E : Environment, Gamma : Context):
        '''
        Parameters -> Rule Terms:
        - `E` -> `E`
        - `Gamma` -> `Γ`
        '''
        self.Rem_type_check(E, Environment, 'E')
        self.Rem_type_check(Gamma, Context, 'Γ')
        self.__E = E
        self.__Gamma = Gamma

    @property
    def E(self) -> Environment:
        return self.__E
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma

    def conclusion(self) -> str:
        return f"WF({self.E}){self.Gamma}"
    
@Rem_term(rem_coc)
class Rem_WT(RemProof):
    '''
    well-typed
    ```
        E[Γ] ⊢ t : T
    ```
    The proof of well-typed term.
    '''
    def __init__(self, E : Environment, Gamma : Context, t : Term, T : Term):
        '''
        Parameters -> Rule Terms:
        - `E` -> `E`
        - `Gamma` -> `Γ`
        - `t` -> `t`
        - `T` -> `T`
        '''
        self.Rem_type_check(E, Environment, 'E')
        self.Rem_type_check(Gamma, Context, 'Γ')
        self.Rem_type_check(t, Term, 't')
        self.Rem_type_check(T, Term, 'T')
        self.__E = E
        self.__Gamma = Gamma
        self.__t = t
        self.__T = T
    
    @property
    def E(self) -> Environment:
        return self.__E
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma
    
    @property
    def t(self) -> Term:
        return self.__t

    @property
    def T(self) -> Term:
        return self.__T
    
    def conclusion(self) -> str:
        return f"{self.E}{self.Gamma} ⊢ {self.t} : {self.T}"


###############################################################
# specific rules

@concrete_Rem_term(rem_coc)
class Rem_W_Empty(Rem_WF):
    '''
    W-Empty
    ```
        --------
        WF([])[]
    ```
    '''

    def __init__(self):
        '''
        Parameters -> Rule Terms: none.
        '''

        # the conclusion `WF([])[]`
        super().__init__(Environment(), Context())

        
    def premises(self) -> str:
        return ""


@concrete_Rem_term(rem_coc)
class Rem_W_Local_Assum(Rem_WF):
    '''
    W-Local-Assum
    ```
        E[Γ] ⊢ T : s
        s ∈ S
        x ∉ Γ
        ------------------------------
        WF(E)[Γ::(x:T)]
    ```
    '''

    def __init__(self, wt : Rem_WT, s_sort : Rem_IsSort, x_notin_Gamma : Rem_Cont_Not_Contain_Var):
        '''
        Parameters -> Rule Terms:
        - `wt` -> `E[Γ] ⊢ T : s`
        - `s_sort` -> `s ∈ S`
        - `x_notin_Gamma` -> `x ∉ Γ`
        '''

        self.Rem_type_check(wt, Rem_WT, 'E[Γ] ⊢ T : s')
        
        self.Rem_type_check(s_sort, Rem_IsSort, 's ∈ S')

        self.Rem_type_check(x_notin_Gamma, Rem_Cont_Not_Contain_Var, 'x ∉ Γ')

        # consistent `s`
        self.Rem_consistency_check(wt.T, s_sort.s, 's')
        
        # consistent `Γ`
        self.Rem_consistency_check(wt.Gamma, x_notin_Gamma.Gamma, 'Γ')
        
        self.__wt = wt
        self.__s_sort = s_sort
        self.__x_notin_Gamma = x_notin_Gamma


        # the conclusion
        new_Gamma = x_notin_Gamma.Gamma.push(
            LocalTyping(x_notin_Gamma.x, wt.t)
        )
        super().__init__(wt.E, new_Gamma)
    
    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__s_sort.conclusion() + "\n"
        res += self.__x_notin_Gamma.conclusion() + "\n"
        return res

@concrete_Rem_term(rem_coc)
class Rem_W_Local_Def(Rem_WF):
    '''
    W-Local-Def
    ```
        E[Γ] ⊢ t : T
        x ∉ Γ
        -------------------------
        WF(E)[Γ::(x:=t:T)]
    ```
    '''

    def __init__(self, wt : Rem_WT, x_notin_Gamma : Rem_Cont_Not_Contain_Var):
        '''
        Parameters -> Rule Terms:
        - `wt` -> `E[Γ] ⊢ t : T`
        - `x_notin_Gamma` -> `x ∉ Γ`
        '''


        self.Rem_type_check(wt, Rem_WT, 'E[Γ] ⊢ t : T')

        self.Rem_type_check(x_notin_Gamma, Rem_Cont_Not_Contain_Var, 'x ∉ Γ')

        # consistent `Γ`
        self.Rem_consistency_check(wt.Gamma, x_notin_Gamma.Gamma, 'Γ')

        self.__wt = wt
        self.__x_notin_Gamma = x_notin_Gamma

        # the conclusion
        new_Gamma = x_notin_Gamma.Gamma.push(
            LocalDef(x_notin_Gamma.x, wt.t, wt.T)
        )
        super().__init__(wt.E, new_Gamma)

    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__x_notin_Gamma.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_W_Global_Assum(Rem_WF):
    '''
    W-Global-Assum
    ```
        E[] ⊢ T : s
        s ∈ S
        c ∉ E
        -------------------------
        WF(E; c:T)
    ```
    '''

    def __init__(self, wt : Rem_WT, s_sort : Rem_IsSort, c_notin_E : Rem_Env_Not_Contain_Const):
        '''
        Parameters -> Rule Terms:
        - `wt` -> `E[] ⊢ T : s`
        - `s_sort` -> `s ∈ S`
        - `c_notin_E` -> `c ∉ E`
        '''

        self.Rem_type_check(wt, Rem_WT, 'E[] ⊢ T : s')

        self.Rem_type_check(s_sort, Rem_IsSort, 's ∈ S')

        self.Rem_type_check(c_notin_E, Rem_Env_Not_Contain_Const, 'c ∉ E')

        # empty Gamma
        self.Rem_other_check(wt.Gamma.is_empty, "Context is not empty.")

        # consistent `s`
        self.Rem_consistency_check(wt.T, s_sort.s, 's')

        # consistent `E`
        self.Rem_consistency_check(wt.E, c_notin_E, 'E')

        self.__wt = wt
        self.__s_sort = s_sort
        self.__c_notin_E = c_notin_E

        # the conclusion
        new_E = wt.E.push(
            GlobalTyping(c_notin_E.c, wt.T)
        )
        super().__init__(new_E, Context())

    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__s_sort.conclusion() + "\n"
        res += self.__c_notin_E.conclusion() + "\n"
        return res
    
@concrete_Rem_term(rem_coc)
class Rem_W_Global_Def(Rem_WF):
    '''
    W-Global-Def
    ```
        E[] ⊢ t : T
        c ∉ E
        -------------------------
        WF(E; c:=t:T)
    ```
    '''

    def __init__(self, wt : Rem_WT, c_notin_E : Rem_Env_Not_Contain_Const):
        '''
        Parameters -> Rule Terms:
        - `wt` -> `E[] ⊢ t : T`
        - `c_notin_E` -> `c ∉ E`
        '''

        self.Rem_type_check(wt, Rem_WT, 'E[] ⊢ t : T')

        self.Rem_type_check(c_notin_E, Rem_Env_Not_Contain_Const, 'c ∉ E')

        # empty Gamma
        self.Rem_other_check(wt.Gamma.is_empty, "Context is not empty.")

        # consistent `E`
        self.Rem_consistency_check(wt.E, c_notin_E.E, 'E')

        self.__wt = wt
        self.__c_notin_E = c_notin_E

        # the conclusion
        new_E = wt.E.push(
            GlobalDef(c_notin_E.c, wt.t, wt.T)
        )
        super().__init__(new_E, Context())

    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__c_notin_E.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_Ax_SProp(Rem_WT):
    '''
    Ax-SProp
    ```
        WF(E)[Γ]
        -----------------
        E[Γ] ⊢ SProp : Type(1)
    ```
    '''

    def __init__(self, wf : Rem_WF):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        '''


        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')
        self.__wf = wf

        # the conclusion
        super().__init__(wf.E, wf.Gamma, SProp(), Type_i(1))
    
    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_Ax_Prop(Rem_WT):
    '''
    Ax-Prop
    ```
        WF(E)[Γ]
        -----------------
        E[Γ] ⊢ Prop : Type(1)
    ```
    '''

    def __init__(self, wf : Rem_WF):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        '''

        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')
        self.__wf = wf

        # the conclusion
        super().__init__(wf.E, wf.Gamma, Prop(), Type_i(1))
    
    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_Ax_Set(Rem_WT):
    '''
    Ax-Set
    ```
        WF(E)[Γ]
        -----------------
        E[Γ] ⊢ Set : Type(1)
    ```
    '''

    def __init__(self, wf : Rem_WF):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        '''

        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')
        self.__wf = wf

        # the conclusion
        super().__init__(wf.E, wf.Gamma, Set(), Type_i(1))
    
    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        return res


@concrete_Rem_term(rem_coc)
class Rem_Ax_Type(Rem_WT):
    '''
    Ax-Type
    ```
        WF(E)[Γ]
        ----------------------------
        E[Γ] ⊢ Type(i) : Type(i + 1)
    ```
    '''

    def __init__(self, wf : Rem_WF, i : int):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        - `i` -> `i`
        '''

        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')

        # a python number `i`
        self.Rem_type_check(i, int, 'i')

        self.__wf = wf
        self.__i = i

        # the conclusion
        super().__init__(wf.E, wf.Gamma, Type_i(i), Type_i(i+1))
    
    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_Var(Rem_WT):
    '''
    Var
    ```
        WF(E)[Γ]
        (x : T) ∈ Γ or (x:=t : T) ∈ Γ
        -----------------------------
        E[Γ] ⊢ x:T
    ```
    '''

    def __init__(self, wf : Rem_WF, x_dec_in_Gamma : Rem_Cont_Contain_Typing):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        - `x_dec_in_Gamma` -> `(x : T) ∈ Γ or (x:=t : T) ∈ Γ`
        '''

        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')

        self.Rem_type_check(x_dec_in_Gamma, Rem_Cont_Contain_Typing, '(x : T) ∈ Γ or (x:=t : T) ∈ Γ')

        # consistent `Γ`
        self.Rem_consistency_check(wf.Gamma, x_dec_in_Gamma.Gamma, 'Γ')
        
        self.__wf = wf
        self.__x_dec_in_Gamma = x_dec_in_Gamma

        # the conclusion
        super().__init__(wf.E, wf.Gamma, x_dec_in_Gamma.x_typing.x, x_dec_in_Gamma.x_typing.T)


    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__x_dec_in_Gamma.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_Const(Rem_WT):
    '''
    Const
    ```
        WF(E)[Γ]
        (c : T) ∈ E or (c:=t : T) ∈ E
        -----------------------------
        E[Γ] ⊢ c:T
    ```
    '''

    def __init__(self, wf : Rem_WF, c_dec_in_E : Rem_Env_Contain_Typing):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        - `c_dec_in_E` -> `(c : T) ∈ E or (c:=t : T) ∈ E`
        '''

        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')

        self.Rem_type_check(c_dec_in_E, Rem_Env_Contain_Typing, '(c : T) ∈ E or (c:=t : T) ∈ E')

        # consistent `E`
        self.Rem_consistency_check(wf.E, c_dec_in_E.E, "E")
        
        self.__wf = wf
        self.__c_dec_in_E = c_dec_in_E

        # the conclusion
        super().__init__(wf.E, wf.Gamma, c_dec_in_E.c_typing.c, c_dec_in_E.c_typing.T)


    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__c_dec_in_E.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_Prod_SProp(Rem_WT):
    '''
    Prod-SProp
    ```
        E[Γ] ⊢ T : s
        s ∈ S
        E[Γ::(x:T)] ⊢ U : SProp
        ---------------------------
        E[Γ] ⊢ ∀x:T, U : SProp
    ```
    '''

    def __init__(self, wt_outer : Rem_WT, s_sort : Rem_IsSort, wt_inner : Rem_WT):
        '''
        Parameters -> Rule Terms:
        - `wt_outer` -> `E[Γ] ⊢ T : s`
        - `s_sort` -> `s ∈ S`
        - `wt_inner` -> `E[Γ::(x:T)] ⊢ U : SProp`
        '''

        self.Rem_type_check(wt_outer, Rem_WT, 'E[Γ] ⊢ T : s')

        self.Rem_type_check(s_sort, Rem_IsSort, 's ∈ S')

        self.Rem_type_check(wt_inner, Rem_WT, 'E[Γ::(x:T)] ⊢ U : SProp')

        # consistent `s`
        self.Rem_consistency_check(wt_outer.T, s_sort.s, 's')
        
        # consistent `E`
        self.Rem_consistency_check(wt_outer.E, wt_inner.E, 'E')
        
        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `Gamma`
        self.Rem_consistency_check(wt_outer.Gamma, Gamma_pre, "Γ")

        # consistent `T`
        self.Rem_consistency_check(wt_outer.t, dec.T, "T")
        
        # consisten `SProp`
        self.Rem_consistency_check(wt_inner.T, SProp(), 'SProp')
        
        self.__wt_outer = wt_outer
        self.__s_sort = s_sort
        self.__wt_inner = wt_inner

        # the conclusion
        prod = Prod(dec.x, dec.T, wt_inner.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, prod, SProp())

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += self.__s_sort.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_Prod_Prop(Rem_WT):
    '''
    Prod-Prop
    ```
        E[Γ] ⊢ T : s
        s ∈ S
        E[Γ::(x:T)] ⊢ U : Prop
        ---------------------------
        E[Γ] ⊢ ∀x:T, U : Prop
    ```
    '''

    def __init__(self, wt_outer : Rem_WT, s_sort : Rem_IsSort, wt_inner : Rem_WT):
        '''
        Parameters -> Rule Terms:
        - `wt_outer` -> `E[Γ] ⊢ T : s`
        - `s_sort` -> `s ∈ S`
        - `wt_inner` -> `E[Γ::(x:T)] ⊢ U : Prop`
        '''
        
        self.Rem_type_check(wt_outer, Rem_WT, 'E[Γ] ⊢ T : s')

        self.Rem_type_check(s_sort, Rem_IsSort, 's ∈ S')

        self.Rem_type_check(wt_inner, Rem_WT, 'E[Γ::(x:T)] ⊢ U : Prop')

        # consistent `s`
        self.Rem_consistency_check(wt_outer.T, s_sort.s, 's')
        
        # consistent `E`
        self.Rem_consistency_check(wt_outer.E, wt_inner.E, 'E')

        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `Γ`
        self.Rem_consistency_check(wt_outer.Gamma, Gamma_pre, 'Γ')
        
        # consistent `T`
        self.Rem_consistency_check(wt_outer.t, dec.T, 'T')
        
        # consistent `Prop`
        self.Rem_consistency_check(wt_inner.T, Prop(), 'Prop')
        
        self.__wt_outer = wt_outer
        self.__s_sort = s_sort
        self.__wt_inner = wt_inner

        # the conclusion
        prod = Prod(dec.x, dec.T, wt_inner.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, prod, Prop())

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += self.__s_sort.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    
    
@concrete_Rem_term(rem_coc)
class Rem_Prod_Set(Rem_WT):
    '''
    Prod-Set
    ```
        E[Γ] ⊢ T : s
        s ∈ {SProp, Prop, Set}
        E[Γ::(x:T)] ⊢ U : Set
        ---------------------------
        E[Γ] ⊢ ∀x:T, U : Set
    ```
    '''

    def __init__(self, wt_outer : Rem_WT, s_sort : Rem_IsSort, wt_inner : Rem_WT):
        '''
        Parameters -> Rule Terms:
        - `wt_outer` -> `E[Γ] ⊢ T : s`
        - `s_sort` -> `s ∈ {SProp, Prop, Set}`
        - `wt_inner` -> `E[Γ::(x:T)] ⊢ U : Set`
        '''
        
        self.Rem_type_check(wt_outer, Rem_WT, 'E[Γ] ⊢ T : s')

        self.Rem_other_check(
            (isinstance(s_sort.s, SProp) or isinstance(s_sort.s, Prop) or isinstance(s_sort.s, Set)), 
            f"'s ∈ {{SProp, Prop, Set}}' not satisfied for s = {s_sort.s}."
        )


        self.Rem_type_check(wt_inner, Rem_WT, 'E[Γ::(x:T)] ⊢ U : Set')

        # consistent `s`
        self.Rem_consistency_check(wt_outer.T, s_sort.s, 's')
        
        # consistent `E`
        self.Rem_consistency_check(wt_outer.E, wt_inner.E, 'E')

        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `Γ`
        self.Rem_consistency_check(wt_outer.Gamma, Gamma_pre, 'Γ')
        
        # consistent `T`
        self.Rem_consistency_check(wt_outer.t, dec.T, 'T')
        
        # consistent `Set`
        self.Rem_consistency_check(wt_inner.T, Set(), 'Set')
        
        self.__wt_outer = wt_outer
        self.__s_sort = s_sort
        self.__wt_inner = wt_inner

        # the conclusion
        prod = Prod(dec.x, dec.T, wt_inner.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, prod, Set())

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += f"{self.__s_sort.s} ∈ {{SProp, Prop, Set}}"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_Prod_Type(Rem_WT):
    '''
    Prod-Type
    ```
        E[Γ] ⊢ T : s
        s ∈ {SProp, Type(i)}
        E[Γ::(x:T)] ⊢ U : Type(i)
        ---------------------------
        E[Γ] ⊢ ∀x:T, U : Type(i)
    ```
    '''

    def __init__(self, wt_outer : Rem_WT, s_sort : Rem_IsSort, wt_inner : Rem_WT):
        '''
        Parameters -> Rule Terms:
        - `wt_outer` -> `E[Γ] ⊢ T : s`
        - `s_sort` -> `s ∈ {SProp, Type(i)}`
        - `wt_inner` -> `E[Γ::(x:T)] ⊢ U : Type(i)`
        '''

        self.Rem_type_check(wt_outer, Rem_WT, 'E[Γ] ⊢ T : s')

        self.Rem_other_check(
            (isinstance(s_sort.s, SProp) or isinstance(s_sort.s, Type)),
            f"'s ∈ {{SProp, Type(i)}}' not satisfied for s = {s_sort.s}."
        )


        self.Rem_type_check(wt_inner, Rem_WT, 'E[Γ::(x:T)] ⊢ U : Type(i)')

        # consistent `s`
        self.Rem_consistency_check(wt_outer.T, s_sort.s, 's')
        
        # consistent `E`
        self.Rem_consistency_check(wt_outer.E, wt_inner.E, 'E')

        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `Γ`
        self.Rem_consistency_check(wt_outer.Gamma, Gamma_pre, 'Γ')
        
        # consistent `T`
        self.Rem_consistency_check(wt_outer.t, dec.T, 'T')
        
        # consistent `Type(i)`
        self.Rem_type_check(wt_inner.T, Type_i, 'Type(i)')
        
        self.__wt_outer = wt_outer
        self.__s_sort = s_sort
        self.__wt_inner = wt_inner

        # the conclusion
        prod = Prod(dec.x, dec.T, wt_inner.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, prod, wt_inner.T)

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += f"{self.__s_sort.s} ∈ {{SProp, Type(i)}}"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    
    
@concrete_Rem_term(rem_coc)
class Rem_Lam(Rem_WT):
    '''
    Lam
    ```
        E[Γ] ⊢ ∀x:T, U : s
        E[Γ::(x:T)] ⊢ t : U
        --------------------
        E[Γ] ⊢ λx:T,t : ∀x:T, U
    ```
    '''

    def __init__(self, wt_outer : Rem_WT, wt_inner : Rem_WT):
        '''
        Parameters -> Rule Terms:
        - `wt_outer` -> `E[Γ] ⊢ ∀x:T, U : s`
        - `wt_inner` -> `E[Γ::(x:T)] ⊢ t : U`
        '''

        self.Rem_type_check(wt_outer, Rem_WT, 'E[Γ] ⊢ ∀x:T, U : s')

        self.Rem_type_check(wt_inner, Rem_WT, 'E[Γ::(x:T)] ⊢ t : U')

        self.Rem_type_check(wt_outer.t, Prod, '∀x:T, U')
        assert isinstance(wt_outer.t, Prod)
        
        # break `Γ::(x:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()

        # consistent `E`
        self.Rem_consistency_check(wt_outer.E, wt_inner.E, 'E')

        # consistent `Γ`
        self.Rem_consistency_check(wt_outer.Gamma, Gamma_pre, 'Γ')
    
        # consistent `x`
        self.Rem_consistency_check(wt_outer.t.x, dec.x, 'x')
        
        # consistent `T`
        self.Rem_consistency_check(wt_outer.t.T, dec.T, 'T')
        
        # consistent `U`
        self.Rem_consistency_check(wt_outer.t.U, wt_inner.T, 'U')
        
        self.__wt_outer = wt_outer
        self.__wt_inner = wt_inner

        # the conclusion
        lam = Abstract(dec.x, dec.T, wt_inner.t)
        prod = Prod(dec.x, dec.T, wt_inner.T)
        super().__init__(wt_outer.E, wt_outer.Gamma, lam, prod)

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_App(Rem_WT):
    '''
    App
    ```
        E[Γ] ⊢ t: ∀x:U, T
        E[Γ] ⊢ u : U
        --------------------
        E[Γ] ⊢ (t u) : T{x/u}
    ```
    '''

    def __init__(self, wt_t : Rem_WT, wt_u : Rem_WT):
        '''
        Parameters -> Rule Terms:
        - `wt_t` -> `E[Γ] ⊢ t: ∀x:U, T`
        - `wt_u` -> `E[Γ] ⊢ u : U`
        '''

        self.Rem_type_check(wt_t, Rem_WT, 'E[Γ] ⊢ t: ∀x:U, T')

        self.Rem_type_check(wt_u, Rem_WT, 'E[Γ] ⊢ u : U')

        # extact `∀x:U, T`
        self.Rem_type_check(wt_t.T, Prod, '∀x:U, T')
        assert isinstance(wt_t.T, Prod)
        
        # consistent `E`
        self.Rem_consistency_check(wt_t.E, wt_u.E, 'E')

        # consistent `Γ`
        self.Rem_consistency_check(wt_t.Gamma, wt_u.Gamma, 'Γ')
        
        # consistent `U`
        self.Rem_consistency_check(wt_t.T.T, wt_u.T, 'U')
        
        self.__wt_t = wt_t
        self.__wt_u = wt_u

        # the conclusion
        app = Apply(wt_t.t, wt_u.t)
        T_sub = wt_t.T.U.substitute(wt_t.T.x, wt_u.t)
        super().__init__(wt_t.E, wt_t.Gamma, app, T_sub)

    def premises(self) -> str:
        res = self.__wt_t.conclusion() + "\n"
        res += self.__wt_u.conclusion() + "\n"
        return res
    

@concrete_Rem_term(rem_coc)
class Rem_Let(Rem_WT):
    '''
    Let
    ```
        E[Γ] ⊢ t : T
        E[Γ::(x:=t:T)] ⊢ u : U
        --------------------
        E[Γ] ⊢ let x:=t:T in u : U{x/t}
    ```
    '''

    def __init__(self, wt_outer : Rem_WT, wt_inner : Rem_WT):
        '''
        Parameters -> Rule Terms:
        - `wt_outer` -> `E[Γ] ⊢ t : T`
        - `wt_inner` -> `E[Γ::(x:=t:T)] ⊢ u : U`
        '''

        self.Rem_type_check(wt_outer, Rem_WT, 'E[Γ] ⊢ t : T')

        self.Rem_type_check(wt_inner, Rem_WT, 'E[Γ::(x:=t:T)] ⊢ u : U')

        
        # break `Γ::(x:=t:T)`
        Gamma_pre, dec = wt_inner.Gamma.pop()
        self.Rem_type_check(dec, LocalDef, 'x:=t:T')
        assert isinstance(dec, LocalDef)

        # consistent `E`
        self.Rem_consistency_check(wt_outer.E, wt_inner.E, 'E')

        # consistent `Γ`
        self.Rem_consistency_check(wt_outer.Gamma, Gamma_pre, 'Γ')

        # consistent `t`
        self.Rem_consistency_check(dec.t, wt_outer.t, 't')

        # consistent `T`
        self.Rem_consistency_check(wt_outer.T, dec.T, 'T')
        
        self.__wt_outer = wt_outer
        self.__wt_inner = wt_inner

        # the conclusion
        let_in = Let_in(dec.x, dec.t, dec.T, wt_inner.t)
        U_sub = wt_inner.T.substitute(dec.x, dec.t)
        super().__init__(wt_outer.E, wt_outer.Gamma, let_in, U_sub)

    def premises(self) -> str:
        res = self.__wt_outer.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

# basic typing rules ends here
#####################################################

