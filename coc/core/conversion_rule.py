'''

See (https://coq.inria.fr/refman/language/core/conversion.html)

'''


from __future__ import annotations

from .context import *
from .environment import *
from .typing_rule import Rem_WF, Rem_WT


# alpha-conversion judgement is implemented in `Term`.
    
@Rem_term
class Rem_reduction(RemProof):
    '''
    reduce
    ```
        E[Γ] ⊢ t1 ▷ t2
    ```

    Note: the reduction rule here also considers alpha-convertibility.
    '''
    def __init__(self, E : Environment, Gamma : Context, t1 : Term, t2 : Term):
        '''
        Parameters -> Rule Terms:
        - `E` -> `E`
        - `Gamma` -> `Γ`
        - `t1` -> `t1`
        - `t2` -> `t2`
        '''
        self.Rem_type_check(E, Environment, 'E')
        self.Rem_type_check(Gamma, Context, 'Γ')
        self.Rem_type_check(t1, Term, 't1')
        self.Rem_type_check(t2, Term, 't2')

        self.__E = E
        self.__Gamma = Gamma
        self.__t1 = t1
        self.__t2 = t2

    @property
    def E(self) -> Environment:
        return self.__E
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma
    
    @property
    def t1(self) -> Term:
        return self.__t1

    @property
    def t2(self) -> Term:
        return self.__t2

    def conclusion(self) -> str:
        return f"{self.E}{self.Gamma} ⊢ {self.t1} ▷ {self.t2}"
    

@concrete_Rem_term
class Rem_beta_reduction(Rem_reduction):
    '''
    β-reduction
    ```
        -----------------------------
        E[Γ] ⊢ ((λx:T,t) u) ▷ t{x/u}
    ```
    '''
    

    def __init__(self, E : Environment, Gamma : Context, t1 : Apply):
        '''
        Parameters -> Rule Terms:
        - `E` -> `E`
        - `Gamma` -> `Γ`
        - `t1` -> `(λx:T,t) u`
        '''
        self.Rem_type_check(t1, Apply, '(λx:T,t) u')
        self.Rem_type_check(t1.t, Abstract, 'λx:T,t')
        assert isinstance(t1.t, Abstract)


        # the conclusion `E[Γ] ⊢ ((λx:T,t) u) ▷ t{x/u}`
        t2_sub = t1.t.u.substitute(t1.t.x, t1.u)        
        super().__init__(E, Gamma, t1, t2_sub)

    def premises(self) -> str:
        return ""


@concrete_Rem_term
class Rem_delta_reduction(Rem_reduction):
    '''
    δ-reduction
    ```
        WF(E)[Γ]
        (x:=t:T) ∈ Γ
        -----------------------------
        E[Γ] ⊢ x ▷ t
    ```
    '''

    def __init__(self, wf : Rem_WF, x_in_Gamma : Rem_Cont_Contain_Def):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        - `x_in_Gamma` -> `(x:=t:T) ∈ Γ`
        '''
        
        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')

        self.Rem_type_check(x_in_Gamma, Rem_Cont_Contain_Def, '(x:=t:T) ∈ Γ')

        # consistent `Γ`
        self.Rem_consistency_check(wf.Gamma, x_in_Gamma, 'Γ')
        
        self.__wf = wf
        self.__x_in_Gamma = x_in_Gamma

        # the conclusion
        super().__init__(wf.E, wf.Gamma, x_in_Gamma.x_def.x, x_in_Gamma.x_def.t)

    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__x_in_Gamma.conclusion() + "\n"
        return res
    

@concrete_Rem_term
class Rem_Delta_reduction(Rem_reduction):
    '''
    Δ-reduction
    ```
        WF(E)[Γ]
        (c:=t:T) ∈ E
        -----------------------------
        E[Γ] ⊢ c ▷ t
    ```
    '''

    def __init__(self, wf : Rem_WF, c_in_E : Rem_Env_Contain_Def):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        - `c_in_E` -> `(c:=t:T) ∈ E`
        '''

        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')

        self.Rem_type_check(c_in_E, Rem_Env_Contain_Def, '(c:=t:T) ∈ E')

        # consistent `E`
        self.Rem_consistency_check(wf.E, c_in_E, 'E')
        
        self.__wf = wf
        self.__c_in_E = c_in_E

        # the conclusion
        super().__init__(wf.E, wf.Gamma, c_in_E.c_def.c, c_in_E.c_def.t)

    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__c_in_E.conclusion() + "\n"
        return res
    

# ι-reduction is omitted here.


@concrete_Rem_term
class Rem_zeta_reduction(Rem_reduction):
    '''
    ζ-reduction
    ```
        WF(E)[Γ]
        E[Γ] ⊢ u : U
        E[Γ::(x:=u:U)] ⊢ t : T
        ------------------------------------
        E[Γ] ⊢ let x := u : U in t ▷ t{x/u}
    ```
    '''

    def __init__(self, wf : Rem_WF, wt_outer : Rem_WT, wt_inner : Rem_WT):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        - `wt_outer` -> `E[Γ] ⊢ u : U`
        - `wt_inner` -> `E[Γ::(x:=u:U)] ⊢ t : T`
        '''

        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')

        self.Rem_type_check(wt_outer, Rem_WT, 'E[Γ] ⊢ u : U')

        self.Rem_type_check(wt_inner, Rem_WT, 'E[Γ::(x:=u:U)] ⊢ t : T')

        # consistent `E`
        self.Rem_consistency_check(wf.E, wt_outer.E, 'E')
        self.Rem_consistency_check(wf.E, wt_inner.E, 'E')

        # break `Γ::(x:=u:U)`
        Gamma_pre, dec = wt_inner.Gamma.pop()
        self.Rem_type_check(dec, LocalDef, 'Γ::(x:=u:U)')
        assert isinstance(dec, LocalDef)

        # consistent `Γ`
        self.Rem_consistency_check(wf.Gamma, wt_outer.Gamma, 'Γ')
        self.Rem_consistency_check(wf.Gamma, Gamma_pre, 'Γ')
        
        # consistent `u`
        self.Rem_consistency_check(wt_outer.t, dec.t, 'u')
        
        # consistent `U`
        self.Rem_consistency_check(wt_outer.T, dec.T, 'U')
        
        self.__wf = wf
        self.__wt_outer = wt_outer
        self.__wt_inner = wt_inner

        # the conclusion
        t1 = Let_in(dec.x, dec.t, dec.T, wt_inner.t)
        t2 = wt_inner.t.substitute(dec.x, wt_outer.t)
        super().__init__(wf.E, wf.Gamma, t1, t2)

    def premises(self) -> str:
        res = self.__wf.conclusion() + "\n"
        res += self.__wt_outer.conclusion() + "\n"
        res += self.__wt_inner.conclusion() + "\n"
        return res
    

@concrete_Rem_term
class Rem_eta_conversion(RemProof):
    '''
    η-expansion (conversion)

    ```
        E[Γ] ⊢ λx:T,u : ∀y:T, U
        E[Γ::(x:T)] ⊢ u =βδιζη (t x)
        -------------------
        E[Γ] ⊢ t =η λx:T,u
    ```

    It is legal to identify any term `t` of functional type `∀x:T, U` with its so-called η-expansion `λx:T,(t x)`.

    Here a special property is used: because of the generation rule for `E[Γ] ⊢ λx:T,u : ∀x:T, U`, x will not be contained in `Γ`.
    Note that this rule is 'convertible' but not 'reducible'.
    '''

    def __init__(self, wt : Rem_WT, convert : Rem_convertible):
        '''
        Parameters -> Rule Terms:
        - `wt` -> `E[Γ] ⊢ λx:T,u : ∀y:T, U`
        - `convert` -> `E[Γ::(x:T)] ⊢ u =βδιζη (t x)`
        '''

        self.Rem_type_check(wt, Rem_WT, 'E[Γ] ⊢ λx:T,u : ∀x:T, U')
        self.Rem_type_check(wt.t, Abstract, 'λx:T,u')
        assert isinstance(wt.t, Abstract)
        self.Rem_type_check(wt.T, Prod, '∀y:T, U')
        assert isinstance(wt.T, Prod)


        self.Rem_type_check(convert, Rem_convertible, 'E[Γ::(x:T)] ⊢ u =βδιζη (t x)')
        self.Rem_type_check(convert.t2, Apply, 't x')
        assert isinstance(convert.t2, Apply)

        # break `Γ::(x:T)`
        Gamma_pre, dec = convert.Gamma.pop()

        # consistent `E`
        self.Rem_consistency_check(wt.E, convert.E, 'E')
        
        # consistent `Γ`
        self.Rem_consistency_check(wt.Gamma, Gamma_pre, 'Γ')
        
        # consistent `x`
        self.Rem_consistency_check(wt.t.x, dec.x, 'x')
        self.Rem_consistency_check(wt.t.x, convert.t2.u, 'x')
        
        # consistent `T`
        self.Rem_consistency_check(wt.t.T, wt.T.T, 'T')
        self.Rem_consistency_check(wt.t.T, dec.T, 'T')
        
        # consistent `u`
        self.Rem_consistency_check(wt.t.u, convert.t1, 'u')
        
        self.__wt = wt
        self.__convert = convert

        # the proof `E[Γ] ⊢ t ~η λx:T,u` complete


    @property
    def E(self) -> Environment:
        return self.__wt.E
    
    @property
    def Gamma(self) -> Context:
        return self.__wt.Gamma

    @property
    def t(self) -> Term:
        assert isinstance(self.__convert.t2, Apply)
        return self.__convert.t2.t
    
    @property
    def lam(self) -> Abstract:
        assert isinstance(self.__wt.t, Abstract)
        return self.__wt.t

    def premises(self) -> str:
        res = self.__wt.conclusion() + "\n"
        res += self.__convert.conclusion() + "\n"
        return res
    
    def conclusion(self) -> str:
        return f"{self.E}{self.Gamma} ⊢ {self.t} =η {self.lam}"
    

#############################################################
# rules for compatibility of reduction with term construction

@concrete_Rem_term
class Rem_red_prod_T(Rem_reduction):
    '''
    red-prod-T
    ```
        E[Γ] ⊢ T1 ▷ T2
        ---------------------------
        E[Γ] ⊢ ∀x:T1, U ▷ ∀x:T2, U
    ```
    '''
    def __init__(self, red : Rem_reduction, x : Var, U : Term):
        '''
        Parameters -> Rule Terms:
        - `red` -> `E[Γ] ⊢ T1 ▷ T2`
        - `x` -> `x`
        - `U` -> `U`
        '''
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ T1 ▷ T2')

        self.Rem_type_check(x , Var, "x")

        self.Rem_type_check(U, Term, 'U')

        self.__red = red

        super().__init__(red.E, red.Gamma, 
            Prod(x, red.t1, U), Prod(x, red.t2, U)
        )

    def premises(self) -> str:
        return self.__red.conclusion()


@concrete_Rem_term
class Rem_red_prod_U(Rem_reduction):
    '''
    red-prod-T
    ```
        E[Γ] ⊢ U1 ▷ U2
        ---------------------------
        E[Γ] ⊢ ∀x:T, U1 ▷ ∀x:T, U2
    ```
    '''
    def __init__(self, red : Rem_reduction, x : Var, T : Term):
        '''
        Parameters -> Rule Terms:
        - `red` -> `E[Γ] ⊢ U1 ▷ U2`
        - `x` -> `x`
        - `T` -> `T`
        '''
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ U1 ▷ U2')

        self.Rem_type_check(x , Var, "x")

        self.Rem_type_check(T, Term, 'T')

        self.__red = red

        super().__init__(red.E, red.Gamma, 
            Prod(x, T, red.t1), Prod(x, T, red.t2)
        )

    def premises(self) -> str:
        return self.__red.conclusion()



@concrete_Rem_term
class Rem_red_abstract_T(Rem_reduction):
    '''
    red-abstract-T
    ```
        E[Γ] ⊢ T1 ▷ T2
        ---------------------------
        E[Γ] ⊢ λx:T1, u ▷ λx:T2, u
    ```
    '''
    def __init__(self, red : Rem_reduction, x : Var, u : Term):
        '''
        Parameters -> Rule Terms:
        - `E[Γ] ⊢ T1 ▷ T2`
        - `x` -> `x`
        - `u` -> `u`
        '''
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ T1 ▷ T2')

        self.Rem_type_check(x , Var, "x")

        self.Rem_type_check(u, Term, 'u')

        self.__red = red

        super().__init__(red.E, red.Gamma, 
            Abstract(x, red.t1, u), Abstract(x, red.t2, u)
        )

    def premises(self) -> str:
        return self.__red.conclusion()


@concrete_Rem_term
class Rem_red_abstract_u(Rem_reduction):
    '''
    red-abstract-u
    ```
        E[Γ] ⊢ u1 ▷ u2
        ---------------------------
        E[Γ] ⊢ λx:T, u1 ▷ λx:T, u2
    ```
    '''
    def __init__(self, red : Rem_reduction, x : Var, T : Term):
        '''
        Parameters -> Rule Terms:
        - `E[Γ] ⊢ u1 ▷ u2`
        - `x` -> `x`
        - `T` -> `T`
        '''
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ u1 ▷ u2')

        self.Rem_type_check(x , Var, "x")

        self.Rem_type_check(T, Term, 'T')

        self.__red = red

        super().__init__(red.E, red.Gamma, 
            Abstract(x, T, red.t1), Abstract(x, T, red.t2)
        )

    def premises(self) -> str:
        return self.__red.conclusion()


@concrete_Rem_term
class Rem_red_apply_t(Rem_reduction):
    '''
    red-apply-t
    ```
        E[Γ] ⊢ t1 ▷ t2
        ---------------------------
        E[Γ] ⊢ t1 u ▷ t2 u
    ```
    '''
    def __init__(self, red : Rem_reduction, u : Term):
        '''
        Parameters -> Rule Terms:
        - `E[Γ] ⊢ t1 ▷ t2`
        - `u` -> `u`
        '''
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ t1 ▷ t2')

        self.Rem_type_check(u, Term, 'u')

        self.__red = red

        super().__init__(red.E, red.Gamma, 
            Apply(red.t1, u), Apply(red.t2, u)
        )

    def premises(self) -> str:
        return self.__red.conclusion()
    

@concrete_Rem_term
class Rem_red_apply_u(Rem_reduction):
    '''
    red-apply-u
    ```
        E[Γ] ⊢ u1 ▷ u2
        ---------------------------
        E[Γ] ⊢ t u1 ▷ t u2
    ```
    '''
    def __init__(self, red : Rem_reduction, t : Term):
        '''
        Parameters -> Rule Terms:
        - `E[Γ] ⊢ u1 ▷ u2`
        - `t` -> `t`
        '''
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ u1 ▷ u2')

        self.Rem_type_check(t, Term, 't')

        self.__red = red

        super().__init__(red.E, red.Gamma, 
            Apply(t, red.t1), Apply(t, red.t2)
        )

    def premises(self) -> str:
        return self.__red.conclusion()
    

@concrete_Rem_term
class Rem_red_let_in_t(Rem_reduction):
    '''
    red-let-in-t
    ```
        E[Γ] ⊢ t1 ▷ t2
        -------------------------------------------
        E[Γ] ⊢ let x:=t1:T in u ▷ let x:=t2:T in u
    ```
    '''
    def __init__(self, red : Rem_reduction, T : Term, u : Term):
        '''
        Parameters -> Rule Terms:
        - `E[Γ] ⊢ t1 ▷ t2`
        - `T` -> `T` 
        - `u` -> `u`
        '''
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ t1 ▷ t2')

        self.Rem_type_check(T, Term, 'T')

        self.Rem_type_check(u, Term, 'u')

        self.__red = red

        super().__init__(red.E, red.Gamma, 
            Let_in(red.t1, T, u), Let_in(red.t2, T, u)
        )

    def premises(self) -> str:
        return self.__red.conclusion()
    


@concrete_Rem_term
class Rem_red_let_in_T(Rem_reduction):
    '''
    red-let-in-T
    ```
        E[Γ] ⊢ T1 ▷ T2
        -------------------------------------------
        E[Γ] ⊢ let x:=t:T1 in u ▷ let x:=t:T2 in u
    ```
    '''
    def __init__(self, red : Rem_reduction, t : Term, u : Term):
        '''
        Parameters -> Rule Terms:
        - `E[Γ] ⊢ T1 ▷ T2`
        - `t` -> `t` 
        - `u` -> `u`
        '''
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ T1 ▷ T2')

        self.Rem_type_check(t, Term, 't')

        self.Rem_type_check(u, Term, 'u')

        self.__red = red

        super().__init__(red.E, red.Gamma, 
            Let_in(t, red.t1, u), Let_in(t, red.t2, u)
        )

    def premises(self) -> str:
        return self.__red.conclusion()
    


@concrete_Rem_term
class Rem_red_let_in_u(Rem_reduction):
    '''
    red-let-in-u
    ```
        E[Γ] ⊢ u1 ▷ u2
        -------------------------------------------
        E[Γ] ⊢ let x:=t:T in u1 ▷ let x:=t:T in u2
    ```
    '''
    def __init__(self, red : Rem_reduction, t : Term, T : Term):
        '''
        Parameters -> Rule Terms:
        - `E[Γ] ⊢ u1 ▷ u2`
        - `t` -> `t` 
        - `T` -> `T`
        '''
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ u1 ▷ u2')

        self.Rem_type_check(t, Term, 't')

        self.Rem_type_check(T, Term, 'T')

        self.__red = red

        super().__init__(red.E, red.Gamma, 
            Let_in(t, T, red.t1), Let_in(t, T, red.t2)
        )

    def premises(self) -> str:
        return self.__red.conclusion()
    


#############################################################
# reduction sequence

@Rem_term
class Rem_red_seq(RemProof):
    '''
    red-seq
    ```
        E[Γ] ⊢ t ▷ ... ▷ u
    ```
    A sequence of reduction relation.
    '''
    def __init__(self, E : Environment, Gamma : Context, t : Term, u : Term):
        '''
        Parameters -> Rule Terms:
        - `E` -> `E`
        - `Gamma` -> `Γ`
        - `t` -> `t`
        - `u` -> `u`
        '''

        self.Rem_type_check(E, Environment, 'E')
        self.Rem_type_check(Gamma, Context, 'Γ')
        self.Rem_type_check(t, Term, 't')
        self.Rem_type_check(u, Term, 'u')

        self.__E = E
        self.__Gamma = Gamma
        self.__t = t
        self.__u = u
    
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
    def u(self) -> Term:
        return self.__u
    
    def conclusion(self) -> str:
        return f"{self.E}[{self.Gamma}] ⊢ {self.t} ▷ ... ▷ {self.u}"
    

@concrete_Rem_term
class Rem_red_seq_refl(Rem_red_seq):
    '''
    red-seq-refl
    ```
        WF(E)[Γ]
        --------------------
        E[Γ] ⊢ t ▷ ... ▷ t
    ```
    '''
    def __init__(self, wf : Rem_WF, t : Term):
        '''
        Parameters -> Rule Terms:
        - `wf` -> `WF(E)[Γ]`
        - `t` -> `t`
        '''
        self.Rem_type_check(wf, Rem_WF, 'WF(E)[Γ]')
        self.Rem_type_check(t, Term, 't')

        self.__wf = wf
        super().__init__(wf.E, wf.Gamma, t, t)

    def premises(self) -> str:
        return self.__wf.conclusion()
    

@concrete_Rem_term
class Rem_red_seq_trans(Rem_red_seq):
    '''
    red-seq-trans
    ```
        E[Γ] ⊢ t1 ▷ ... ▷ t2
        E[Γ] ⊢ t2 ▷ t3
        --------------------
        E[Γ] ⊢ t1 ▷ ... ▷ t3
    ```
    '''
    def __init__(self, red_seq : Rem_red_seq, red : Rem_reduction):
        '''
        Parameters -> Rule Terms:
        - `red_seq` -> `E[Γ] ⊢ t1 ▷ ... ▷ t2`
        - `red` -> `E[Γ] ⊢ t2 ▷ t3`
        '''
        self.Rem_type_check(red_seq, Rem_red_seq, 'E[Γ] ⊢ t1 ▷ ... ▷ t2')
        self.Rem_type_check(red, Rem_reduction, 'E[Γ] ⊢ t2 ▷ t3')

        # consistent `t2`
        self.Rem_consistency_check(red_seq.u, red.t1, "t2")

        self.__red_seq = red_seq
        self.__red = red
        super().__init__(red_seq.E, red_seq.Gamma, red_seq.t, red.t2)

    def premises(self) -> str:
        res = self.__red_seq.conclusion() + "\n"
        res += self.__red.conclusion() + "\n"
        return res
    


@concrete_Rem_term
class Rem_convertible(RemProof):
    '''
    βδιζη-convertible.
    ```
        E[Γ] ⊢ t1 ▷ ... ▷ u1
        E[Γ] ⊢ t2 ▷ ... ▷ u2
        u1 ~α u2 or E[Γ] ⊢ u1 =η u2 or E[Γ] ⊢ u2 =η u1
        ----------------------------------
        E[Γ] ⊢ t1 =βδιζη t2
    ```
    '''

    def __init__(self, red_seq1 : Rem_red_seq, red_seq2 : Rem_red_seq, u_eq_proof : None | Rem_eta_conversion):
        '''
        Parameters -> Rule Terms:
        - `red1` -> `E[Γ] ⊢ t1 ▷ ... ▷ u1`
        - `red2` -> `E[Γ] ⊢ t2 ▷ ... ▷ u2`
        - `u_eq_proof` :
            - `None`: proof by alpha-conversion
            - `Rem_eta_conversion` : proof by eta-conversion (automatically detect `u1` `u2`)
        '''

        self.Rem_type_check(red_seq1, Rem_red_seq, 'E[Γ] ⊢ t1 ▷ ... ▷ u1')

        self.Rem_type_check(red_seq2, Rem_red_seq, 'E[Γ] ⊢ t2 ▷ ... ▷ u2')

        self.Rem_type_check(u_eq_proof, (type(None), Rem_eta_conversion), 'u1 ~α u2 or u1 ~η u2 or u2 ~η u1')

        # consistent `E`
        self.Rem_consistency_check(red_seq1.E, red_seq2.E, 'E')
        
        # consistent `Γ`
        self.Rem_consistency_check(red_seq1.Gamma, red_seq2.Gamma, 'Γ')

        # branch : proof by alpha-conversion
        if u_eq_proof is None:
            self.Rem_other_check(
                red_seq1.u.alpha_convertible(red_seq2.u),
                f"proposed to proof by alpha-conversion, but '{red_seq1.u}' and '{red_seq2.u}' are not alpha-convertible."
            )
            
        # branch : proof by eta-conversion
        else:
            assert isinstance(u_eq_proof, Rem_eta_conversion)

            # consistent `E`
            self.Rem_consistency_check(u_eq_proof.E, red_seq1.E, 'E')
            
            # consistent `Γ`
            self.Rem_consistency_check(u_eq_proof.Gamma, red_seq1.Gamma, 'Γ')

            self.Rem_other_check(
                ((red_seq1.u == u_eq_proof.t and red_seq2.u == u_eq_proof.lam) or (red_seq1.u == u_eq_proof.lam and red_seq2.u == u_eq_proof.t)),
                f"Inconsistent eta-conversion proof : {u_eq_proof}."
            )

            
        self.__red_seq1 = red_seq1
        self.__red_seq2 = red_seq2
        self.__u_eq_proof = u_eq_proof


    @property
    def E(self) -> Environment:
        return self.__red_seq1.E

    @property
    def Gamma(self) -> Context:
        return self.__red_seq1.Gamma

    @property
    def t1(self) -> Term:
        return self.__red_seq1.t

    @property
    def t2(self) -> Term:
        return self.__red_seq2.t
    
    def premises(self) -> str:
        res = self.__red_seq1.conclusion() + "\n"
        res += self.__red_seq2.conclusion() + "\n"
        if self.__u_eq_proof is not None:
            res += self.__u_eq_proof.conclusion() + "\n"
        return res
    
    def conclusion(self) -> str:
        return f"{self.E}{self.Gamma} ⊢ {self.t1} =βδιζη {self.t2}"


##########################################################################
# Subtyping conversion.
###

@Rem_term
class Rem_subtyping(RemProof):
    '''
    subtype
    ```
        E[Γ] ⊢ t1 ≤βδιζη t2
    ```
    '''

    def __init__(self, E : Environment, Gamma : Context, t1 : Term, t2 : Term):
        '''
        Parameters -> Rule Terms:
        - `E` -> `E`
        - `Gamma` -> `Γ`
        - `t1` -> `t1`
        - `t2` -> `t2`
        '''

        self.Rem_type_check(E, Environment, 'E')
        self.Rem_type_check(Gamma, Context, 'Γ')
        self.Rem_type_check(t1, Term, 't1')
        self.Rem_type_check(t2, Term, 't2')
        self.__E = E
        self.__Gamma = Gamma
        self.__t1 = t1
        self.__t2 = t2

    @property
    def E(self) -> Environment:
        return self.__E
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma
    
    @property
    def t1(self) -> Term:
        return self.__t1
    
    @property
    def t2(self) -> Term:
        return self.__t2
    
    def conclusion(self) -> str:
        return f"{self.E}{self.Gamma} ⊢ {self.t1} ≤βδιζη {self.t2}"

@Rem_term
class Rem_subtyping_trans(Rem_subtyping):
    '''
    subtype-trans
    ```
        E[Γ] ⊢ t1 ≤βδιζη t2
        E[Γ] ⊢ t2 ≤βδιζη t3
        -------------------
        E[Γ] ⊢ t1 ≤βδιζη t3
    ```
    '''
    def __init__(self, subtype1 : Rem_subtyping, subtype2 : Rem_subtyping):
        '''
        Parameters -> Rule Terms:
        - `subtype1` -> `E[Γ] ⊢ t1 ≤βδιζη t2`
        - `subtype2` -> `E[Γ] ⊢ t2 ≤βδιζη t3`
        '''

        self.Rem_type_check(subtype1, Rem_subtyping, 'E[Γ] ⊢ t1 ≤βδιζη t2')

        self.Rem_type_check(subtype2, Rem_subtyping, 'E[Γ] ⊢ t2 ≤βδιζη t3')

        # consistent `E`
        self.Rem_consistency_check(subtype1.E, subtype2.E, 'E')
        
        # consistent `Γ`
        self.Rem_consistency_check(subtype1.Gamma, subtype2.Gamma, 'Γ')
        
        # consistent `t2`
        self.Rem_consistency_check(subtype1.t2, subtype2.t1, 't2')
        
        self.__subtype1 = subtype1
        self.__subtype2 = subtype2

        # the conclusion
        super().__init__(subtype1.E, subtype1.Gamma, subtype1.t1, subtype2.t2)

    def premises(self) -> str:
        res = self.__subtype1.conclusion() + "\n"
        res = self.__subtype2.conclusion() + "\n"
        return res


@concrete_Rem_term
class Rem_subtyping_convert(Rem_subtyping):
    '''
    subtype-convert
    ```
        E[Γ] ⊢ t1 =βδιζη t2
        ---------------------
        E[Γ] ⊢ t1 ≤βδιζη t2
    ```
    '''
    def __init__(self, convert : Rem_convertible):
        '''
        Parameters -> Rule Terms:
        - `convert` -> `E[Γ] ⊢ t1 =βδιζη t2`
        '''

        self.Rem_type_check(convert, Rem_convertible, 'E[Γ] ⊢ t1 =βδιζη t2')
        
        self.__convert = convert

        # the conclusion
        super().__init__(convert.E, convert.Gamma, convert.t1, convert.t2)

    def premises(self) -> str:
        return self.__convert.conclusion() + "\n"
    
    
@concrete_Rem_term
class Rem_subtyping_universe(Rem_subtyping):
    '''
    subtype-universe
    ```
        i ≤ j
        -----------------------------
        E[Γ] ⊢ Type(i) ≤βδιζη Type(j)
    ```
    '''
    def __init__(self, E : Environment, Gamma : Context, i : int, j : int):
        '''
        Parameters -> Rule Terms:
        - `i` -> `i`
        - `j` -> `j`
        '''
        
        self.Rem_type_check(i, int, 'i')
        self.Rem_type_check(j, int, 'j')
        self.Rem_other_check(0 < i <= j, f"The universe number condition 0 < i <= j is not satisfied for i = {i} and j = {j}.")
        
        self.__i = i
        self.__j = j

        # the conclusion
        super().__init__(E, Gamma, Type_i(i), Type_i(j))

    def premises(self) -> str:
        return f"{self.__i} ≤ {self.__j}"
        

@concrete_Rem_term
class Rem_subtyping_Set(Rem_subtyping):
    '''
    subtype-Set
    ```
        --------------------------
        E[Γ] ⊢ Set ≤βδιζη Type(i)
    ```
    '''
    def __init__(self, E : Environment, Gamma : Context, i : int):
        '''
        Parameters -> Rule Terms:
        - `E` -> `E`
        - `Gamma` -> `Γ`
        - `i` -> `i`
        '''

        # proof check
        self.Rem_type_check(i, int, 'i')
        self.Rem_other_check(0 < i, f"Invalid universe number: {i}.")
        
        self.__i = i

        # the conclusion
        super().__init__(E, Gamma, Set(), Type_i())

    def premises(self) -> str:
        return ""
    

@concrete_Rem_term
class Rem_subtyping_Prop(Rem_subtyping):
    '''
    subtype-Prop
    ```
        -------------------------
        E[Γ] ⊢ Prop ≤βδιζη Set
    ```
    '''
    def __init__(self, E : Environment, Gamma : Context):
        '''
        Parameters -> Rule Terms:
        - `E` -> `E`
        - `Gamma` -> `Γ`
        '''

        # the conclusion
        super().__init__(E, Gamma, Prop(), Set())

    def premises(self) -> str:
        return ""
    
@concrete_Rem_term
class Rem_subtyping_lam(Rem_subtyping):
    '''
    subtype-lam
    ```
        E[Γ] ⊢ T =βδιζη U
        E[Γ::(x:T)] ⊢ T' ≤βδιζη U'
        --------------------------------
        E[Γ] ⊢ ∀x:T, T' ≤βδιζη ∀x:U, U'
    ```
    '''
    def __init__(self, convert : Rem_convertible, subtype : Rem_subtyping):
        '''
        Parameters -> Rule Terms:
        - `convert` -> `E[Γ] ⊢ T =βδιζη U`
        - `subtype` -> `E[Γ::(x:T)] ⊢ T' ≤βδιζη U'`
        '''

        self.Rem_type_check(convert, Rem_convertible, 'E[Γ] ⊢ T =βδιζη U')

        self.Rem_type_check(subtype, Rem_subtyping, "E[Γ::(x:T)] ⊢ T' ≤βδιζη U'")

        # consistent `E`
        self.Rem_consistency_check(convert.E, subtype.E, 'E')

        # break `Γ::(x:T)`
        Gamma_pre, dec = subtype.Gamma.pop()

        # consistent `Γ`
        self.Rem_consistency_check(convert.Gamma, Gamma_pre, 'Γ')
        
        # consistent `T`
        self.Rem_consistency_check(convert.t1, dec.T, 'T')
        
        self.__convert = convert
        self.__subtype = subtype

        # the conclusion
        t1 = Prod(dec.x, convert.t1, subtype.t1)
        t2 = Prod(dec.x, convert.t2, subtype.t2)
        super().__init__(convert.E, convert.Gamma, t1, t2)

    def premises(self) -> str:
        res = self.__convert.conclusion() + "\n"
        res += self.__subtype.conclusion() + "\n"
        return res
    
# for CIC: there is still a subtyping rule for inductive types





##########################################
# the Convertible proof (with subtyping) #
##########################################

@concrete_Rem_term
class Rem_Conv(Rem_WT):
    '''
    Conv
    ```
        E[Γ] ⊢ U : s
        E[Γ] ⊢ t : T
        E[Γ] ⊢ T ≤βδιζη U
        ------------------
        E[Γ] ⊢ t : U
    ```
    '''
    def __init__(self, wt_U : Rem_WT, wt_t : Rem_WT, subtype : Rem_subtyping):
        '''
        Parameters -> Rule Terms:
        - `wt_U` -> `E[Γ] ⊢ U : s`
        - `wt_t` -> `E[Γ] ⊢ t : T`
        - `subtype` -> `E[Γ] ⊢ T ≤βδιζη U`
        '''

        self.Rem_type_check(wt_U, Rem_WT, 'E[Γ] ⊢ U : s')

        self.Rem_type_check(wt_t, Rem_WT, 'E[Γ] ⊢ t : T')

        self.Rem_type_check(subtype, Rem_subtyping, 'E[Γ] ⊢ T ≤βδιζη U')

        # consistent `E`
        self.Rem_consistency_check(wt_U.E, wt_t.E, 'E')
        self.Rem_consistency_check(wt_U.E, subtype.E, 'E')
        
        # consistent `Γ`
        self.Rem_consistency_check(wt_U.Gamma, wt_t.Gamma, 'Γ')
        self.Rem_consistency_check(wt_U.Gamma, subtype.Gamma, 'Γ')
        
        # consistent `U`
        self.Rem_consistency_check(wt_U.t, subtype.t2, 'U')
        
        # consistent `T`
        self.Rem_consistency_check(wt_t.T, subtype.t1, 'T')
        
        self.__wt_U = wt_U
        self.__wt_t = wt_t
        self.__subtype = subtype

        # the conclusion
        super().__init__(wt_U.E, wt_U.Gamma, wt_t.t, wt_U.t)

    def premises(self) -> str:
        res = self.__wt_U.conclusion() + "\n"
        res += self.__wt_t.conclusion() + "\n"
        res += self.__subtype.conclusion() + "\n"
        return res


