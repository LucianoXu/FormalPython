'''

Calculate the normal form.

Note: the approach to prove subtyping through normal form can be largely improved.

'''

from ..core import *
from .type_calc import well_typed_pf
from .var_dec import local_def

@concrete_Rem_term
class Rem_red_seq_alg(Rem_red_seq):
    '''
    red-seq-alg
    ```
        E[Γ] ⊢ t ▷ ... ▷ u
        -------------------------------
        E[Γ] ⊢ t ▷ ... ▷ u (automatic)
    ```
    '''
    def __init__(self, wf : Rem_WF, t : Term):
        self.Rem_type_check(wf, Rem_WF, "WF(E)[Γ]")
        self.Rem_type_check(t, Term, "t")

        super().__init__(wf.E, wf.Gamma, t, normal_form(wf, t))

    def premises(self) -> str:
        return "(algorithm)"

def normal_form(wf : Rem_WF, t : Term) -> Term:
    '''
    Return the normal form of `t`.
    '''
    succ = True
    newt = t
    while succ:
        succ, newt = step_reduction(wf, newt)
    return newt

def step_reduction(wf : Rem_WF, t : Term) -> Tuple[bool, Term]:

    # delta
    if isinstance(t, Var):
        dec = wf.Gamma[t]
        if isinstance(dec, LocalDef):
            return (True, dec.t)
        else:
            return (False, t)
        
    # Delta
    elif isinstance(t, Const):
        dec = wf.E[t]
        if isinstance(dec, GlobalDef):
            return (True, dec.t)
        else:
            return (False, t)
        
    elif isinstance(t, Prod):
        
        succ, newT = step_reduction(wf, t.T)
        if succ:
            return (True, Prod(t.x, newT, t.U))
        succ, newU = step_reduction(wf, t.U)
        if succ:
            return (True, Prod(t.x, t.T, newU))
        
        return (False, t)
    
    elif isinstance(t, Abstract):

        succ, newT = step_reduction(wf, t.T)
        if succ:
            return (True, Abstract(t.x, newT, t.u))
        
        succ, newu = step_reduction(wf, t.u)
        if succ:
            return (True, Abstract(t.x, t.T, newu))
        
        return (False, t)

    elif isinstance(t, Apply):

        # beta
        if isinstance(t.t, Abstract):
            return (True, t.t.u.substitute(t.t.x, t.u))
        
        succ, newt = step_reduction(wf, t.t)
        if succ:
            return (True, Apply(newt, t.u))
        
        succ, newu = step_reduction(wf, t.u)
        if succ:
            return (True, Apply(t.t, newu))
        
        return (False, t)

    elif isinstance(t, Let_in):

        # check for Zeta-reduction
        # check `E[Γ] ⊢ u : U` and `E[Γ::(x:=u:U)] ⊢ t:T`
        try:
            wf_inner = local_def(wf, t.x, t.u)
            wt_inner = well_typed_pf(wf_inner, t.t)
            # consistent `U`
            dec = wf_inner.Gamma[t.x]
            assert dec is not None
            REM_other_check(dec.T == t.T, "")

            return (True, t.t.substitute(t.x, t.u))
        
        except REM_Error:
            pass


        succ, newt = step_reduction(wf, t.t)
        if succ:
            return (True, Let_in(t.x, newt, t.T, t.u))
        
        succ, newT = step_reduction(wf, t.T)
        if succ:
            return (True, Let_in(t.x, t.t, newT, t.u))
        
        succ, newu = step_reduction(wf, t.u)
        if succ:
            return (True, Let_in(t.x, t.t, t.T, newu))
        
        return (False, t)
    
    else:
        return (False, t)






