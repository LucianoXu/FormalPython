'''

This is the automation for well-typed proofs.

'''

from ..core import *

def well_typed_pf(coc : RemCoC, wf : Rem_WF, term : Term) -> Rem_WT:
    '''
    auto-well-typed
    ```
        WF(E)[Γ] ⊢ t : T
        ----------------------------
        WF(E)[Γ] ⊢ t : T (automatic)
    ```
    '''
    # Ax-SProp
    if isinstance(term, coc.SProp):
        return coc.Rem_Ax_SProp(wf)
    
    # Ax-Prop
    elif isinstance(term, coc.Prop):
        return coc.Rem_Ax_Prop(wf)
    
    # Ax-Set
    elif isinstance(term, coc.Set):
        return coc.Rem_Ax_Set(wf)
    
    # Ax-Type
    elif isinstance(term, coc.Type_i):
        return coc.Rem_Ax_Type(wf, term.i)
    
    # Ax-Var
    elif isinstance(term, coc.Var):
        dec = wf.Gamma[term]
        REM_other_check(dec is not None, f"The variable '{term}' is not defined in the context.")

        assert dec is not None
        x_dec_in_Gamma = coc.Rem_Cont_Contain_Typing(coc.LocalTyping(term, dec.T), wf.Gamma)
        return coc.Rem_Var(wf, x_dec_in_Gamma)
    
    # Ax-Const
    elif isinstance(term, coc.Const):
        dec = wf.E[term]
        REM_other_check(dec is not None, f"The constant '{term}' is not defined in the environment.")

        assert dec is not None
        c_dec_in_E = coc.Rem_Env_Contain_Typing(coc.GlobalTyping(term, dec.T), wf.E)
        return coc.Rem_Const(wf, c_dec_in_E)
    
    elif isinstance(term, coc.Prod):
        # E[Γ] ⊢ T : s
        wt = well_typed_pf(coc, wf, term.T)
        # s ∈ S
        s_sort = coc.Rem_IsSort(wt.T)
        # x ∉ Γ
        x_notin_Gamma = coc.Rem_Cont_Not_Contain_Var(term.x, wt.Gamma)
        # WF(E)[Γ::(x:T)]
        wf_inner = coc.Rem_W_Local_Assum(wt, s_sort, x_notin_Gamma)
        # E[Γ::(x:T)] ⊢ U : ?
        wt_inner = well_typed_pf(coc, wf_inner, term.U)
        
        if isinstance(wt_inner.T, coc.SProp):
            return coc.Rem_Prod_SProp(wt, s_sort, wt_inner)
        elif isinstance(wt_inner.T, coc.Prop):
            return coc.Rem_Prod_Prop(wt, s_sort, wt_inner)
        elif isinstance(wt_inner.T, coc.Set):
            return coc.Rem_Prod_Set(wt, s_sort, wt_inner)
        elif isinstance(wt_inner.T, coc.Type_i):
            return coc.Rem_Prod_Type(wt, s_sort, wt_inner)
        else:
            raise Exception()
        
    # Lam
    elif isinstance(term, coc.Abstract):
        # E[Γ] ⊢ T : s
        wt = well_typed_pf(coc, wf, term.T)
        # s ∈ S
        s_sort = coc.Rem_IsSort(wt.T)
        # x ∉ Γ
        x_notin_Gamma = coc.Rem_Cont_Not_Contain_Var(term.x, wt.Gamma)
        # WF(E)[Γ::(x:T)]
        wf_inner = coc.Rem_W_Local_Assum(wt, s_sort, x_notin_Gamma)
        # E[Γ::(x:T)] ⊢ t : U
        wt_inner = well_typed_pf(coc, wf_inner, term.u)

        # E[Γ] ⊢ ∀x:T, U : s
        prod = coc.Prod(term.x, term.T, wt_inner.T)
        wt_outer = well_typed_pf(coc, wf, prod)

        return coc.Rem_Lam(wt_outer, wt_inner)
    
    # App
    elif isinstance(term, Apply):
        wt_t = well_typed_pf(coc, wf, term.t)
        wt_u = well_typed_pf(coc, wf, term.u)
        return Rem_App(wt_t, wt_u)
    
    # Let
    elif isinstance(term, Let_in):
        # E[Γ] ⊢ t : T
        wt_outer = well_typed_pf(coc, wf, term.t)

        # E[Γ] ⊢ t : T
        wt = well_typed_pf(coc, wf, term.t)
        # x ∉ Γ
        x_notin_Gamma = coc.Rem_Cont_Not_Contain_Var(term.x, wt.Gamma)
        # WF(E)[Γ::(x:=t:T)]
        wf_inner = coc.Rem_W_Local_Def(wt, x_notin_Gamma)
        # E[Γ::(x:=t:T)] ⊢ u : U
        wt_inner = well_typed_pf(coc, wf_inner, term.u)
        
        return coc.Rem_Let(wt_outer, wt_inner)
    
    else:
        raise Exception()

