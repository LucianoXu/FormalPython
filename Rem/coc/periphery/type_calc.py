'''

This is the automation for well-typed proofs.

'''

from ..core import *

def local_assum(wf : Rem_WF, x : Var, T : Term) -> Rem_WF:

    # E[Γ] ⊢ T : s
    wt = well_typed_pf(wf, T)

    # s ∈ S
    s_sort = Rem_IsSort(wt.T)

    # x ∉ Γ
    x_notin_Gamma = Rem_Cont_Not_Contain_Var(x, wt.Gamma)

    return Rem_W_Local_Assum(wt, s_sort, x_notin_Gamma)

def local_def(wf : Rem_WF, x : Var, t : Term) -> Rem_WF:
    '''
    Here we need to consider conversion rules. (and let the user decide the type).
    '''

    # E[Γ] ⊢ t : T
    wt = well_typed_pf(wf, t)

    # x ∉ Γ
    x_notin_Gamma = Rem_Cont_Not_Contain_Var(x, wt.Gamma)

    return Rem_W_Local_Def(wt, x_notin_Gamma)

def global_assum(wf : Rem_WF, c : Const, T : Term) -> Rem_WF:

    # E[] ⊢ T : s
    wt = well_typed_pf(wf, T)

    # s ∈ S
    s_sort = Rem_IsSort(wt.T)

    # c ∉ E
    c_notin_Env = Rem_Env_Not_Contain_Const(c, wt.E)

    return Rem_W_Global_Assum(wt, s_sort, c_notin_Env)

def global_def(wf : Rem_WF, c : Const, t : Term):
    '''
    Here we need to consider conversion rules. (and let the user decide the type).
    '''

    # E[] ⊢ t : T
    wt = well_typed_pf(wf, t)

    # c ∉ E
    c_notin_Env = Rem_Env_Not_Contain_Const(c, wt.E)

    return Rem_W_Global_Def(wt, c_notin_Env)



def well_typed_pf(wf : Rem_WF, term : Term) -> Rem_WT:
    '''
    auto-well-typed
    ```
        WF(E)[Γ] ⊢ t : T
        ----------------------------
        WF(E)[Γ] ⊢ t : T (automatic)
    ```
    '''
    # Ax-SProp
    if isinstance(term, SProp):
        return Rem_Ax_SProp(wf)
    
    # Ax-Prop
    elif isinstance(term, Prop):
        return Rem_Ax_Prop(wf)
    
    # Ax-Set
    elif isinstance(term, Set):
        return Rem_Ax_Set(wf)
    
    # Ax-Type
    elif isinstance(term, Type_i):
        return Rem_Ax_Type(wf, term.i)
    
    # Ax-Var
    elif isinstance(term, Var):
        T = wf.Gamma.get_typing(term)
        REM_other_check(T is not None, f"The variable '{term}' is not defined in the context.")

        x_dec_in_Gamma = Rem_Cont_Contain_Typing(LocalTyping(term, T), wf.Gamma)
        return Rem_Var(wf, x_dec_in_Gamma)
    
    # Ax-Const
    elif isinstance(term, Const):
        T = wf.E.get_typing(term)
        REM_other_check(T is not None, f"The constant '{term}' is not defined in the environment.")

        c_dec_in_E = Rem_Env_Contain_Typing(GlobalTyping(term, T), wf.E)
        return Rem_Const(wf, c_dec_in_E)
    
    elif isinstance(term, Prod):
        # E[Γ] ⊢ T : s
        wt = well_typed_pf(wf, term.T)
        # s ∈ S
        s_sort = Rem_IsSort(wt.T)
        # x ∉ Γ
        x_notin_Gamma = Rem_Cont_Not_Contain_Var(term.x, wt.Gamma)
        # WF(E)[Γ::(x:T)]
        wf_inner = Rem_W_Local_Assum(wt, s_sort, x_notin_Gamma)
        # E[Γ::(x:T)] ⊢ U : ?
        wt_inner = well_typed_pf(wf_inner, term.U)
        
        if isinstance(wt_inner.T, SProp):
            return Rem_Prod_SProp(wt, s_sort, wt_inner)
        elif isinstance(wt_inner.T, Prop):
            return Rem_Prod_Prop(wt, s_sort, wt_inner)
        elif isinstance(wt_inner.T, Set):
            return Rem_Prod_Set(wt, s_sort, wt_inner)
        elif isinstance(wt_inner.T, Type_i):
            return Rem_Prod_Type(wt, s_sort, wt_inner)
        else:
            raise Exception()
        
    # Lam
    elif isinstance(term, Abstract):
        # E[Γ] ⊢ T : s
        wt = well_typed_pf(wf, term.T)
        # s ∈ S
        s_sort = Rem_IsSort(wt.T)
        # x ∉ Γ
        x_notin_Gamma = Rem_Cont_Not_Contain_Var(term.x, wt.Gamma)
        # WF(E)[Γ::(x:T)]
        wf_inner = Rem_W_Local_Assum(wt, s_sort, x_notin_Gamma)
        # E[Γ::(x:T)] ⊢ t : U
        wt_inner = well_typed_pf(wf_inner, term.u)

        # E[Γ] ⊢ ∀x:T, U : s
        prod = Prod(term.x, term.T, wt_inner.T)
        wt_outer = well_typed_pf(wf, prod)

        return Rem_Lam(wt_outer, wt_inner)
    
    # App
    elif isinstance(term, Apply):
        wt_t = well_typed_pf(wf, term.t)
        wt_u = well_typed_pf(wf, term.u)
        return Rem_App(wt_t, wt_u)
    
    # Let
    elif isinstance(term, Let_in):
        # E[Γ] ⊢ t : T
        wt_outer = well_typed_pf(wf, term.t)

        # E[Γ] ⊢ t : T
        wt = well_typed_pf(wf, term.t)
        # x ∉ Γ
        x_notin_Gamma = Rem_Cont_Not_Contain_Var(term.x, wt.Gamma)
        # WF(E)[Γ::(x:=t:T)]
        wf_inner = Rem_W_Local_Def(wt, x_notin_Gamma)
        # E[Γ::(x:=t:T)] ⊢ u : U
        wt_inner = well_typed_pf(wf_inner, term.u)
        
        return Rem_Let(wt_outer, wt_inner)
    
    else:
        raise Exception()

