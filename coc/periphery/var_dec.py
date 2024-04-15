
from .type_calc import *

def local_assum(coc : RemCoC, wf : Rem_WF, x : Var, T : Term) -> Rem_WF:

    # E[Γ] ⊢ T : s
    wt = well_typed_pf(coc, wf, T)

    # s ∈ S
    s_sort = Rem_IsSort(wt.T)

    # x ∉ Γ
    x_notin_Gamma = Rem_Cont_Not_Contain_Var(x, wt.Gamma)

    return Rem_W_Local_Assum(wt, s_sort, x_notin_Gamma)

def local_def(coc : RemCoC, wf : Rem_WF, x : Var, t : Term) -> Rem_WF:
    '''
    Here we need to consider conversion rules. (and let the user decide the type).
    '''

    # E[Γ] ⊢ t : T
    wt = well_typed_pf(coc, wf, t)

    # x ∉ Γ
    x_notin_Gamma = Rem_Cont_Not_Contain_Var(x, wt.Gamma)

    return Rem_W_Local_Def(wt, x_notin_Gamma)

def global_assum(coc : RemCoC, wf : Rem_WF, c : Const, T : Term) -> Rem_WF:

    # E[] ⊢ T : s
    wt = well_typed_pf(coc, wf, T)

    # s ∈ S
    s_sort = Rem_IsSort(wt.T)

    # c ∉ E
    c_notin_Env = Rem_Env_Not_Contain_Const(c, wt.E)

    return Rem_W_Global_Assum(wt, s_sort, c_notin_Env)

def global_def(coc : RemCoC, wf : Rem_WF, c : Const, t : Term):
    '''
    Here we need to consider conversion rules. (and let the user decide the type).
    '''

    # E[] ⊢ t : T
    wt = well_typed_pf(coc, wf, t)

    # c ∉ E
    c_notin_Env = Rem_Env_Not_Contain_Const(c, wt.E)

    return Rem_W_Global_Def(wt, c_notin_Env)

