'''

This is the automation for conversion rules.

'''

from ..core import *
from .normal import *
from .var_dec import local_assum

# TODO #5
def conv_pf(wf : Rem_WF, t1 : Term, t2 : Term) -> Rem_convertible:
    '''
    auto-convertibility-check
    ```
        E[Γ] ⊢ t1 =βδιζη t2
        ----------------------------
        E[Γ] ⊢ t1 =βδιζη t2 (automatic)
    ```
    Raise an error when subtyping relation does not hold.
    '''
    red_seq1 = Rem_red_seq_alg(wf, t1)
    red_seq2 = Rem_red_seq_alg(wf, t2)

    wt_u1 = well_typed_pf(wf, red_seq1.u)
    wt_u2 = well_typed_pf(wf, red_seq2.u)

    # check convertibility
    try:
        # try alpha-conversion
        return Rem_convertible(red_seq1, red_seq2, None)
    except REM_Error:
        pass

    raise REM_Error(f"The terms '{t1}' and '{t2}' are not convertible.")



def subtype_pf(wf : Rem_WF, t1 : Term, t2 : Term) -> Rem_subtyping:
    '''
    auto-subtyping-check
    ```
        E[Γ] ⊢ t1 ≤βδιζη t2
        ----------------------------
        E[Γ] ⊢ t1 ≤βδιζη t2 (automatic)
    ```
    Raise an error when subtyping relation does not hold.
    '''
    raise NotImplementedError()

    

    
