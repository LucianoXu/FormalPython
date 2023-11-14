
from __future__ import annotations

from typing import List, Tuple
from ..rem_error import REM_META_Error, REM_CONSTRUCTION_Error
from ..rem import RemSort, RemFun, RemTerm

class ProofSort(RemSort):
    '''
    The sort of proofs.
    Special printing will be applied.
    '''
    pass


class ProofTerm(RemTerm[ProofSort, "ProofTerm"]):    
    pass
    

class ProofFun(RemFun[ProofSort, ProofTerm]):
    term_type = ProofTerm
