
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
    def premises(self) -> str:
        raise NotImplementedError()
    
    def conclusion(self) -> str:
        raise NotImplementedError()
    
    def full_proof(self) -> str:
        space_len = len(self.sort.name) + 3

        # indent, premise
        res = " " * space_len + self.premises()
        if res[-1] == "\n":
            res = res[:-1]
        res = res.replace("\n", "\n" + " " * space_len)
        res += "\n"

        # line
        res += f"({self.sort.name}) " + "-"*40 + "\n" 

        # indent conclusion
        res += " " * space_len + self.conclusion() 
        return res
    
    def __str__(self) -> str:
        return self.conclusion()
    

class ProofFun(RemFun[ProofSort, ProofTerm]):
    sort_type = ProofSort
    term_type = ProofTerm
