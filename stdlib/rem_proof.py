
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


class ProofFun(RemFun):
    def __init__(self, name : str, para_sorts : Tuple[RemSort], domain_sort : ProofSort, symbol : str | None = None):

        if not isinstance(domain_sort, ProofSort):
            raise REM_META_Error(f"({name}): The domain sort '{domain_sort}' is not an instance of class ProofSort.")
        
        super().__init__(name, para_sorts, domain_sort, symbol)


    def __call__(self, *paras : RemTerm, **kwparas) -> RemTerm:
        '''
        Create a `RemTerm` instance with the parameters.
        '''
        if len(paras) != self.arity:
            raise REM_CONSTRUCTION_Error(f"({self.name}): Invalid argument number. The function arity is {self.arity} but {len(paras)} arguments are provided.")
        
        for i in range(self.arity):                
            self.type_check(paras[i], self.para_sorts[i], self.__para_doc[i])
            
        self.extra_check(*paras, **kwparas)

        term = ProofTerm(self, *paras, **kwparas)

        self.modify(term, *paras, **kwparas)

        return term


class ProofTerm(RemTerm):    
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
