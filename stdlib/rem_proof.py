
raise NotImplementedError()
from ..rem import RemTerm

class RemProof(RemTerm):
    '''
    Rem-proof
    ```
    _
    ```
    The proof objects in REM.
    '''
    Rem_term_name   = 'Rem-proof'
    Rem_term_def    = '_'
    term_order      = 1

    def premises(self) -> str:
        raise NotImplementedError()
    
    def conclusion(self) -> str:
        raise NotImplementedError()
    
    def full_proof(self) -> str:
        space_len = len(self.Rem_term_name) + 3

        # indent, premise
        res = " " * space_len + self.premises()
        if res[-1] == "\n":
            res = res[:-1]
        res = res.replace("\n", "\n" + " " * space_len)
        res += "\n"

        # line
        res += f"({self.Rem_term_name}) " + "-"*40 + "\n" 

        # indent conclusion
        res += " " * space_len + self.conclusion() 
        return res
    
    def __str__(self) -> str:
        return self.conclusion()

