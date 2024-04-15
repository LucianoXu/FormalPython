
from Rem import *

from ..core import *
from .type_calc import well_typed_pf
from .var_dec import local_assum, local_def, global_assum, global_def


class RemCoC_WT(REMTheory):
    '''
    Equip the CoC theory with algorithms.
    '''
    def __init__(self, coc : RemCoC):
        super().__init__()

        REM_type_check(coc, RemCoC)

        self.fuse_append(coc)

        self.coc = coc

        class Rem_WT_calc(coc.Rem_WT):
            def __new__(cls, wf : coc.Rem_WF, term : coc.Term):
                return well_typed_pf(self.coc, wf, term)
        self.Rem_WT_calc = Rem_WT_calc

        class LocalAssum(coc.LocalTyping):
            def __new__(cls, wf : coc.Rem_WF, x : coc.Var, T : coc.Term):
                return local_assum(self.coc, wf, x, T)
        self.LocalAssum = LocalAssum

        class LocalDef(coc.LocalDef):
            def __new__(cls, wf : coc.Rem_WF, x : coc.Var, t : coc.Term):
                return local_def(self.coc, wf, x, t)
        self.LocalDef = LocalDef

        class GlobalAssum(coc.GlobalTyping):
            def __new__(cls, wf : coc.Rem_WF, c : coc.Const, T : coc.Term):
                return global_assum(self.coc, wf, c, T)
        self.GlobalAssum = GlobalAssum
        
        class GlobalDef(coc.GlobalDef):
            def __new__(cls, wf : coc.Rem_WF, c : coc.Const, t : coc.Term):
                return global_def(self.coc, wf, c, t)
        self.GlobalDef = GlobalDef


        # build the parser
        self.build_parser("term")