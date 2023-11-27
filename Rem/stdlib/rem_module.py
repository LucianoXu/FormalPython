
from ..rem import *


#####################################################################
# ModuleTerm and Functors

class ModuleSort(RemSort):
    '''
    The sort of modules.
    '''
    pass

class ModuleTerm(RemTerm[ModuleSort, "ModuleTerm"]):
    def __init__(self, fun: RemFun, *paras: RemTerm):
        RemTerm.__init__(self, fun, *paras)


    ###########################################################
    # drawing by Graphviz

    def vlayout(self, dot : Digraph, id : str, title : str):
        dot.node(id, title,
            shape = "box", style="filled", fillcolor = "lightblue",
            fontname = "Consolas",
            labeljust="l")
        
    def vlayout_focus(self, dot : Digraph, id : str, title : str):
        dot.node(id, title,
            shape = "box", 
            style="filled, bold", color = "red", fillcolor = "lightblue",
            fontname = "Consolas",
            labeljust="l")        
    
class ModuleFun(RemFun[ModuleSort, ModuleTerm]):
    term_type = ModuleTerm

