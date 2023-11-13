
from ..rem import *


#####################################################################
# ModuleTerm and Functors

class ModuleSort(RemSort):
    '''
    The sort of modules.
    '''
    pass

class ModuleTerm(RemTerm[ModuleSort, "ModuleTerm"], syn.ParserHost):
    def __init__(self, fun: RemFun, *paras: RemTerm):
        syn.ParserHost.__init__(self,None)
        RemTerm.__init__(self, fun, *paras)
        

    def __setattr__(self, __name: str, __value: Any) -> None:

        if isinstance(__value, RemSort) or isinstance(__value, RemFun) or isinstance(__value, ModuleTerm):
            # the attributes of `RemSort` class will be linked to the parser automatically
            self.parser_node.set_sub_node(__value.parser_node)

        return super().__setattr__(__name, __value)

    def __delattr__(self, __name: str) -> None:
        attr = self.__dict__[__name]
        if isinstance(attr, RemSort) or isinstance(attr, RemFun) or isinstance(attr, ModuleTerm):
            self.parser_node.del_sub_node(attr.parser_node)

        return super().__delattr__(__name)
    
class ModuleFun(RemFun[ModuleSort, ModuleTerm]):
    sort_type = ModuleSort
    term_type = ModuleTerm

