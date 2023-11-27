from __future__ import annotations

from ..rem import *

from graphviz import unflatten


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

    def rem_obj(self) -> set[RemObject]:
        '''
        Return the direct Rem objects. (not recursive in submodule)
        '''
        res = set()
        for attr_id in vars(self):
            attr = getattr(self, attr_id)
            if isinstance(attr, RemObject) and attr is not self._fun:
                res.add(attr)
        return res


    ###########################################################
    # drawing by Graphviz

    def layout(self, dot : Digraph, sort_network: Network[RemSort]):
        '''
        sort_network is necessary because of the subtyping relation.
        '''

        dot.node(str(id(self)), str(self),
            shape = "folder", style="filled", fillcolor = "lightblue",
            fontname = "Consolas",
            labeljust="l")
        
        objs = self.rem_obj()

        for obj in objs:
            # the edge for module inclusion
            dot.edge(str(id(obj)), str(id(self)), style = "dashed",
                     label=None, arrowsize = "0.5", color="#00000050")

            if isinstance(obj, RemSort):
                sort_network.absorb(Network(obj.downstream_nodes))

            elif isinstance(obj, ModuleTerm):
                obj.layout(dot, sort_network)

            elif isinstance(obj, RemFun) or isinstance(obj, RemTerm):
                obj.vlayout(dot, str(id(obj)), str(obj))

    def module_draw(self, output : str | None = None) -> Digraph:
        dot = Digraph()
        sort_nw = Network(set())

        self.layout(dot, sort_nw)

        # layout the sort_nw for only once to avoid multiple edges
        sort_nw.layout(dot)

        if output is not None:
            dot.render(output, cleanup=True, engine='dot')

        return dot


    
class ModuleFun(RemFun[ModuleSort, ModuleTerm]):
    term_type = ModuleTerm

    def vlayout(self, dot: Digraph, id : str, title : str):
        # visual distinction between terminal/nonterminals
        if self.terminal:
            dot.node(id, title,
                shape = "note", style="filled", fillcolor = "lightblue",
                fontname = "Consolas",
                labeljust="l")
        else:
            dot.node(id, title,
                shape = "cds", style="filled", fillcolor = "lightblue",
                fontname = "Consolas",
                labeljust="l")
