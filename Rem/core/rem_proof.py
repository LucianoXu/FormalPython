
from __future__ import annotations

from typing import List, Tuple

from graphviz import Digraph
from .rem_error import REM_META_Error, REM_CONSTRUCTION_Error
from .rem import RemSort, RemFun, RemTerm, RemVar, RemCons

class ProofSort(RemSort):
    '''
    The sort of proofs.
    Special printing will be applied.
    '''
    def vlayout(self, dot: Digraph, id : str, title : str):
        dot.node(id, title,
            shape = "ellipse", style="filled", fillcolor = "lightgreen",
            fontname = "Consolas",
            labeljust="l")


class ProofTerm(RemTerm):
    pass

class ProofVar(ProofTerm, RemVar):
    def vlayout(self, dot: Digraph, id: str, title: str):
        dot.node(id, title,
            shape = "circle", style="filled", fillcolor = "lightgreen",
            fontname = "Consolas",
            labeljust="l")

class ProofCons(ProofTerm, RemCons):    
    def vlayout(self, dot: Digraph, id : str, title : str):
        dot.node(id, title,
            shape = "box", style="filled", fillcolor = "lightgreen",
            fontname = "Consolas",
            labeljust="l")    

class ProofFun(RemFun):

    def vlayout(self, dot: Digraph, id : str, title : str):

        # visual distinction between terminal/nonterminals
        if self.terminal:
            dot.node(id, title,
                shape = "note", style="filled", fillcolor = "lightgreen",
                fontname = "Consolas",
                labeljust="l")
        else:
            dot.node(id, title,
                shape = "cds", style="filled", fillcolor = "lightgreen",
                fontname = "Consolas",
                labeljust="l")
