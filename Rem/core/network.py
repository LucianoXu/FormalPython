
from __future__ import annotations

from typing import Tuple, List, Generic, TypeVar

from graphviz import Digraph

T = TypeVar("T", bound = "NetworkNode[T]")

class Network(Generic[T]):
    def __init__(self, nodes : set[NetworkNode[T]]):
        self._nodes = nodes.copy()

    def add(self, node : NetworkNode[T]) -> None:
        self._nodes.add(node)

    def absorb(self, other : Network[T]) -> None:
        self._nodes |= other._nodes

    def union(self, other : Network[T]) -> Network[T]:
        return Network(self._nodes | other._nodes)

    @property
    def nodes(self) -> set[NetworkNode[T]]:
        return self._nodes
    
    def layout(self, dot : Digraph):
        '''
        layout all the nodes and edges of this network
        '''
        for node in self._nodes:
            node.vlayout(dot, str(hash(node)), str(node))
            for snode in node.super_nodes:
                if snode in self._nodes:
                    node.elayout(snode, dot)


    def draw(self, output : None | str = None) -> Digraph:
        dot = Digraph()

        self.layout(dot)

        if output:
            dot.render(output, cleanup=True)
            
        return dot


class NetworkNode(Generic[T]):
    '''
    The nodes of a network.
    '''

    def __init__(self, super_nodes : set[T]):

        self._super_nodes  : set[T] = set()
        self._sub_nodes    : set[T] = set()

        self._upstream_nodes : set[T]
        
        self.set_super_nodes(super_nodes)

    def connected_nw(self) -> Network[T]:
        '''
        Returns the network that contains all nodes that connected to this node.
        '''
        s = {self}

        while True:
            updated = False
            for e in s:
                new_s = s | e.downstream_nodes | e.upstream_nodes
                if new_s != s:
                    s = new_s
                    updated = True
                    break
            if not updated:
                break

        return Network(s)   # type: ignore


    def __hash__(self) -> int:
        return id(self)
    
    def vlayout(self, dot : Digraph, id : str, title : str):
        dot.node(id, title,
            shape = "box", style="filled", fillcolor = "gray",
            fontname = "Consolas",
            labeljust="l")
        
    def elayout(self, super_node : NetworkNode[T], dot : Digraph):
        '''
        One layout function for edges.
        '''
        dot.edge(str(hash(self)), str(hash(super_node)),
                 label=None)


    
    @property
    def super_nodes(self) -> set[T]:
        return self._super_nodes
    
    @property
    def sub_nodes(self) -> set[T]:
        return self._sub_nodes
    
    @property
    def upstream_nodes(self) -> set[T]:
        '''
        INCLUDE itself.
        '''
        return self._upstream_nodes
    
    @property
    def downstream_nodes(self) -> set[T]:
        '''
        Note that this property is dynamically calculated.
        INCLUDE itself.
        '''
        return self._calc_downstream_nodes()
    
    
    def _calc_upstream_nodes(self) -> set[T]:
        '''
        Calculate and return all the reflexive, transitive closure of super nodes.
        '''

        traveled : set[T] = set()
        upstream_nodes : set[T] = {self}   # type: ignore

        while len(traveled) < len(upstream_nodes):
            for node in upstream_nodes:
                if node not in traveled:
                    traveled.add(node)
                    for new_node in node._super_nodes:
                        if new_node not in upstream_nodes:
                            upstream_nodes.add(new_node)
                    break

        return upstream_nodes
    

    def _calc_downstream_nodes(self) -> set[T]:
        '''
        Calculate and return all the reflexive, transitive closure of sub nodes.
        '''

        traveled : set[T] = set()
        downstream_nodes : set[T] = {self}   # type: ignore

        while len(traveled) < len(downstream_nodes):
            for node in downstream_nodes:
                if node not in traveled:
                    traveled.add(node)
                    for new_node in node._sub_nodes:
                        if new_node not in downstream_nodes:
                            downstream_nodes.add(new_node)
                    break

        return downstream_nodes
    
    def set_super_node(self, super_node : T):
        if super_node not in self.super_nodes:
            self.set_super_nodes(self.super_nodes | {super_node})

    def del_super_node(self, super_node : T):
        if super_node in self.super_nodes:
            self.set_super_nodes(self.super_nodes - {super_node})

    def set_sub_node(self, sub_node : T):
        sub_node.set_super_node(self)

    def del_sub_node(self, sub_node : T):
        sub_node.del_super_node(self)

    def set_super_nodes(self, super_nodes : set[T]):
        '''
        Reset the super node, and calculate the reflexive, transitive closure of super nodes.
        '''

        # check uniqueness
        unique_nodes = set()
        for node in super_nodes:
            if node not in unique_nodes:
                assert isinstance(node, NetworkNode)
                unique_nodes.add(node)
            else:
                print(f"The super node setting '{tuple([str(node) for node in super_nodes])}' for node '{self}' is illegal. The super node '{node}' appears more than once.")

        # cancel the original sub_node items
        for node in self._super_nodes:
            node._sub_nodes = node._sub_nodes - {self}

        self._super_nodes = unique_nodes

        # create the new sub_node items
        for node in self._super_nodes:
            node._sub_nodes = node._sub_nodes | {self}

        # recalculate the reflexive, transitive closure of super nodes
        for node in self.downstream_nodes:
            node._upstream_nodes = node._calc_upstream_nodes()
