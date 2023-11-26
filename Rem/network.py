
from __future__ import annotations

from typing import Tuple, List, Generic, TypeVar

T = TypeVar("T", bound = "NetworkNode[T]")

class NetworkNode(Generic[T]):
    '''
    The nodes of a network.
    '''

    def __init__(self, super_nodes : Tuple[T, ...]):

        self._super_nodes  : Tuple[T, ...] = ()
        self._sub_nodes    : Tuple[T, ...] = ()

        self._upstream_nodes : Tuple[T, ...]
        
        self.set_super_nodes(super_nodes)

    @property
    def super_nodes(self) -> Tuple[T, ...]:
        return self._super_nodes
    
    @property
    def sub_nodes(self) -> Tuple[T, ...]:
        return self._sub_nodes
    
    @property
    def upstream_nodes(self) -> Tuple[T, ...]:
        '''
        INCLUDE itself.
        '''
        return self._upstream_nodes
    
    @property
    def downstream_nodes(self) -> Tuple[T, ...]:
        '''
        Note that this property is dynamically calculated.
        INCLUDE itself.
        '''
        return self._calc_downstream_nodes()
    
    
    def _calc_upstream_nodes(self) -> Tuple[T, ...]:
        '''
        Calculate and return all the reflexive, transitive closure of super nodes.
        '''

        traveled : List[T] = []
        upstream_nodes : List[T] = [self]   # type: ignore

        while len(traveled) < len(upstream_nodes):
            for node in upstream_nodes:
                if node not in traveled:
                    traveled.append(node)
                    for new_node in node._super_nodes:
                        if new_node not in upstream_nodes:
                            upstream_nodes.append(new_node)
                    break

        return tuple(upstream_nodes)
    

    def _calc_downstream_nodes(self) -> Tuple[T, ...]:
        '''
        Calculate and return all the reflexive, transitive closure of sub nodes.
        '''

        traveled : List[T] = []
        downstream_nodes : List[T] = [self]   # type: ignore

        while len(traveled) < len(downstream_nodes):
            for node in downstream_nodes:
                if node not in traveled:
                    traveled.append(node)
                    for new_node in node._sub_nodes:
                        if new_node not in downstream_nodes:
                            downstream_nodes.append(new_node)
                    break

        return tuple(downstream_nodes)
    
    def set_super_node(self, super_node : T):
        if super_node not in self.super_nodes:
            self.set_super_nodes(self.super_nodes + (super_node,))

    def del_super_node(self, super_node : T):
        if super_node in self.super_nodes:
            new_ls = list(self.super_nodes)
            new_ls.remove(super_node)
            self.set_super_nodes(tuple(new_ls))

    def set_sub_node(self, sub_node : T):
        sub_node.set_super_node(self)

    def del_sub_node(self, sub_node : T):
        sub_node.del_super_node(self)

    def set_super_nodes(self, super_nodes : Tuple[T, ...]):
        '''
        Reset the super node, and calculate the reflexive, transitive closure of super nodes.
        '''

        # check uniqueness
        unique_nodes = []
        for node in super_nodes:
            if node not in unique_nodes:
                assert isinstance(node, NetworkNode)
                unique_nodes.append(node)
            else:
                print(f"The super node setting '{tuple([str(node) for node in super_nodes])}' for node '{self}' is illegal. The super node '{node}' appears more than once.")

        # cancel the original sub_node items
        for node in self._super_nodes:
            temp = list(node._sub_nodes)
            temp.remove(self)
            node._sub_nodes = tuple(temp)

        self._super_nodes = tuple(unique_nodes)

        # create the new sub_node items
        for node in self._super_nodes:
            node._sub_nodes = node._sub_nodes + (self,)

        # recalculate the reflexive, transitive closure of super nodes
        for node in self.downstream_nodes:
            node._upstream_nodes = node._calc_upstream_nodes()
