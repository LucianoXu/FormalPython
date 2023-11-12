
from __future__ import annotations

from typing import Tuple, List

class NetworkNode:
    '''
    The nodes of a network.
    '''

    def __init__(self, super_nodes : Tuple[NetworkNode, ...]):
        self.__super_nodes  : Tuple[NetworkNode, ...] = ()
        self.__sub_nodes    : Tuple[NetworkNode, ...] = ()

        self.__upstream_nodes : Tuple[NetworkNode, ...]
        
        self.set_super_nodes(super_nodes)

    @property
    def super_nodes(self) -> Tuple[NetworkNode, ...]:
        return self.__super_nodes
    
    @property
    def sub_nodes(self) -> Tuple[NetworkNode, ...]:
        return self.__sub_nodes
    
    @property
    def upstream_nodes(self) -> Tuple[NetworkNode, ...]:
        return self.__upstream_nodes
    
    @property
    def downstream_nodes(self) -> Tuple[NetworkNode, ...]:
        '''
        Note that this property is dynamically calculated.
        '''
        return self.__calc_downstream_nodes()
    
    
    def __calc_upstream_nodes(self) -> Tuple[NetworkNode, ...]:
        '''
        Calculate and return all the reflexive, transitive closure of super nodes.
        '''

        traveled : List[NetworkNode] = []
        upstream_nodes : List[NetworkNode] = [self]

        while len(traveled) < len(upstream_nodes):
            for node in upstream_nodes:
                if node not in traveled:
                    traveled.append(node)
                    for new_node in node.__super_nodes:
                        if new_node not in upstream_nodes:
                            upstream_nodes.append(new_node)
                    break

        return tuple(upstream_nodes)
    

    def __calc_downstream_nodes(self) -> Tuple[NetworkNode, ...]:
        '''
        Calculate and return all the reflexive, transitive closure of sub nodes.
        '''

        traveled : List[NetworkNode] = []
        downstream_nodes : List[NetworkNode] = [self]

        while len(traveled) < len(downstream_nodes):
            for node in downstream_nodes:
                if node not in traveled:
                    traveled.append(node)
                    for new_node in node.__sub_nodes:
                        if new_node not in downstream_nodes:
                            downstream_nodes.append(new_node)
                    break

        return tuple(downstream_nodes)
    
    def set_super_node(self, super_node : NetworkNode):
        if super_node not in self.super_nodes:
            self.set_super_nodes(self.super_nodes + (super_node,))

    def del_super_node(self, super_node : NetworkNode):
        if super_node in self.super_nodes:
            new_ls = list(self.super_nodes)
            new_ls.remove(super_node)
            self.set_super_nodes(tuple(new_ls))

    def set_sub_node(self, sub_node : NetworkNode):
        sub_node.set_sub_node(self)

    def del_sub_node(self, sub_node : NetworkNode):
        sub_node.del_super_node(self)

    def set_super_nodes(self, super_nodes : Tuple[NetworkNode, ...]):
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
        for node in self.__super_nodes:
            temp = list(node.__sub_nodes)
            temp.remove(self)
            node.__sub_nodes = tuple(temp)

        self.__super_nodes = tuple(unique_nodes)

        # create the new sub_node items
        for node in self.__super_nodes:
            node.__sub_nodes = node.__sub_nodes + (self,)

        # recalculate the reflexive, transitive closure of super nodes
        for node in self.downstream_nodes:
            node.__upstream_nodes = node.__calc_upstream_nodes()
