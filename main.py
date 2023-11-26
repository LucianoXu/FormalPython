import numpy as np

from Rem import network as nw




if __name__ == "__main__":
    n1 = nw.NetworkNode(())
    n2 = nw.NetworkNode(())
    n3 = nw.NetworkNode(())
    n4 = nw.NetworkNode(())

    net = nw.Network({n1, n2, n3, n4})

    n2.set_super_node(n1)
    n1.set_super_node(n2)
    n1.set_super_node(n3)

    print(n3.downstream_nodes)

    net.draw().render("output")