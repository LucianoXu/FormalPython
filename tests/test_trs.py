
from Rem import *


def test_group():
    G = RemSort("G")
    e = RemFun("e", (), G)
    i = RemFun("i", (G,), G)
    m = RemFun("m", (G, G), G)

    G1 = RemRedRule(m(m("?x", "?y"), "?z"), m("?x", m("?y", "?z")))
    G2 = RemRedRule(m(e(), "?x"), RemVar("?x"))
    G3 = RemRedRule(m("?x", e()), RemVar("?x"))
    G4 = RemRedRule(m(i("?x"), "?x"), e())
    G5 = RemRedRule(m("?x", i("?x")), e())
    G6 = RemRedRule(i(e()), e())

    TRS = RemTRS([G1, G2, G3, G4, G5, G6])

    t = m(i(m("x", i("x"))), m("x", i("x")))

    assert TRS.reduces(t) == e()