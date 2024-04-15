
from Rem import *

def test_TRaAT_E_4_6_4():
    '''
    [Term rewriting and all that] Example 4.6.4
    '''
    S = RemSort("S")
    f = RemFun("f", (S,), S)
    g = RemFun("g", (S, S), S)

    p = RemUnification([(RemVar("x"), f("a")), (g("x", "x"), g("x", "y"))])

    assert p.solve() == RemSubst({"x" : f("a"), "y" : f("a")})
