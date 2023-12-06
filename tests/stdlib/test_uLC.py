
from Rem import uLC


def test_alpha_eq_1():    
    lc = uLC.build()
    a = lc["parser"]("λy. y")
    b = lc["parser"]("λz. z")
    lc["R_eq"](a, b)


def test_red_1():
    lc = uLC.build()
    start = lc["parser"]("(λy. λx.(x y)) x")
    target = lc["parser"]("λz.(z x)")
    result = lc["TRS"].reduces(start)
    lc["R_eq"](result, target)