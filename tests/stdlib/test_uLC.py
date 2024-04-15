
from Rem import uLC


def test_alpha_eq_1():    
    lc = uLC.build()
    a = lc["parser"]("λy. y")
    b = lc["parser"](r"\lambda z. z")
    lc["R_eq"](a, b)

def test_alpha_eq_2():    
    lc = uLC.build()
    a = lc["parser"]("λx.λy.(x y)")
    b = lc["parser"]("λy.λx.(y x)")
    lc["R_eq"](a, b)

def test_red_1():
    lc = uLC.build()
    start = lc["parser"]("(λy. λx.(x y)) x")
    target = lc["parser"]("λz.(z x)")
    result = lc["TRS"].reduces(start)
    lc["R_eq"](result, target)
    

def test_red_2():
    lc = uLC.build()
    start = lc["parser"]("(λf.(f a)) ((λx.(x x)) (λy.y))")
    target = lc["parser"]("a")
    result = lc["TRS"].reduces(start)
    lc["R_eq"](result, target)