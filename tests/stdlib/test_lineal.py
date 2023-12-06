from Rem import *
from Rem import wolframC, uLC, lineal

from wolframclient.evaluation import WolframLanguageSession

def test_eq_1():
    session = WolframLanguageSession()
    try:
        L = lineal.build(
            wolframC.MF_WolComp(session=session), 
            uLC.MF_uLC(uLC.MF_uLC_syn())
        )

        t1 = L["parser"](r'\lambda x. "a"*(x + (\lambda x.x + z))')
        t2 = L["parser"](r'\lambda y. "a"*((\lambda x.x + y) + z)')
        
        L["R_eq"](t1, t2)

    finally:
        session.terminate()


def test_Not():
    session = WolframLanguageSession()
    try:
        L = lineal.build(
            wolframC.MF_WolComp(session=session), 
            uLC.MF_uLC(uLC.MF_uLC_syn())
        )

        env = RemSubst(
            {
                "true"  : L["parser"]("λx.λy.x"),
                "false" : L["parser"]("λx.λy.y"),
                "Not"   : L["parser"]("λf.(f (λx.λy.y) (λx.λy.x))"),
            }
        )

        t1 = L["F_apply"]("Not", "true")
        t2 = RemVar("false")

        L["R_eq"](L["TRS"].reduces(env(t1)), L["TRS"].reduces(env(t2)))

    finally:
        session.terminate()

def test_Phase():
    session = WolframLanguageSession()
    try:
        L = lineal.build(
            wolframC.MF_WolComp(session=session), 
            uLC.MF_uLC(uLC.MF_uLC_syn())
        )

        env = RemSubst(
            {
                "true"  : L["parser"]("λx.λy.x"),
                "false" : L["parser"]("λx.λy.y"),
                "Not"   : L["parser"]("λf.(f (λx.λy.y) (λx.λy.x))"),
                "Phase" : L["parser"]('λy.((y λx.("E^(I Pi/4)" * (λx.λy.x)) (λx.λx.λy.y)) λx.x)'),
            }
        )

        t1 = L["F_apply"]("Phase", "true")
        t2 = L["parser"]('"E^(I Pi/4)"*λx.λy.x')

        L["R_eq"](L["TRS"].reduces(env(t1)), L["TRS"].reduces(env(t2)))


        t1 = L["F_apply"]("Phase", "false")
        t2 = RemVar("false")

        L["R_eq"](L["TRS"].reduces(env(t1)), L["TRS"].reduces(env(t2)))

    finally:
        session.terminate()
