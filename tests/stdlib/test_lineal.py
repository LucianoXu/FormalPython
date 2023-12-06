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