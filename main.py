

import numpy as np

from Rem import *
from Rem import uLC, wolframC, lineal

from wolframclient.evaluation import WolframLanguageSession

if __name__ == "__main__":
    session = WolframLanguageSession()
    try:
        L = lineal.build(wolframC.MF_WolComp(session=session), uLC.MF_uLC(uLC.MF_uLC_syn()))

        env = RemSubst(
            {
                "true"  : L["parser"]("λx.λy.x"),
                "false" : L["parser"]("λx.λy.y"),
                "H"     : L["parser"]
                    ('''                     
                        λy.(
                            (
                                y 
                                λo."Sqrt[2]/2"*(λx.λy.x + λx.λy.y)
                                (λo.("Sqrt[2]/2"*(λx.λy.x) + "-Sqrt[2]/2"*(λx.λy.y)))
                            ) 
                            λx.x
                        )
                        '''),
                "dot"   : L["parser"]('λA.λB.(λy.(A (B y)))')
            }
        )

        t = L["F_apply"]("H", L["parser"]('λx.λy.x'))

        t = L["F_apply"](L["F_apply"](L["F_apply"]("dot", "H"), "H"), L["parser"]('"a"*λx.λy.x + "b"*λx.λy.y'))
        L["TRS"].reduces(env(t), silent = False)

    except Exception as e:
        print(e)
        session.terminate()

    finally:
        session.terminate()