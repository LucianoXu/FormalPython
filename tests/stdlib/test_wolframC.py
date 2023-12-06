
from Rem import wolframC

from wolframclient.evaluation import WolframLanguageSession

def test_eq_1():
    session = WolframLanguageSession()

    try:
        wc = wolframC.build(session)

        a = wc["parser"]('"a+b"')
        b = wc["parser"]('"b+a"')

        wc["R_wolcomp_eq"](a, b)

    finally:
        session.terminate()


def test_eq_2():
    session = WolframLanguageSession()

    try:
        wc = wolframC.build(session)

        a = wc["parser"]('"a+2b"')
        b = wc["parser"]('"b+a"')

        assert not wc["wolcomp_eq_fun"](a, b)

    finally:
        session.terminate()

def test_eq_3():
    session = WolframLanguageSession()

    try:
        wc = wolframC.build(session)

        a = wc["parser"]('"Cos[a]^2 + Sin[a]^2"')
        b = wc["parser"]('"Sum[1/2^i, {i,1,Infinity}]"')

        wc["R_wolcomp_eq"](a, b)

    finally:
        session.terminate()