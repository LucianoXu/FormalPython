'''
module for Wolfram complex number

Note that the wolfram terms are build simultaneously when building Rem terms.
'''

from ..core import *

from wolframclient.evaluation import WolframLanguageSession
from wolframclient.language import wl, wlexpr

def S_WolComp_factory(session : WolframLanguageSession) -> RemSort:
    S = RemSort("Wolfram Complex", {'term' : object})
    S.doc = "<wolcomp>"
    S["session"] = session

    def term_str(term : RemCons):
        return f'"{term["term"]}"'
    
    S.term_str = term_str    

    return S

def F_wolcode_factory(WolComp : RemSort) -> RemFun:
    F = RemFun("f_wolcode", (), WolComp, {"code" : str})

    F.rule_doc = "<wolfram code>"

    def term_str(term : RemCons):
        return f'"{term["code"]}"'
    
    F.term_str = term_str
    
    def modify(term : RemCons, *paras, **kwparas):
        term["term"] =  wlexpr(kwparas["code"])
    F.modify = modify

    return F

def F_wolcomp_zero_factory(WolComp : RemSort) -> RemFun:
    F = RemFun("f_wolcomp_zero", (), WolComp)

    F.rule_doc = "<wolfram 0>"

    def term_str(term : RemCons):
        return f'"0"'
    
    F.term_str = term_str
    
    def modify(term : RemCons, *paras, **kwparas):
        term["term"] = wlexpr(0)

    F.modify = modify
    return F

def F_wolcomp_one_factory(WolComp : RemSort) -> RemFun:
    F = RemFun("f_wolcomp_one", (), WolComp)

    F.rule_doc = "<wolfram 1>"

    def term_str(term : RemCons):
        return f'"1"'
    
    F.term_str = term_str
    
    def modify(term : RemCons, *paras, **kwparas):
        term["term"] = wlexpr(1)

    F.modify = modify
    return F

def F_wolcomp_add_factory(WolComp : RemSort) -> RemFun:
    F = RemFun("f_wolcomp_add", (WolComp, WolComp), WolComp)

    F.rule_doc = "c1 + c2"

    F.set_para_doc("c1", "c2")

    F.set_precedence(150, 'left')

    def term_str(term : RemCons):
        return f'{term["c1"].ctx_term_str(term.fun, True)} + {term["c2"].ctx_term_str(term.fun, False)}'
    
    F.term_str = term_str
    
    def modify(term : RemCons, *paras, **kwparas):
        term["term"] = wl.Plus(paras[0]["term"], paras[1]["term"])

    F.modify = modify
    return F

def F_wolcomp_mul_factory(WolComp : RemSort) -> RemFun:
    F = RemFun("f_wolcomp_mul", (WolComp, WolComp), WolComp)

    F.rule_doc = "c1 * c2"
    F.set_para_doc("c1", "c2")

    F.set_precedence(160, 'left')

    def term_str(term : RemCons):
        return f'{term["c1"].ctx_term_str(term.fun, True)} * {term["c2"].ctx_term_str(term.fun, False)}'
    
    F.term_str = term_str
    
    def modify(term : RemCons, *paras, **kwparas):
        term["term"] = wl.Times(paras[0]["term"], paras[1]["term"])

    F.modify = modify
    return F


def F_wolcomp_conj_factory(WolComp : RemSort) -> RemFun:
    F = RemFun("f_wolcomp_conj", (WolComp,), WolComp)

    F.rule_doc = "conj(c)"

    F.set_para_doc("c")

    F.set_precedence(180, 'left')

    def term_str(term : RemCons):
        return f'conj({term["c"]})'
    
    F.term_str = term_str
    
    def modify(term : RemCons, *paras, **kwparas):
        term["term"] = wl.Conjugate(paras[0]["term"])

    F.modify = modify
    return F

#########################################################
# equivalence checked by Wolfram

# the function to check equiality
def wolcomp_eq_fun_factory(WolComp : RemSort):
    def f(c1 : RemCons, c2 : RemCons) -> bool:
        return WolComp["session"].evaluate(wl.Simplify(wl.Equal(c1["term"], c2["term"]))) == True
    
    return f

# equality proof
def P_wolcomp_eq_factory(WolComp : RemSort) -> ProofSort:
    P = ProofSort("P_wolcomp_eq", {"c1": WolComp, "c2" : WolComp})

    def term_str(term : RemCons):
        return f"{term['c1']} = {term['c2']}"
    
    P.term_str = term_str
    return P

def R_wolcomp_eq_factory(WolComp : RemSort, P_wolcomp_eq : ProofSort) -> ProofFun:

    R = ProofFun("R_wolcomp_eq", (WolComp, WolComp), P_wolcomp_eq)

    R.rule_doc = " (Wolfram engine) ⊢ c1 = c2"
    R.set_para_doc("c1", "c2")

    eq_check = wolcomp_eq_fun_factory(WolComp)

    # the check conducted by Wolfram
    def extra_check(fun : RemFun, *paras, **kwparas):
        if not eq_check(paras[0], paras[1]):
            raise REM_CONSTRUCTION_Error(f"Inequal wolfram complex terms:\n\n{paras[0]['term']}\n\nand\n\n{paras[1]['term']}")
        
    R.extra_check = extra_check

    return R

#############################################################
# parser

def Parser_factory(F_wolcode : RemFun) -> PLYParser:
    lexer = PLYLexer("wolcode")
    lexer.add_normal_token("ignore", " \t")

    def t_WOLFRAM_CODE(t):
        r'"[^"]*"'
        t.value = t.value[1:-1]
        return t

    lexer.add_normal_token("WOLFRAM_CODE", t_WOLFRAM_CODE)

    parser = PLYParser(lexer, "wolcode", "wolcode")

    def p_rule(p):
        '''
        wolcode    : WOLFRAM_CODE
        '''
        p[0] = F_wolcode(code = p[1])

    parser.add_rule(p_rule)

    return parser

M_WolComp = ModuleSort("M_WolComp",
    {
        "WolComp" : RemSort,
        "F_wolcode" : RemFun,
        "F_wolcomp_zero"    : RemFun,
        "F_wolcomp_one"     : RemFun,
        "F_wolcomp_add"     : RemFun,
        "F_wolcomp_mul"     : RemFun,
        "F_wolcomp_conj"     : RemFun,
        "wolcomp_eq_fun"     : FunctionType,
        "P_wolcomp_eq"      : ProofSort,
        "R_wolcomp_eq"      : ProofFun,

        "parser"            : PLYParser,
    })

MF_WolComp = ModuleFun("MF_WolComp", (), M_WolComp, {"session" : WolframLanguageSession})
def __modify_MF_WolComp(term : ModuleCons, *paras, **kwparas):
    session = kwparas["session"]
    WolComp = S_WolComp_factory(session)
    term["WolComp"          ] = WolComp
    term["F_wolcode"        ] = F_wolcode_factory(WolComp)
    term["F_wolcomp_zero"   ] = F_wolcomp_zero_factory(WolComp)
    term["F_wolcomp_one"    ] = F_wolcomp_one_factory(WolComp)
    term["F_wolcomp_add"    ] = F_wolcomp_add_factory(WolComp)
    term["F_wolcomp_mul"    ] = F_wolcomp_mul_factory(WolComp)
    term["F_wolcomp_conj"   ] = F_wolcomp_conj_factory(WolComp)
    term["wolcomp_eq_fun"   ] = wolcomp_eq_fun_factory(WolComp)
    P_wolcomp_eq = P_wolcomp_eq_factory(WolComp)
    term["P_wolcomp_eq"     ] = P_wolcomp_eq
    term["R_wolcomp_eq"     ] = R_wolcomp_eq_factory(WolComp, P_wolcomp_eq)

    parser = Parser_factory(term["F_wolcode"])
    parser.build()
    term["parser"] = parser

MF_WolComp.modify = __modify_MF_WolComp


def build(session : WolframLanguageSession) -> RemVTerm:
    '''
    build and verify the system
    '''
    return RemVTerm.verify(MF_WolComp(session=session))

