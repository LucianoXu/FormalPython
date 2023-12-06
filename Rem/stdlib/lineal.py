'''
lineal : linear algebraic lambda calculus, untyped
'''

from ..core import *

from types import FunctionType

from . import uLC
from . import wolframC


#########################################################
# linear term sort
## WARNING: m_uLC's Term sort will be modified.

def S_Term_factory(m_uLC : ModuleTerm) -> RemSort:
    S = RemSort("lineal-Term", {}, (m_uLC["Term"],))
    m_uLC["Term"].set_super_node(S)
    return S

#########################################################
# zero term

def F_zero_factory(Term : RemSort) -> RemFun:
    F = RemFun("f_zero", (), Term)
    F.rule_doc = " 𝟬 "

    def term_str(term : RemCons):
        return "𝟬"
    
    F.term_str = term_str

    return F

#########################################################
# scalar

def F_scalar_factory(m_WolComp : ModuleTerm, Term : RemSort) -> RemFun:
    F = RemFun("f_scalar", (m_WolComp["WolComp"], Term), Term)

    F.rule_doc = "c*M"
    F.set_para_doc("c", "M")

    F.set_precedence(70, 'right')

    def term_str(term : RemCons):
        return f"{term['c'].ctx_term_str(term.fun, True)}*{term['M'].ctx_term_str(term.fun, False)}"
    
    F.term_str = term_str

    return F


#########################################################
# addition

def F_add_factory(Term : RemSort) -> RemFun:
    F = RemFun("f_add", (Term, Term), Term)

    F.rule_doc = "t1 + t2"
    F.set_para_doc("t1", "t2")

    F.set_precedence(30, 'left')

    def term_str(term : RemCons):
        return f"{term['t1'].ctx_term_str(term.fun, True)} + {term['t2'].ctx_term_str(term.fun, False)}"
    
    F.term_str = term_str

    return F

def Parser_factory(m_uLC : ModuleTerm, m_WolComp : ModuleTerm, 
        Term : RemSort, F_zero : RemFun, F_scalar : RemFun, F_add : RemFun) -> PLYParser:

    lexer = PLYLexer("lineal")
    lexer.fuse_append(m_uLC["parser"].bound_plylexer)
    lexer.fuse_append(m_WolComp["parser"].bound_plylexer)

    parser = PLYParser(lexer, "lineal", "lineal")
    parser.fuse_append(m_uLC["parser"])
    parser.fuse_append(m_WolComp["parser"])

    lexer.add_literals({'*', '+'})
    lexer.add_normal_token("OPTZERO", r"𝟬|\\0")

    def p_rule_optzero(p):
        '''
        lineal-term : OPTZERO
        '''
        p[0] = F_zero()
    parser.add_rule(p_rule_optzero)

    def p_rule_scalar(p):
        '''
        lineal-term : wolcomp-term '*' lineal-term
        '''
        p[0] = F_scalar(p[1], p[3])
    parser.set_precedence('*', 70, 'right')
    parser.add_rule(p_rule_scalar)

    def p_rule_add(p):
        '''
        lineal-term : lineal-term '+' lineal-term
        '''
        p[0] = F_add(p[1], p[3])
    parser.set_precedence('+', 30, 'left')
    parser.add_rule(p_rule_add)

    parser.add_subterm("lineal", "lineal-term")
    parser.add_subterm("lineal-term", "uLC-term")
    parser.add_subterm("uLC-term", "lineal-term")

    return parser


M_lineal = ModuleSort("M_lineal",
    {
        "Term" : RemSort,
        "Var" : RemSort,

        "F_var" : RemFun,
        "F_abstract" : RemFun,
        "F_apply" : RemFun,

        "F_zero"  : RemFun,
        "F_scalar" : RemFun,
        "F_add"     : RemFun,

        "parser"    : PLYParser,
    })


MF_lineal = ModuleFun("MF_lineal", (wolframC.M_WolComp, uLC.M_uLC), M_lineal)

def __modify_MF_lineal(term : ModuleCons, *paras, **kwparas):

    m_WolComp = paras[0]
    m_uLC = paras[1]

    Term = S_Term_factory(m_uLC)
    term["Term"         ] = Term

    term["Var"          ] = m_uLC["Var"]
    term["F_var"        ] = m_uLC["F_var"]
    term["F_abstract"   ] = m_uLC["F_abstract"]
    term["F_apply"      ] = m_uLC["F_apply"]

    F_zero = F_zero_factory(Term)
    term["F_zero"       ] = F_zero

    F_scalar = F_scalar_factory(m_WolComp, Term)
    term["F_scalar"     ] = F_scalar

    F_add = F_add_factory(Term)
    term["F_add"        ] = F_add

    parser = Parser_factory(m_uLC, m_WolComp, Term, F_zero, F_scalar, F_add)
    parser.build()
    term["parser"       ] = parser
    
MF_lineal.modify = __modify_MF_lineal

def build(m_wolcomp : ModuleTerm, m_uLC : ModuleTerm) -> RemVTerm:
    '''
    build and verify the system
    '''
    return RemVTerm.verify(MF_lineal(m_wolcomp, m_uLC))