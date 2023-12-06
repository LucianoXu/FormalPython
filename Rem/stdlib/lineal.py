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

def S_Term_factory(m_uLC_syn : ModuleTerm) -> RemSort:
    S = RemSort("lineal-Term", {}, (m_uLC_syn["Term"],))
    m_uLC_syn["Term"].set_super_node(S)
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

    F.rule_doc = "M + N"
    F.set_para_doc("M", "N")

    F.set_precedence(30, 'left')

    def term_str(term : RemCons):
        return f"{term['M'].ctx_term_str(term.fun, True)} + {term['N'].ctx_term_str(term.fun, False)}"
    
    F.term_str = term_str

    return F



##################################################
# the syntax-only lineal module

M_lineal_syn = ModuleSort("M_lineal_syn",
    {
        "Term" : RemSort,
        "M_WolComp" : ModuleSort,

        "Var" : RemSort,

        "F_var" : RemFun,
        "F_abstract" : RemFun,
        "F_apply" : RemFun,

        "F_zero"  : RemFun,
        "F_scalar" : RemFun,
        "F_add"     : RemFun,

        # the function to get all variables of a term
        # Callable[[RemCons<Term>], set[str]]
        "vars_of"  : FunctionType,

        # the function to substitute the free appearance of the variable, and return the result
        # Callable[[RemCons, RemCons, RemCons], RemCons]
        # fun M x N => M[N/x]
        "subst" : FunctionType,

        # the function to return a freshvar (F_var) outside the given set of variables
        # Callable[[set[str]], RemCons<F_var>]
        "freshvar" : FunctionType,
    })


MF_lineal_syn = ModuleFun("MF_lineal_syn", ((wolframC.M_WolComp, uLC.M_uLC_syn)), M_lineal_syn)

def __modify_MF_lineal_syn(term : ModuleCons, *paras, **kwparas):

    m_WolComp = paras[0]
    m_uLC_syn = paras[1]

    Term = S_Term_factory(m_uLC_syn)
    term["Term"         ] = Term

    term["M_WolComp"    ] = m_WolComp

    term["Var"          ] = m_uLC_syn["Var"]

    F_var = m_uLC_syn["F_var"]
    term["F_var"        ] = F_var

    F_abstract = m_uLC_syn["F_abstract"]
    term["F_abstract"   ] = F_abstract

    F_apply = m_uLC_syn["F_apply"]
    term["F_apply"      ] = F_apply

    F_zero = F_zero_factory(Term)
    term["F_zero"       ] = F_zero

    F_scalar = F_scalar_factory(m_WolComp, Term)
    term["F_scalar"     ] = F_scalar

    F_add = F_add_factory(Term)
    term["F_add"        ] = F_add


    def vars_of(term : RemCons) -> set[str]:
        if term.fun == F_zero:
            return set()
        elif term.fun == F_scalar:
            return vars_of(term["M"])
        elif term.fun == F_add:
            return vars_of(term["M"]) | vars_of(term["N"])
        elif term.fun == F_var:
            return {term["name"]}
        elif term.fun == F_abstract:
            return {term["x"]} | vars_of(term["M"])
        elif term.fun == F_apply:
            return vars_of(term["M"]) | vars_of(term["N"])
        else:
            raise REM_CONSTRUCTION_Error("Not allowed.")
            
    term["vars_of"] = vars_of

    def subst(M : RemCons, x : RemCons, N : RemCons) -> RemCons:
        if M.fun == F_zero:
            return M
        
        elif M.fun == F_scalar:
            return F_scalar(M["c"], subst(M["M"], x, N))
        
        elif M.fun == F_add:
            return F_add(subst(M["M"], x, N), subst(M["N"], x, N))

        elif M.fun == F_var:
            if M == x:
                return N
            else:
                return M
            
        elif M.fun == F_apply:
            return F_apply(subst(M["M"], x, N), subst(M["N"], x, N))
        
        elif M.fun == F_abstract:
            # in this case the variable is bound
            if M["x"] == x:
                return M
            else:
                # check whether renaming is needed
                vars_of_N = vars_of(N)
                if M["x"]["name"] in vars_of_N:
                    vsets = vars_of_N | vars_of(M["M"])
                    newvar = freshvar(vsets)
                    newM = subst(M["M"], M["x"], newvar)
                    return F_abstract(newvar, subst(newM, x, N))
                else:
                    return F_abstract(M["x"], subst(M["M"], x, N))
            
        else:
            raise Exception()
    term["subst"] = subst


    freshvar = m_uLC_syn["freshvar"]
    
    term["freshvar"] = freshvar

MF_lineal_syn.modify = __modify_MF_lineal_syn

###################################
# alpha-equivalence
# note that `P_alpha_eq` of uLC is still applicable here



def R_alpha_AC_eq_factory(m_lineal_syn : ModuleTerm,  P_alpha_eq : ProofSort) -> ProofFun:

    Term = m_lineal_syn["Term"]
    M_WolComp = m_lineal_syn["M_WolComp"]

    F_var = m_lineal_syn["F_var"]
    F_apply = m_lineal_syn["F_apply"]
    F_abstract = m_lineal_syn["F_abstract"]
    F_zero = m_lineal_syn["F_zero"]
    F_scalar = m_lineal_syn["F_scalar"]
    F_add = m_lineal_syn["F_add"]

    vars_of = m_lineal_syn["vars_of"]
    subst = m_lineal_syn["subst"]
    freshvar = m_lineal_syn["freshvar"]


    R = ProofFun("R_lineal_eq", (Term, Term), P_alpha_eq)

    R.rule_doc = " (automatic check) ⊢ t1 = t2"
    R.set_para_doc("t1", "t2")

    def __collect(term : RemCons) -> List[RemCons]:
        '''
        collect all terms in the addition
        '''
        if term.fun == F_add:
            return __collect(term["M"]) + __collect(term["N"])
        else:
            return [term]


    def extra_check(fun : RemFun, *paras, **kwparas):
        t1 = paras[0]
        t2 = paras[1]

        if isinstance(t1, RemCons) and isinstance(t2, RemCons):
            if t1.fun == t2.fun:
                if t1.fun == F_zero:
                    return 
                
                elif t1.fun == F_scalar:
                    M_WolComp["R_wolcomp_eq"](t1["c"], t2["c"])
                    R(t1["M"], t2["M"])
                    return
                
                elif t1.fun == F_add:
                    ################################
                    # AC equivalence comes in here #
                    ################################

                    # collect and flatten the sequence of addition
                    addls1 = __collect(t1)
                    addls2 = __collect(t2)

                    # check list equivalence
                    if len(addls1) != len(addls2):
                        raise REM_CONSTRUCTION_Error("Inequal addition sequence.")
                    
                    while len(addls1) > 0:
                        head = addls1[0]
                        matched = False
                        for i in range(len(addls1)):
                            try:
                                extra_check(R, head, addls2[i])
                                matched = True
                                addls1 = addls1[1:]
                                addls2 = addls2[:i] + addls2[i+1:]
                                break
                            except REM_CONSTRUCTION_Error:
                                continue

                        if not matched:
                            raise REM_CONSTRUCTION_Error("Inequal addition sequence.")

                    return

                elif t1.fun == F_var:
                    if t1["name"] == t2["name"]:
                        return
                    else:
                        raise REM_CONSTRUCTION_Error("Variable not identical.")
                
                elif t1.fun == F_apply:
                    R(t1["M"], t2["M"])
                    R(t1["N"], t2["N"])
                    return
                
                # alpha-conversion comes in
                elif t1.fun == F_abstract:
                    t1M = t1["M"]
                    t2M = t2["M"]
                    vset = vars_of(t1M) | vars_of(t2M)
                    newbound = freshvar(vset)
                    renamed_t1M = subst(t1M, t1["x"], newbound)
                    renamed_t2M = subst(t2M, t2["x"], newbound)
                    R(renamed_t1M, renamed_t2M)
                    return

                else:
                    raise Exception()

            else:
                raise REM_CONSTRUCTION_Error("Symbol not equivalent.")
        else:
            raise REM_CONSTRUCTION_Error("Meta level variable not allowed in alpha-equivalence comparison.")
        

    R.extra_check = extra_check

    return R

############################################
# parser

def Parser_factory(m_uLC : ModuleTerm, m_WolComp : ModuleTerm, lineal_syn : ModuleTerm) -> PLYParser:

    Term = lineal_syn["Term"]
    F_zero = lineal_syn["F_zero"]
    F_scalar = lineal_syn["F_scalar"]
    F_add = lineal_syn["F_add"]

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

        "P_eq"      : ProofSort,
        "R_eq"      : ProofFun,

        "parser"    : PLYParser,
    })


###################################################
# final module

MF_lineal = ModuleFun("MF_lineal", (wolframC.M_WolComp, uLC.M_uLC), M_lineal)

def __modify_MF_lineal(term : ModuleCons, *paras, **kwparas):

    m_WolComp = paras[0]
    m_uLC = paras[1]
    lineal_syn = MF_lineal_syn(m_WolComp, m_uLC["syn"])

    
    term["Term"         ] = lineal_syn["Term"]

    term["Var"          ] = lineal_syn["Var"]
    term["F_var"        ] = lineal_syn["F_var"]
    term["F_abstract"   ] = lineal_syn["F_abstract"]
    term["F_apply"      ] = lineal_syn["F_apply"]

    term["F_zero"       ] = lineal_syn["F_zero"]

    term["F_scalar"     ] = lineal_syn["F_scalar"]

    term["F_add"        ] = lineal_syn["F_add"]

    #########################
    # about alpha-equivalence

    P_eq = m_uLC["P_eq"]
    term["P_eq"         ] = P_eq

    R_alpha_AC_eq = R_alpha_AC_eq_factory(lineal_syn, P_eq)
    term["R_eq"         ] = R_alpha_AC_eq


    # the parser
    parser = Parser_factory(m_uLC, m_WolComp, lineal_syn)
    parser.build()
    term["parser"       ] = parser
    
MF_lineal.modify = __modify_MF_lineal

def build(m_wolcomp : ModuleTerm, m_uLC : ModuleTerm) -> RemVTerm:
    '''
    build and verify the system
    '''
    return RemVTerm.verify(MF_lineal(m_wolcomp, m_uLC))