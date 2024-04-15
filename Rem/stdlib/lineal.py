'''
lineal : linear algebraic lambda calculus, untyped
'''
from __future__ import annotations

from ..core import *
from types import FunctionType

from . import uLC
from . import wolframC

from itertools import permutations

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
                    vsets = vars_of_N | vars_of(M["M"]) | {x["name"]}
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


###################################################
# TRS 

def TRS_factory(lineal_syn : ModuleTerm, R_eq : ProofFun) -> RemTRS:
    '''
    R_eq : alpha-conversion and AC-equivalence
    '''

    m_WolComp = lineal_syn["M_WolComp"]
    F_var = lineal_syn["F_var"]
    F_apply = lineal_syn["F_apply"]
    F_abstract = lineal_syn["F_abstract"]
    F_zero = lineal_syn["F_zero"]
    F_scalar = lineal_syn["F_scalar"]
    F_add = lineal_syn["F_add"]

    subst = lineal_syn["subst"]

    def freevars(term : RemCons) -> set[RemCons]:
        if term.fun == F_var:
            return {term}
        elif term.fun == F_apply:
            return freevars(term["M"]) | freevars(term["N"])
        elif term.fun == F_abstract:
            return freevars(term["M"]) - {term["x"]}
        elif term.fun == F_zero:
            return set()
        elif term.fun == F_scalar:
            return freevars(term["M"])
        elif term.fun == F_add:
            return freevars(term["M"]) | freevars(term["N"])
        else:
            raise Exception()


    def closed_L_normal(term : RemCons) -> bool:
        '''
        Check whether term is closed L-normal
        '''
        if len(freevars(term)) > 0:
            return False
        
        if TRS.reduce(term) is not None:
            return False
        
        return True
    
    ############################
    # for E-matching

    def eq_check(a : RemTerm, b : RemTerm) -> bool:
        try:
            RemVTerm.verify(R_eq(a, b))
            return True
        
        except REM_CONSTRUCTION_Error:
            return False
        

    def __collect(term : RemCons) -> Tuple[RemTerm, ...]:
        '''
        collect all terms in the addition
        '''
        if term.fun == F_add:
            return __collect(term["M"]) + __collect(term["N"])
        else:
            return (term,)
        
    def eq_set(a : RemTerm) -> List[RemTerm]:
        
            return [a]




    #######

    rule_list : List[RemRedRule] = []

    #########################################
    # Group C -- FullySimplify Wolfram Terms

    ### COMPLEX_SIMP
    def complex_simp_sidecond(matcher : RemSubst) -> RemSubst | None:
        c = matcher["?c"]
        assert isinstance(c, RemCons)
        if c.fun != m_WolComp["F_wolsimp"]:
            return matcher
        else:
            return None

    def complex_simp_RHS(matcher : RemSubst) -> RemTerm:
        return F_scalar(m_WolComp["F_wolsimp"](matcher["?c"]), matcher["?u"])
        
    COMPLEX_SIMP = RemRedRule(F_scalar("?c", "?u"), complex_simp_RHS, "simp(?c)*?u", complex_simp_sidecond, "?c is not simplified" )

    # rule_list.append(COMPLEX_SIMP)

    ##################################################################
    # Group E

    ### ADD0
    ADD0_L = RemRedRule(F_add("?u", F_zero()), RemVar("?u"))
    rule_list.append(ADD0_L)
    ADD0_R = RemRedRule(F_add(F_zero(), "?u"), RemVar("?u"))
    rule_list.append(ADD0_R)

    ### SCALAR0
    def scalar0_sidecond(matcher : RemSubst) -> RemSubst | None:
        if m_WolComp["wolcomp_eq_fun"](matcher["?c"], m_WolComp["F_wolcomp_zero"]()):
            return matcher
        else:
            return None
        
    SCALAR0 = RemRedRule(F_scalar("?c", "?u"), F_zero(), "𝟬", scalar0_sidecond, "?c is 0" )
    rule_list.append(SCALAR0)

    ### SCALAR1
    def scalar1_sidecond(matcher : RemSubst) -> RemSubst | None:
        if m_WolComp["wolcomp_eq_fun"](matcher["?c"], m_WolComp["F_wolcomp_one"]()):
            return matcher
        else:
            return None
        
    SCALAR1 = RemRedRule(F_scalar("?c", "?u"), RemVar("?u"), "?u", scalar1_sidecond, "?c is 1" )
    rule_list.append(SCALAR1)


    ### SCALAR_VEC0
    SCALAR_VEC0 = RemRedRule(F_scalar("?c", F_zero()), F_zero())
    rule_list.append(SCALAR_VEC0)


    ### DOUBLE_SCALAR
    def double_scalar_RHS(matcher : RemSubst) -> RemTerm:
        c1 = matcher["?c1"]
        c2 = matcher["?c2"]
        u = matcher["?u"]
        return F_scalar(m_WolComp["F_wolcomp_mul"](c1, c2), u)

    DOUBLE_SCALAR = RemRedRule(F_scalar("?c1", F_scalar("?c2", "?u")), double_scalar_RHS, "(?c1*?c2)*?u")
    rule_list.append(DOUBLE_SCALAR)


    ### DISTRIBUTE
    DISTRIBUTE = RemRedRule(F_scalar("?c", F_add("?u", "?v")), F_add(F_scalar("?c", "?u"), F_scalar("?c", "?v")))
    rule_list.append(DISTRIBUTE)



    ##################################################################
    # Group F

    def fac_sidecond(matcher : RemSubst) -> RemSubst | None:

        if not closed_L_normal(matcher["?u"]): # type: ignore
            return None
        
        return matcher

    ### FAC2

    def fac2_RHS(matcher : RemSubst) -> RemTerm:
        c1 = matcher["?c1"]
        c2 = matcher["?c2"]
        u = matcher["?u"]
        return F_scalar(m_WolComp["F_wolcomp_add"](c1, c2), u)

    FAC2 = RemRedRule(F_add(F_scalar("?c1", "?u"), F_scalar("?c2", "?u")), fac2_RHS, "", fac_sidecond)
    rule_list.append(FAC2)

    ### FAC2_EXTRA
    def fac2_extra_matching(term : RemTerm) -> RemSubst | None:
        assert isinstance(term, RemCons)
        add_terms = __collect(term)

        for i in range(len(add_terms)):
            term_i = add_terms[i]
            assert isinstance(term_i, RemCons)

            if term_i.fun == F_scalar:
                for j in range(i + 1, len(add_terms)):
                    term_j = add_terms[j]
                    assert isinstance(term_j, RemCons)
                    if term_j.fun == F_scalar and eq_check(term_i["M"], term_j["M"]):

                        remainings = None
                        for k in range(len(add_terms)):

                            if k != i and k != j:
                                if remainings is None:
                                    remainings = add_terms[k]
                                else:
                                    remainings = F_add(remainings, add_terms[k])
                        if remainings is None:
                            return None

                        return RemSubst({
                            "?c1" : term_i["c"],
                            "?c2" : term_j["c"],
                            "?u"  : term_i["M"],
                            "?V"  : remainings
                        })


    def fac2_extra_RHS(matcher : RemSubst) -> RemTerm:
        c1 = matcher["?c1"]
        c2 = matcher["?c2"]
        u = matcher["?u"]
        V = matcher["?V"]
        return F_add(F_scalar(m_WolComp["F_wolcomp_add"](c1, c2), u), V)
    
    FAC2_EXTRA = RemRedRule(fac2_extra_matching, fac2_extra_RHS, "", fac_sidecond)
    rule_list.append(FAC2_EXTRA)

    ### FAC1L
    def fac1l_RHS(matcher : RemSubst) -> RemTerm:
        c = matcher["?c"]
        u = matcher["?u"]
        return F_scalar(m_WolComp["F_wolcomp_add"](c, m_WolComp["F_wolcomp_one"]()), u)

    FAC1L = RemRedRule(F_add(F_scalar("?c", "?u"), "?u"), fac1l_RHS, "(?c+1)*?u", fac_sidecond)
    rule_list.append(FAC1L)

    ### FAC1R
    def fac1r_RHS(matcher : RemSubst) -> RemTerm:
        c = matcher["?c"]
        u = matcher["?u"]
        return F_scalar(m_WolComp["F_wolcomp_add"](m_WolComp["F_wolcomp_one"](), c), u)

    FAC1R = RemRedRule(F_add("?u", F_scalar("?c", "?u")), fac1r_RHS, "", fac_sidecond)
    rule_list.append(FAC1R)

    ### FAC1_EXTRA
    def fac1_extra_matching(term : RemTerm) -> RemSubst | None:
        assert isinstance(term, RemCons)
        add_terms = __collect(term)

        for i in range(len(add_terms)):
            term_i = add_terms[i]
            assert isinstance(term_i, RemCons)

            if term_i.fun == F_scalar:
                for j in range(len(add_terms)):
                    if j == i:
                        continue

                    term_j = add_terms[j]
                    assert isinstance(term_j, RemCons)
                    if eq_check(term_i["M"], term_j):

                        remainings = None
                        for k in range(len(add_terms)):

                            if k != i and k != j:
                                if remainings is None:
                                    remainings = add_terms[k]
                                else:
                                    remainings = F_add(remainings, add_terms[k])
                        if remainings is None:
                            return None

                        return RemSubst({
                            "?c"  : term_i["c"],
                            "?u"  : term_i["M"],
                            "?V"  : remainings
                        })


    def fac1_extra_RHS(matcher : RemSubst) -> RemTerm:
        c = matcher["?c"]
        u = matcher["?u"]
        V = matcher["?V"]
        return F_add(F_scalar(m_WolComp["F_wolcomp_add"](c, m_WolComp["F_wolcomp_one"]()), u), V)
    
    FAC1_EXTRA = RemRedRule(fac1_extra_matching, fac1_extra_RHS, "", fac_sidecond)
    rule_list.append(FAC1_EXTRA)


    ### FAC0
    FAC0 = RemRedRule(F_add("?u", "?u"), 
        F_scalar(m_WolComp["F_wolcomp_add"](m_WolComp["F_wolcomp_one"](), 
        m_WolComp["F_wolcomp_one"]()), "?u"), "", fac_sidecond)
    rule_list.append(FAC0)

    ### FAC0_EXTRA
    def fac0_extra_matching(term : RemTerm) -> RemSubst | None:
        assert isinstance(term, RemCons)
        add_terms = __collect(term)

        for i in range(len(add_terms)):
            term_i = add_terms[i]
            assert isinstance(term_i, RemCons)

            for j in range(i + 1, len(add_terms)):

                term_j = add_terms[j]
                assert isinstance(term_j, RemCons)
                if eq_check(term_i, term_j):

                    remainings = None
                    for k in range(len(add_terms)):

                        if k != i and k != j:
                            if remainings is None:
                                remainings = add_terms[k]
                            else:
                                remainings = F_add(remainings, add_terms[k])
                    if remainings is None:
                        return None

                    return RemSubst({
                        "?u"  : term_i,
                        "?V"  : remainings
                    })


    def fac0_extra_RHS(matcher : RemSubst) -> RemTerm:
        u = matcher["?u"]
        V = matcher["?V"]
        return F_add(F_scalar(m_WolComp["F_wolcomp_add"](m_WolComp["F_wolcomp_one"](), m_WolComp["F_wolcomp_one"]()), u), V)
    
    FAC0_EXTRA = RemRedRule(fac0_extra_matching, fac0_extra_RHS, "", fac_sidecond)
    rule_list.append(FAC0_EXTRA)

    ######################################################
    # Group A

    ### APP_DISTR_L

    def app_distr_sidecond(matcher : RemSubst) -> RemSubst | None:

        if not closed_L_normal(F_add(matcher["?u"], matcher["?v"])): # type: ignore
            return None
        
        return matcher

    APP_DISTR_L = RemRedRule(F_apply(F_add("?u", "?v"), "?w"), F_add(F_apply("?u", "?w"), F_apply("?v", "?w")), "", app_distr_sidecond, "(?u + ?v) is L-normal")
    rule_list.append(APP_DISTR_L)

    ### APP_DISTR_R
    APP_DISTR_R = RemRedRule(F_apply("?w", F_add("?u", "?v")), F_add(F_apply("?w", "?u"), F_apply("?w", "?v")), "", app_distr_sidecond, "(?u + ?v) is L-normal")
    rule_list.append(APP_DISTR_R)

    ### APP_SCALAR_L
    def app_scalar_sidecond(matcher : RemSubst) -> RemSubst | None:

        if not closed_L_normal(matcher["?u"]): # type: ignore
            return None
        
        return matcher

    APP_SCALAR_L = RemRedRule(F_apply(F_scalar("?c", "?u"), "?v"), F_scalar("?c", F_apply("?u", "?v")), "", app_scalar_sidecond, "?u is L-normal")
    rule_list.append(APP_SCALAR_L)

    ### APP_SCALAR_R
    APP_SCALAR_R = RemRedRule(F_apply("?v", F_scalar("?c", "?u")), F_scalar("?c", F_apply("?v", "?u")), "", app_scalar_sidecond, "?u is L-normal")
    rule_list.append(APP_SCALAR_R)

    ### APP_ZERO_L
    APP_ZERO_L = RemRedRule(F_apply(F_zero(), "?u"), F_zero())
    rule_list.append(APP_ZERO_L)

    ### APP_ZERO_R
    APP_ZERO_R = RemRedRule(F_apply("?u", F_zero()), F_zero())
    rule_list.append(APP_ZERO_R)

    ######################################################
    # Group B
    ### LINEAR_BETA
    def linear_beta_sidecond(matcher : RemSubst) -> RemSubst | None:
        N = matcher["?N"]
        assert isinstance(N, RemCons)

        if N.fun == F_abstract or N.fun == F_var:
            return matcher
        else:
            return None

    def linear_beta_RHS(matcher : RemSubst) -> RemTerm:
        x = matcher["?x"]
        M = matcher["?M"]
        N = matcher["?N"]
        assert isinstance(M, RemCons) and isinstance(x, RemCons) and isinstance(N, RemCons)
        
        return subst(M, x, N)

    LINEAR_BETA = RemRedRule(F_apply(F_abstract("?x", "?M"), "?N"), linear_beta_RHS, "?M[?N/?x]", linear_beta_sidecond, "?N is base vector")
    rule_list.append(LINEAR_BETA)


    TRS = RemTRS(rule_list, eq_check, eq_set)
    return TRS


############################################
# parser

def Parser_factory(m_uLC : ModuleTerm, m_WolComp : ModuleTerm, lineal_syn : ModuleTerm) -> PLYParser:


    F_var = m_uLC["F_var"]
    F_apply = m_uLC["F_apply"]
    F_abstract = m_uLC["F_abstract"]

    F_zero = lineal_syn["F_zero"]
    F_scalar = lineal_syn["F_scalar"]
    F_add = lineal_syn["F_add"]

    lexer = PLYLexer("lineal")
    lexer.fuse_append(m_WolComp["parser"].bound_plylexer)
    lexer.add_normal_token("LAMBDA", r"λ|\\lambda")
    lexer.add_normal_token("OPTZERO", r"𝟬|\\0")
    lexer.add_normal_token("ignore", " \t")
    lexer.add_normal_token("newline", syn.t_newline)

    lexer.add_literals({'*', '+'})
    lexer.add_literals({'(', ')'})
    lexer.add_literals({'.'})    
    lexer.add_ID_token()

    parser = PLYParser(lexer, "lineal", "lineal")
    parser.fuse_append(m_WolComp["parser"])


    def p_rule_uLC_term(p):
        '''
        lineal-term : '(' lineal-term ')'
                    | ID
                    | LAMBDA ID '.' lineal-term
                    | lineal-term lineal-term %prec APPLY
        '''
        if type_match(p, ('(', 'lineal-term', ')')):
            p[0] = p[2]
        elif type_match(p, ('ID',)):
            p[0] = F_var(name=p[1])
        elif type_match(p, ('LAMBDA', 'ID', '.', 'lineal-term')):
            p[0] = F_abstract(F_var(name=p[2]), p[4])
        elif type_match(p, ('lineal-term', 'lineal-term')):
            p[0] = F_apply(p[1], p[2])
        else:
            raise Exception()
    parser.set_precedence('.', 50, 'right')
    parser.set_precedence("APPLY", 40, "left") # TODO #20 this seesm not working.
    parser.add_rule(p_rule_uLC_term)


    ###################################
    # 

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

        "TRS"       : RemTRS,

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

    # TRS
    term["TRS"          ] = TRS_factory(lineal_syn, R_alpha_AC_eq)

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