'''
untyped lambda calculus
'''

from ..core import *

from types import FunctionType



##############################
# term

def S_Term_factory() -> RemSort:
    return RemSort("Term")


##############################
# variable

def S_Var_factory(Term : RemSort) -> RemSort:
    S = RemSort("Var", {"name" : str}, (Term,))

    def term_str(term : RemCons):
        return term["name"]
    
    S.term_str = term_str

    return S

def F_var_factory(Var : RemSort) -> RemFun:
    F = RemFun("f_var", (), Var, {"name" : str})
    F.rule_doc = " x "

    return F


##############################
# abstraction

def F_abstract_factory(Term : RemSort, Var : RemSort) -> RemFun:

    F = RemFun("f_abstract", (Var, Term), Term)
    F.rule_doc = " λx.M"
    F.set_para_doc("x", "M")
    F.attr_extract["x"] = lambda term : term.paras[0]
    F.attr_extract["M"] = lambda term : term.paras[1]

    F.set_precedence(50, 'nonassoc')

    def term_str(term : RemCons):
        return f"λ{term['x'].ctx_term_str(term.fun, True)}.{term['M'].ctx_term_str(term.fun, False)}"

    F.term_str = term_str

    return F


##############################
# application

def F_apply_factory(Term : RemSort) -> RemFun:

    F = RemFun("f_apply", (Term, Term), Term)

    F.rule_doc = "M N"
    F.set_para_doc("M", "N")
    F.attr_extract["M"] = lambda term : term.paras[0]
    F.attr_extract["N"] = lambda term : term.paras[1]

    F.set_precedence(40, 'left')

    def term_str(term : RemCons):
        return f"{term['M'].ctx_term_str(term.fun, True)} {term['N'].ctx_term_str(term.fun, False)}"

    F.term_str = term_str

    return F





##################################################
# the syntax-only uLC module


M_uLC_syn = ModuleSort("M_uLC_syn",
    {
        "Term" : RemSort,
        "Var" : RemSort,

        "F_var" : RemFun,
        "F_abstract" : RemFun,
        "F_apply" : RemFun,

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


MF_uLC_syn = ModuleFun("F_uLC_syn", (), M_uLC_syn)
def __modify_F_uLC_syn(term : ModuleCons, *paras, **kwparas):

    Term = S_Term_factory()
    term["Term"] = Term

    Var = S_Var_factory(Term)
    term["Var"] = Var

    F_var = F_var_factory(Var)
    term["F_var"] = F_var

    F_abstract = F_abstract_factory(Term, Var)
    term["F_abstract"] = F_abstract

    F_apply = F_apply_factory(Term)
    term["F_apply"] = F_apply

    def vars_of(term : RemCons) -> set[str]:
        if term.fun == F_var:
            return {term["name"]}
        elif term.fun == F_abstract:
            return {term["x"]} | vars_of(term["M"])
        elif term.fun == F_apply:
            return vars_of(term["M"]) | vars_of(term["N"])
        else:
            raise REM_CONSTRUCTION_Error("Not allowed.")
    term["vars_of"] = vars_of

    def subst(M : RemCons, x : RemCons, N : RemCons) -> RemCons:
        '''
        calculate the substitution `M[N/x]` and return the result.
        '''
        if M.fun == F_var:
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

    def freshvar(vset : set[str]) -> RemCons:
        i = 0
        while True:
            newvar = "x" + str(i)
            i += 1
            if newvar not in vset:
                break
        return F_var(name=newvar)
    
    term["freshvar"] = freshvar


MF_uLC_syn.modify = __modify_F_uLC_syn


###################################
# alpha-equivalence

def P_alpha_eq_factory(Term : RemSort) -> ProofSort:
    P = ProofSort("alpha_eq", {"t1" : Term, "t2" : Term})

    def term_str(term : RemCons):
        return f"{term['t1']} = {term['t2']}"
    
    P.term_str = term_str
    return P

def R_alpha_eq_factory(uLC_syn : ModuleTerm,  P_alpha_eq : ProofSort) -> ProofFun:
    Term = uLC_syn["Term"]
    F_var = uLC_syn["F_var"]
    F_apply = uLC_syn["F_apply"]
    F_abstract = uLC_syn["F_abstract"]

    vars_of = uLC_syn["vars_of"]
    subst = uLC_syn["subst"]
    freshvar = uLC_syn["freshvar"]


    R = ProofFun("PF_alpha_eq", (Term, Term), P_alpha_eq)

    R.rule_doc = " (automatic check) ⊢ t1 = t2"
    R.set_para_doc("t1", "t2")

    R.attr_extract["t1"] = lambda term : term.paras[0]
    R.attr_extract["t2"] = lambda term : term.paras[1]

    def extra_check(fun : RemFun, *paras, **kwparas):
        t1 = paras[0]
        t2 = paras[1]

        if isinstance(t1, RemCons) and isinstance(t2, RemCons):
            if t1.fun == t2.fun:
                if t1.fun == F_var:
                    if t1["name"] == t2["name"]:
                        return
                    else:
                        raise REM_CONSTRUCTION_Error("Variable not identical.")
                
                if t1.fun == F_apply:
                    R(t1["M"], t2["M"])
                    R(t1["N"], t2["N"])
                    return
                
                # alpha-conversion comes in
                if t1.fun == F_abstract:
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

# renaming needed

def TRS_factory(uLC_syn : ModuleTerm) -> RemTRS:
    F_var = uLC_syn["F_var"]
    F_apply = uLC_syn["F_apply"]
    F_abstract = uLC_syn["F_abstract"]
    subst = uLC_syn["subst"]

    def Beta_RHS(matcher : RemSubst) -> RemTerm:
        x = matcher["?x"]
        M = matcher["?M"]
        N = matcher["?N"]
        assert isinstance(M, RemCons) and isinstance(x, RemCons) and isinstance(N, RemCons)
        
        return subst(M, x, N)


    Beta = RemRedRule(F_apply(F_abstract("?x", "?M"), "?N"), Beta_RHS, "?M[?N/?x]")

    return RemTRS([Beta])


###################################################
# parser

def Parser_factory(uLC_syn : ModuleTerm) -> PLYParser:
    F_var = uLC_syn["F_var"]
    F_apply = uLC_syn["F_apply"]
    F_abstract = uLC_syn["F_abstract"]

    lexer = PLYLexer("uLC")
    lexer.add_normal_token("LAMBDA", r"λ|\\lambda")
    lexer.add_normal_token("ignore", " \t")

    lexer.add_ID_token()
    parser = PLYParser(lexer, "uLC", "uLC")

    lexer.add_literals({'(', ')'})
    lexer.add_literals({'.'})
    def p_rule_term(p):
        '''
        uLC-term    : '(' uLC-term ')'
                    | ID
                    | LAMBDA ID '.' uLC-term
                    | uLC-term uLC-term %prec APPLY
        '''
        if type_match(p, ('(', 'uLC-term', ')')):
            p[0] = p[2]
        elif type_match(p, ('ID',)):
            p[0] = F_var(name=p[1])
        elif type_match(p, ('LAMBDA', 'ID', '.', 'uLC-term')):
            p[0] = F_abstract(F_var(name=p[2]), p[4])
        elif type_match(p, ('uLC-term', 'uLC-term')):
            p[0] = F_apply(p[1], p[2])
        else:
            raise Exception()

    parser.add_rule(p_rule_term)
    parser.set_precedence('.', 50, 'right')
    parser.set_precedence("APPLY", 40, "left") # TODO #20 this seesm not working.
    parser.add_subterm("uLC", "uLC-term")

    return parser



M_uLC = ModuleSort("M_uLC",
    {
        "Term" : RemSort,
        "Var" : RemSort,

        "F_var" : RemFun,
        "F_abstract" : RemFun,
        "F_apply" : RemFun,

        "P_eq"  :   ProofSort,
        "R_eq" :   ProofFun,

        "TRS" : RemTRS,

        "parser" : PLYParser,
    })


MF_uLC = ModuleFun("F_uLC", (), M_uLC)
def __modify_F_uLC(term : ModuleCons, *paras, **kwparas):

    uLC_syn = MF_uLC_syn()

    term["Term"] = uLC_syn["Term"]
    term["Var"] = uLC_syn["Var"]
    term["F_var"] = uLC_syn["F_var"]
    term["F_abstract"] = uLC_syn["F_abstract"]
    term["F_apply"] = uLC_syn["F_apply"]

    P_alpha_eq = P_alpha_eq_factory(uLC_syn["Term"])
    term["P_eq"] = P_alpha_eq

    R_alpha_eq = R_alpha_eq_factory(uLC_syn, P_alpha_eq)
    term["R_eq"] = R_alpha_eq

    uLC_TRS = TRS_factory(uLC_syn)
    term["TRS"] = uLC_TRS

    parser = Parser_factory(uLC_syn)
    parser.build()
    term["parser"] = parser

MF_uLC.modify = __modify_F_uLC


def build() -> RemVTerm:
    '''
    build and verify the system
    '''
    return RemVTerm.verify(MF_uLC())



