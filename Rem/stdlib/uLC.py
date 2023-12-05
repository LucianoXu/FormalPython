'''
untyped lambda calculus
'''

from ..core import *




Term = RemSort("Term")

##############################
# variable

Var = RemSort("Var", {"name" : str}, (Term,))

F_var = RemFun("f_var", (), Term, {"name" : str})
F_var.rule_doc = " x "

def __term_str_F_var(term : RemCons):
    return term["name"]

F_var.term_str = __term_str_F_var

##############################
# abstraction

F_abstract = RemFun("f_abstract", (Var, Term), Term)
F_abstract.rule_doc = " λx.M"
F_abstract.set_para_doc("x", "M")
F_abstract.attr_extract["x"] = lambda term : term.paras[0]
F_abstract.attr_extract["M"] = lambda term : term.paras[1]

F_abstract.set_precedence(50, 'nonassoc')

def __term_str_F_abstract(term : RemCons):
    return f"λ{term['x'].ctx_term_str(term.fun, True)}.{term['M'].ctx_term_str(term.fun, False)}"

F_abstract.term_str = __term_str_F_abstract

##############################
# application

F_apply = RemFun("f_apply", (Term, Term), Term)

F_apply.rule_doc = "M N"
F_apply.set_para_doc("M", "N")
F_apply.attr_extract["M"] = lambda term : term.paras[0]
F_apply.attr_extract["N"] = lambda term : term.paras[1]

F_apply.set_precedence(40, 'right')

def __term_str_F_apply(term : RemCons):
    return f"{term['M'].ctx_term_str(term.fun, True)} {term['N'].ctx_term_str(term.fun, False)}"

F_apply.term_str = __term_str_F_apply


###################################################
#

M_uLC = ModuleSort("M_uLC",
    {
        "Term" : RemSort,
        "Var" : RemSort,
    })

F_uLC = ModuleFun("F_uLC", (), M_uLC)

def __modify_F_uLC(term : ModuleCons, *paras, **kwparas):
    term["Term"] = Term
    term["Var"] = Var

F_uLC.modify = __modify_F_uLC

###################################################
# parser

lexer = PLYLexer("uLC")
lexer.add_normal_token("LAMBDA", r"λ")
lexer.add_normal_token("ignore", " \t")

lexer.add_ID_token()
parser = PLYParser(lexer, "uLC", "uLC")

lexer.add_literals({'(', ')'})
lexer.add_literals({'.'})
def __p_rule_term(p):
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

parser.add_rule(__p_rule_term)
parser.set_precedence('.', 50, 'right')
parser.set_precedence("APPLY", 40, "nonassoc")
parser.add_subterm("uLC", "uLC-term")
