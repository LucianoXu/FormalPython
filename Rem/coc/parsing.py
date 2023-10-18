'''
The parsing rules.
'''


from ply.lex import TOKEN

from .core import *


###################################################
# lexing

rem_coc.lexer_reserved("SPROP", "SProp")
rem_coc.lexer_reserved("PROP", "Prop")
rem_coc.lexer_reserved("SET", "Set")
rem_coc.lexer_reserved("TYPE", "Type")
rem_coc.lexer_reserved("LET", "let")
rem_coc.lexer_reserved("IN", "in")
rem_coc.lexer_reserved("CONST", "const")
rem_coc.lexer_reserved('FORALL', 'forall')
rem_coc.lexer_reserved('LAMBDA', 'lambda')

rem_coc.lexer_literals(["(", ")", ":", ",", "."])

# translate unicode expressions
def t_UNICODE(t):
    r"∀|λ"
    if t == "∀":
        t.type = "FORALL"
    elif t == "λ":
        t.type = "LAMBDA"
    else:
        raise Exception()


rem_coc.lexer_token("UNICODE", t_UNICODE)
rem_coc.lexer_token("ASSIGN", r":=")
rem_coc.lexer_token("INT", syn.regex_INT)

@TOKEN(syn.regex_ID)
def t_ID(t):
    t.type = rem_coc.lexer.reserved.get(t.value, "ID")
    return t
rem_coc.lexer_token("ID", t_ID)


rem_coc.lexer_token("ignore", " \t")


#################################################
# parsing

rem_coc.parser_set_precedence("PREC_APPLY", 99, "left")
rem_coc.parser_set_precedence(":", 10, "nonassoc")
rem_coc.parser_set_precedence(",", 10, "nonassoc")
rem_coc.parser_set_precedence("IN", 1, "nonassoc")

def p_term(p):
    '''
    term    : SPROP
            | PROP
            | SET
            | TYPE '(' INT ')'
            | var
            | CONST ID
            | FORALL var ':' term ',' term
            | LAMBDA var ':' term ',' term
            | term term %prec PREC_APPLY
            | LET var ASSIGN term ':' term IN term
            | '(' term ')'
            
    '''
    if syn.type_match(p, ("SPROP",)):
        p[0] = SProp()
    elif syn.type_match(p, ("PROP",)):
        p[0] = Prop()
    elif syn.type_match(p, ("SET",)):
        p[0] = Set()
    elif syn.type_match(p, ('TYPE', '(', 'INT', ')')):
        p[0] = Type_i(int(p[3]))
    elif syn.type_match(p, ("var",)):
        p[0] = p[1]
    elif syn.type_match(p, ("CONST", "ID")):
        p[0] = Const(p[2])
    elif syn.type_match(p, ("FORALL", "var", ":", "term", ",", "term")):
        p[0] = Prod(p[2], p[4], p[6])
    elif syn.type_match(p, ("LAMBDA", "var", ":", "term", ",", "term")):
        p[0] = Abstract(p[2], p[4], p[6])
    elif syn.type_match(p, ("term", "term")):
        p[0] = Apply(p[1], p[2])
    elif syn.type_match(p, ("LET", "var", "ASSIGN", "term", ':', "term", "IN", "term")):
        p[0] = Let_in(p[2], p[4], p[6], p[8])

    elif syn.type_match(p, ("(", "term", ")")):
        p[0] = p[2]
rem_coc.parser_rule(p_term)
    
def p_var(p):
    '''
    var : ID
    '''
    p[0] = Var(p[1])
rem_coc.parser_rule(p_var)


