

from ply.lex import TOKEN

from Rem import *

from .term import *
from .context import *
from .environment import *
from .typing_rule import *
from .conversion_rule import *


class RemCoC(REMTheory):
    def __init__(self):
        super().__init__()

        # terms
        self.Term = Term
        self.Sort = Sort
        self.SProp = SProp
        self.Prop = Prop
        self.Set = Set
        self.Type_i = Type_i
        self.Var = Var
        self.Const = Const
        self.BoundTerm = BoundTerm
        self.Prod = Prod
        self.Abstract = Abstract
        self.Apply = Apply
        self.Let_in = Let_in
        self.Rem_IsSort = Rem_IsSort

        # context
        self.LocalDec = LocalDec
        self.LocalTyping = LocalTyping
        self.LocalDef = LocalDef
        self.Context = Context
        self.Rem_Cont_Not_Contain_Var = Rem_Cont_Not_Contain_Var
        self.Rem_Cont_Contain_Var = Rem_Cont_Contain_Var
        self.Rem_Cont_Contain_Typing = Rem_Cont_Contain_Typing
        self.Rem_Cont_Contain_Def = Rem_Cont_Contain_Def

        # environment
        self.GlobalDec = GlobalDec
        self.GlobalTyping = GlobalTyping
        self.GlobalDef = GlobalDef
        self.Environment = Environment
        self.Rem_Env_Not_Contain_Const = Rem_Env_Not_Contain_Const
        self.Rem_Env_Contain_Const = Rem_Env_Contain_Const
        self.Rem_Env_Contain_Typing = Rem_Env_Contain_Typing
        self.Rem_Env_Contain_Def = Rem_Env_Contain_Def


        self.Rem_WF = Rem_WF
        self.Rem_WT = Rem_WT
        self.Rem_W_Empty = Rem_W_Empty
        self.Rem_W_Local_Assum = Rem_W_Local_Assum
        self.Rem_W_Local_Def = Rem_W_Local_Def
        self.Rem_W_Global_Assum = Rem_W_Global_Assum
        self.Rem_W_Global_Def = Rem_W_Global_Def
        self.Rem_Ax_SProp = Rem_Ax_SProp
        self.Rem_Ax_Prop = Rem_Ax_Prop
        self.Rem_Ax_Set = Rem_Ax_Set
        self.Rem_Ax_Type = Rem_Ax_Type
        self.Rem_Var = Rem_Var
        self.Rem_Const = Rem_Const
        self.Rem_Prod_SProp = Rem_Prod_SProp
        self.Rem_Prod_Prop = Rem_Prod_Prop
        self.Rem_Prod_Set = Rem_Prod_Set
        self.Rem_Prod_Type = Rem_Prod_Type
        self.Rem_Lam = Rem_Lam
        self.Rem_App = Rem_App
        self.Rem_Let = Rem_Let

        # conversion rules
        self.Rem_reduction = Rem_reduction
        self.Rem_beta_reduction = Rem_beta_reduction
        self.Rem_delta_reduction = Rem_delta_reduction
        self.Rem_Delta_reduction = Rem_Delta_reduction
        self.Rem_zeta_reduction = Rem_zeta_reduction
        self.Rem_eta_conversion = Rem_eta_conversion
        self.Rem_red_prod_T = Rem_red_prod_T
        self.Rem_red_prod_U = Rem_red_prod_U
        self.Rem_red_abstract_T = Rem_red_abstract_T
        self.Rem_red_abstract_u = Rem_red_abstract_u
        self.Rem_red_apply_t = Rem_red_apply_t
        self.Rem_red_apply_u = Rem_red_apply_u
        self.Rem_red_let_in_t = Rem_red_let_in_t
        self.Rem_red_let_in_T = Rem_red_let_in_T
        self.Rem_red_let_in_u = Rem_red_let_in_u
        self.Rem_red_seq = Rem_red_seq
        self.Rem_red_seq_refl = Rem_red_seq_refl
        self.Rem_red_seq_trans = Rem_red_seq_trans
        self.Rem_convertible = Rem_convertible
        self.Rem_subtyping = Rem_subtyping
        self.Rem_subtyping_trans = Rem_subtyping_trans
        self.Rem_subtyping_convert = Rem_subtyping_convert
        self.Rem_subtyping_universe = Rem_subtyping_universe
        self.Rem_subtyping_Set = Rem_subtyping_Set
        self.Rem_subtyping_Prop = Rem_subtyping_Prop
        self.Rem_subtyping_lam = Rem_subtyping_lam
        self.Rem_Conv = Rem_Conv


        ###################################################
        # lexing

        self.lexer.add_reserved("SPROP", "SProp")
        self.lexer.add_reserved("PROP", "Prop")
        self.lexer.add_reserved("SET", "Set")
        self.lexer.add_reserved("TYPE", "Type")
        self.lexer.add_reserved("LET", "let")
        self.lexer.add_reserved("IN", "in")
        self.lexer.add_reserved("CONST", "const")
        self.lexer.add_reserved('FORALL', 'forall')
        self.lexer.add_reserved('LAMBDA', 'lambda')

        self.lexer.add_literals(["(", ")", ":", ",", "."])

        # translate unicode expressions
        def t_UNICODE(t):
            r"∀|λ"
            if t == "∀":
                t.type = "FORALL"   # type: ignore
            elif t == "λ":
                t.type = "LAMBDA"   # type: ignore
            else:
                raise Exception()

        self.lexer.add_rule("UNICODE", t_UNICODE)
        self.lexer.add_rule("ASSIGN", r":=")
        self.lexer.add_rule("INT", syn.regex_INT)

        @TOKEN(syn.regex_ID)
        def t_ID(t):
            t.type = self.lexer.reserved.get(t.value, "ID")
            return t
        
        self.lexer.add_rule("ID", t_ID)


        self.lexer.add_rule("ignore", " \t")


        #################################################
        # parsing

        self.parser.set_precedence("PREC_APPLY", 99, "left")
        self.parser.set_precedence(":", 10, "nonassoc")
        self.parser.set_precedence(",", 10, "nonassoc")
        self.parser.set_precedence("IN", 1, "nonassoc")

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

        self.parser.add_rule(p_term)
            
        def p_var(p):
            '''
            var : ID
            '''
            p[0] = Var(p[1])

        self.parser.add_rule(p_var)


        # build the parser
        self.build_parser("term")


