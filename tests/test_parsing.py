from Rem.coc import *

def test_01():
    print(rem_coc.parser("forall x : SProp, forall a : Prop , Type(1)"))
    print(rem_coc.parser("(a b) (c d)"))
    print(rem_coc.parser("let x := Prop : x in Prop"))