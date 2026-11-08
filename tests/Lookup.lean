import QSym

open QSym.Replay

private def values : Lookup Nat := .node (.node (.leaf 11) (.leaf 33)) (.leaf 22)

example : values.get 0 0=11 := rfl
example : values.get 0 1=22 := rfl
example : values.get 0 2=33 := rfl
example : values.get 0 3=0 := rfl
example : values.get 0 4=0 := rfl
example : values.get 0 1000003=0 := rfl
example : (Lookup.empty : Lookup Nat).get 7 0=7 := rfl
example : (Lookup.leaf 11).get 7 1=7 := rfl
