import QSym.Domain

namespace QSym
namespace Value

def ite {α : Type} : Option Bool → Option α → Option α → Option α
  | some true, x, _ => x
  | some false, _, y => y
  | none, _, _ => none

theorem ite_masks {α : Type} [AddZeroClass α] (p : Option Bool) (x y : Option α) :
    ite p x y = add (mask p x) (mask (not p) y) := by
  cases p with
  | none => rfl
  | some p => cases p <;> cases x <;> cases y <;> simp [ite, add, mask, not]

theorem ite_booleans (p x y : Option Bool) :
    ite p x y = or (and p x) (and (not p) y) := by
  cases p with
  | none => rfl
  | some p =>
    cases p
    · rfl
    · cases x with
      | none => rfl
      | some x => cases x <;> rfl

end Value
namespace Domain

theorem conditional {α : Type} {p : Option Bool} {x y : Option α} {dp dx dy : Option Bool}
    (hp : Correct p dp) (hx : Correct x dx) (hy : Correct y dy) :
    Correct (Value.ite p x y)
      (Value.and dp (Value.or (Value.and p dx) (Value.and (Value.not p) dy))) := by
  cases p with
  | none => simp_all [Correct, Value.ite, Value.and]
  | some p => cases p <;> cases x <;> cases y <;> simp_all [Correct, Value.ite, Value.and, Value.or, Value.not]

end Domain
end QSym
