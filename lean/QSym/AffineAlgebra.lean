import QSym.RefinementBase

namespace QSym.Value
variable {R : Type} [CommSemiring R]

theorem affine_add (a b c d x : Option R) :
    add (add (mul a x) b) (add (mul c x) d) = add (mul (add a c) x) (add b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;>
    simp [add, mul] <;> ring

theorem affine_left (c a b x : Option R) :
    mul c (add (mul a x) b) = add (mul (mul c a) x) (mul c b) := by
  cases c <;> cases a <;> cases b <;> cases x <;>
    simp [add, mul] <;> ring

theorem affine_right (a b c x : Option R) :
    mul (add (mul a x) b) c = add (mul (mul a c) x) (mul b c) := by
  cases a <;> cases b <;> cases c <;> cases x <;>
    simp [add, mul] <;> ring

end QSym.Value
