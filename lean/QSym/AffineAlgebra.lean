import QSym.RefinementBase

namespace QSym.Value
variable {R : Type} [CommSemiring R]

theorem spectral_interpolation (a b p q z : Option R) :
    mul (add (mul a p) (mul b q)) z = add (mul (mul a z) p) (mul (mul b z) q) := by
  cases a <;> cases b <;> cases p <;> cases q <;> cases z <;>
    simp [add, mul] <;> ring

theorem spectral_interpolationQ (a b p q z : Option ℚ) :
    Functions.mulQ.apply (Functions.addQ.apply (Functions.mulQ.apply a p) (Functions.mulQ.apply b q)) z =
      Functions.addQ.apply (Functions.mulQ.apply (Functions.mulQ.apply a z) p)
        (Functions.mulQ.apply (Functions.mulQ.apply b z) q) := by
  cases a <;> cases b <;> cases p <;> cases q <;> cases z <;>
    simp [Function2.apply, Functions.addQ, Functions.mulQ] <;> ring

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
