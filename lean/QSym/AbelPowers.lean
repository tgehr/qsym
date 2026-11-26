import QSym.RefinementBase

namespace QSym.Value

theorem powerR_add_pos (x y z : Option ℝ)
    (h : Refines (lt (some (((0 : Int) : ℝ))) x) (some true)) :
    Functions.powerR.apply x (add y z) =
      mul (Functions.powerR.apply x y) (Functions.powerR.apply x z) := by
  classical
  cases x with
  | none => cases y <;> cases z <;> rfl
  | some x =>
    have hx : 0 < x := by simpa [Refines, lt] using h
    cases y <;> cases z <;>
      simp [Functions.powerR, Function2.apply, add, mul, hx, Real.rpow_add]

/-- With two nonnegative bases, the real powers on both sides have the same
domain, including exponent zero and a zero base with a negative exponent. -/
theorem powerR_mul_nonneg (x y t : Option ℝ)
    (hx : Refines (le (some (((0 : Int) : ℝ))) x) (some true)) (hy : Refines (le (some (((0 : Int) : ℝ))) y) (some true)) :
    mul (Functions.powerR.apply x t) (Functions.powerR.apply y t) = Functions.powerR.apply (mul x y) t := by
  classical
  cases x with
  | none => rfl
  | some x =>
    cases y with
    | none => cases Functions.powerR.apply (some x) t <;> rfl
    | some y =>
      cases t with
      | none => rfl
      | some t =>
        have x0 : 0 ≤ x := by simpa [Refines, le] using hx
        have y0 : 0 ≤ y := by simpa [Refines, le] using hy
        have dom (a : ℝ) (ha : 0 ≤ a) : Functions.powerR.domain a t ↔ a ≠ 0 ∨ 0 ≤ t := by
          rcases ha.eq_or_lt with e | p
          · subst a; simp [Functions.powerR]
          · simp [Functions.powerR, p, p.ne']
        change _ = Functions.powerR.apply (some (x*y)) (some t)
        simp only [Function2.apply, Option.some_bind, dom x x0, dom y y0, dom _ (mul_nonneg x0 y0)]
        by_cases ht : 0 ≤ t
        · simp [ht, Functions.powerR, mul, Real.mul_rpow x0 y0]
        · by_cases ex : x=0 <;> by_cases ey : y=0 <;>
            simp [ht, ex, ey, Functions.powerR, mul, Real.mul_rpow x0 y0]

end QSym.Value
