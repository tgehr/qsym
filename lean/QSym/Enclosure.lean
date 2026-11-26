import QSym.RefinementBase
import Mathlib.Data.Real.Pi.Bounds

noncomputable section

namespace QSym.Enclosure
open Real

theorem pi_low : (3141592:ℝ)/1000000 < π := by linarith [Real.pi_gt_d6]
theorem pi_high : π < (3141593:ℝ)/1000000 := by linarith [Real.pi_lt_d6]
theorem inv_pi_low : (1000000:ℝ)/3141593 < π⁻¹ := by
  rw [inv_eq_one_div, div_lt_div_iff₀ (by norm_num) Real.pi_pos]
  linarith [pi_high]
theorem inv_pi_high : π⁻¹ < (1000000:ℝ)/3141592 := by
  rw [inv_eq_one_div, div_lt_div_iff₀ Real.pi_pos (by norm_num)]
  linarith [pi_low]

/-- If an affine function has the same weak sign at both endpoints, its
sign inside the open interval is the sign of the sum of the endpoint values. -/
theorem affine_order {a b t l u : ℝ} (hl : l < t) (hu : t < u)
    (hs : 0 ≤ (a*l+b)*(a*u+b)) :
    (0 < a*t+b ↔ 0 < (a*l+b)+(a*u+b)) ∧ (0 ≤ a*t+b ↔ 0 ≤ (a*l+b)+(a*u+b)) := by
  by_cases h : a = 0
  · subst a; simp only [zero_mul, zero_add]; constructor <;> constructor <;> intro h <;> linarith
  have between : (a*l+b < a*t+b ∧ a*t+b < a*u+b) ∨ (a*u+b < a*t+b ∧ a*t+b < a*l+b) := by
    rcases lt_or_gt_of_ne h with hn | hp
    · exact Or.inr ⟨add_lt_add_right (mul_lt_mul_of_neg_left hu hn) _, add_lt_add_right (mul_lt_mul_of_neg_left hl hn) _⟩
    · exact Or.inl ⟨add_lt_add_right (mul_lt_mul_of_pos_left hl hp) _, add_lt_add_right (mul_lt_mul_of_pos_left hu hp) _⟩
  rcases mul_nonneg_iff.mp hs with hp | hn <;> rcases between with dir | dir <;>
    constructor <;> constructor <;> intro h <;> linarith [dir.1, dir.2]

private def compare (strict : Bool) := if strict then Value.lt else Value.le

theorem compare_affine (strict : Bool) (x y a b t l u : Option ℝ)
    (eq : Value.Refines (Value.not (Value.nonzero (Value.add (Value.add y (Value.mul (some (((-1) : Int) : ℝ)) x))
      (Value.mul (some (((-1) : Int) : ℝ)) (Value.add (Value.mul a t) b))))) (some true))
    (hl : Value.Refines (Value.lt l t) (some true)) (hu : Value.Refines (Value.lt t u) (some true))
    (side : Value.Refines (Value.le (some ((0 : Int) : ℝ)) (Value.mul (Value.add (Value.mul a l) b)
      (Value.add (Value.mul a u) b))) (some true))
    (da : Value.Defined a) (db : Value.Defined b) (dt : Value.Defined t)
    (dl : Value.Defined l) (du : Value.Defined u) :
    Value.Refines (compare strict x y) (compare strict (some ((0 : Int) : ℝ))
      (Value.add (Value.add (Value.mul a l) b) (Value.add (Value.mul a u) b))) := by
  obtain ⟨a, rfl⟩ := da
  obtain ⟨b, rfl⟩ := db
  obtain ⟨t, rfl⟩ := dt
  obtain ⟨l, rfl⟩ := dl
  obtain ⟨u, rfl⟩ := du
  cases x with
  | none => cases strict <;> simp [compare, Value.lt, Value.le, Value.Refines]
  | some x =>
    cases y with
    | none => cases strict <;> simp [compare, Value.lt, Value.le, Value.Refines]
    | some y =>
      simp [Value.Refines, Value.not, Value.nonzero, Value.lt, Value.le, Value.add, Value.mul] at eq hl hu side
      have diff : y - x = a*t + b := by linarith
      obtain ⟨lt, le⟩ := affine_order hl hu side
      have elt := (sub_pos (a := y) (b := x)).symm.trans (diff ▸ lt)
      have ele := (sub_nonneg (a := y) (b := x)).symm.trans (diff ▸ le)
      cases strict <;> simp [compare, Value.Refines, Value.lt, Value.le, Value.mul, Value.add, elt, ele]

end QSym.Enclosure
