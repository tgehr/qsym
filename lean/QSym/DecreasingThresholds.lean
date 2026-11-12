import QSym.RefinementBase

namespace QSym.Value

private theorem refines_decreasing_center (f : Function1 ℝ ℝ)
    (hf : FunctionOrder.Decreasing f) (h0 : f.domain 0) (c : ℝ) (hc : f.value 0=c)
    (x : Option ℝ) :
    Refines (Functions.signR.apply (add (f.apply x) (mul (some (-1)) (some c))))
      (Functions.signR.apply (mul (some (-1)) x)) := by
  cases x with
  | none => simp [Refines, Function1.apply, add, mul]
  | some x =>
    by_cases hx : f.domain x
    · have hn : f.value x<c ↔ 0<x := by simpa only [hc] using hf.lt_iff_lt hx h0
      have hp : c<f.value x ↔ x<0 := by simpa only [hc] using hf.lt_iff_lt h0 hx
      simp [Refines, Function1.apply, Functions.signR, add, mul, hx, ← sub_eq_add_neg, sub_neg, sub_pos, hn, hp]
    · simp [Refines, Function1.apply, add, mul, hx]

private theorem refines_center_decreasing (f : Function1 ℝ ℝ)
    (hf : FunctionOrder.Decreasing f) (h0 : f.domain 0) (c : ℝ) (hc : f.value 0=c)
    (x : Option ℝ) :
    Refines (Functions.signR.apply (add (some c) (mul (some (-1)) (f.apply x))))
      (Functions.signR.apply x) := by
  cases x with
  | none => simp [Refines, Function1.apply, add, mul]
  | some x =>
    by_cases hx : f.domain x
    · have hn : f.value x<c ↔ 0<x := by simpa only [hc] using hf.lt_iff_lt hx h0
      have hp : c<f.value x ↔ x<0 := by simpa only [hc] using hf.lt_iff_lt h0 hx
      simp [Refines, Function1.apply, Functions.signR, add, mul, hx, ← sub_eq_add_neg, sub_neg, sub_pos, hn, hp]
    · simp [Refines, Function1.apply, add, mul, hx]

theorem refines_sign_acos_half_pi (x : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.acosR.apply x)
      (mul (some (((-1:ℚ)/2:ℚ):ℝ)) (some Functions.pi))))
      (Functions.signR.apply (mul (some (-1)) x)) := by
  have h := refines_decreasing_center Functions.acosR FunctionOrder.acos
    (by norm_num [Functions.acosR]) ((((1:ℚ)/2:ℚ):ℝ)*Functions.pi)
    (by norm_num [Functions.acosR, Functions.pi, Real.arccos_zero, div_eq_mul_inv, mul_comm]) x
  simpa [mul, neg_mul, div_eq_mul_inv] using h

theorem refines_sign_half_pi_acos (x : Option ℝ) :
    Refines (Functions.signR.apply (add (some ((((1:ℚ)/2:ℚ):ℝ)*Functions.pi)) (mul (some (-1)) (Functions.acosR.apply x)))) (Functions.signR.apply x) := by
  apply refines_center_decreasing Functions.acosR FunctionOrder.acos
  · norm_num [Functions.acosR]
  · norm_num [Functions.acosR, Functions.erfR, Functions.pi, Real.arccos_zero, div_eq_mul_inv, mul_comm]

theorem refines_sign_erfc_minus_one (x : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.erfcR.apply x) (mul (some (-1)) (some 1)))) (Functions.signR.apply (mul (some (-1)) x)) := by
  apply refines_decreasing_center Functions.erfcR FunctionOrder.erfc
  · norm_num [Functions.erfcR]
  · norm_num [Functions.erfcR, Functions.erfR, Functions.pi, Real.arccos_zero, div_eq_mul_inv, mul_comm]

theorem refines_sign_one_minus_erfc (x : Option ℝ) :
    Refines (Functions.signR.apply (add (some 1) (mul (some (-1)) (Functions.erfcR.apply x)))) (Functions.signR.apply x) := by
  apply refines_center_decreasing Functions.erfcR FunctionOrder.erfc
  · norm_num [Functions.erfcR]
  · norm_num [Functions.erfcR, Functions.erfR, Functions.pi, Real.arccos_zero, div_eq_mul_inv, mul_comm]

end QSym.Value
