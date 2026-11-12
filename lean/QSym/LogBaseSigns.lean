import QSym.RefinementBase

namespace QSym.Value

private theorem sign_log_base (b x : ℝ) (hb : 1<b) (hx : 0<x) :
    Functions.signR.value (Real.log x / Real.log b)=Functions.signR.value (x-1) := by
  have h := Real.log_pos hb
  simp [Functions.signR, div_neg_iff, div_pos_iff, h, not_lt_of_ge h.le,
    Real.log_neg_iff hx, Real.log_pos_iff hx.le, sub_neg, sub_pos]

private theorem refines_sign_log_base (b : ℝ) (hb : 1<b) (x : Option ℝ) :
    Refines (Functions.signR.apply ((⟨fun x => Real.log x / Real.log b, fun x => 0<x⟩ : Function1 ℝ ℝ).apply x))
      (Functions.signR.apply (add x (mul (some (-1)) (some 1)))) := by
  cases x with
  | none => simp [Refines, Function1.apply, add, mul]
  | some x =>
    by_cases hx : 0<x
    · have h := sign_log_base b x hb hx
      simpa [Refines, Function1.apply, Functions.signR, add, mul, hx, ← sub_eq_add_neg] using h.symm
    · simp [Refines, Function1.apply, hx]

private theorem refines_sign_logbase_increasing_pair (f : Function1 ℝ ℝ)
    (hf : FunctionOrder.Increasing f) (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (f.apply x) (mul (some (-1)) (f.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) := by
  cases x with
  | none => simp [Refines, Function1.apply, add, mul]
  | some x =>
    cases y with
    | none => simp [Refines, Function1.apply, add, mul]
    | some y =>
      by_cases hx : f.domain x
      · by_cases hy : f.domain y
        · simp [Refines, Function1.apply, add, mul, Functions.signR, hx, hy,
            ← sub_eq_add_neg, sub_neg, sub_pos, hf.lt_iff_lt hx hy, hf.lt_iff_lt hy hx]
        · simp [Refines, Function1.apply, add, mul, hy]
      · simp [Refines, Function1.apply, add, mul, hx]

theorem refines_sign_log2 (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.log2R.apply x))
      (Functions.signR.apply (add x (mul (some (-1)) (some 1)))) :=
  refines_sign_log_base 2 (by norm_num) x

theorem refines_sign_log2_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.log2R.apply x) (mul (some (-1)) (Functions.log2R.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) := by
  apply refines_sign_logbase_increasing_pair
  intro x hx y _ hxy
  exact (div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr (Real.log_lt_log hx hxy)

theorem refines_sign_log10 (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.log10R.apply x))
      (Functions.signR.apply (add x (mul (some (-1)) (some 1)))) :=
  refines_sign_log_base 10 (by norm_num) x

theorem refines_sign_log10_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.log10R.apply x) (mul (some (-1)) (Functions.log10R.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) := by
  apply refines_sign_logbase_increasing_pair
  intro x hx y _ hxy
  exact (div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num : (1:ℝ)<10))).mpr (Real.log_lt_log hx hxy)

end QSym.Value
