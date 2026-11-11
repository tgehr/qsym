import QSym.RefinementBase

namespace QSym.FunctionOrder

theorem exponential : Increasing Functions.expR := Real.exp_strictMono.strictMonoOn _
theorem logarithm : Increasing Functions.logR := by
  intro x hx y _ h
  exact Real.log_lt_log hx h
theorem squareRoot : Increasing Functions.sqrtR := by
  intro x hx y _ h
  exact Real.sqrt_lt_sqrt hx h

end QSym.FunctionOrder

namespace QSym.Value

theorem refines_min_increasing {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (hf : FunctionOrder.Increasing f) :
    Refines (Functions.minR.apply (f.apply x) (f.apply y))
      (f.apply (Functions.minR.apply x y)) := by
  classical
  cases x with
  | none => simp [Refines, Function1.apply, Function2.apply]
  | some x =>
    cases y with
    | none => simp [Refines, Function1.apply, Function2.apply]
    | some y =>
      by_cases hx : f.domain x
      · by_cases hy : f.domain y
        · rcases le_total x y with h | h
          · have hm := hf.monotoneOn hx hy h
            apply refines_of_eq
            simp [Function1.apply, Function2.apply, Functions.minR, Functions.maxR,
              min_eq_left h, max_eq_right h, min_eq_left hm, max_eq_right hm, hx, hy]
          · have hm := hf.monotoneOn hy hx h
            apply refines_of_eq
            simp [Function1.apply, Function2.apply, Functions.minR, Functions.maxR,
              min_eq_right h, max_eq_left h, min_eq_right hm, max_eq_left hm, hx, hy]
        · simp [Refines, Function1.apply, Function2.apply, hx, hy]
      · simp [Refines, Function1.apply, Function2.apply, hx]

theorem refines_min_decreasing {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (hf : FunctionOrder.Decreasing f) :
    Refines (Functions.minR.apply (f.apply x) (f.apply y))
      (f.apply (Functions.maxR.apply x y)) := by
  classical
  cases x with
  | none => simp [Refines, Function1.apply, Function2.apply]
  | some x =>
    cases y with
    | none => simp [Refines, Function1.apply, Function2.apply]
    | some y =>
      by_cases hx : f.domain x
      · by_cases hy : f.domain y
        · rcases le_total x y with h | h
          · have hm := hf.antitoneOn hx hy h
            apply refines_of_eq
            simp [Function1.apply, Function2.apply, Functions.minR, Functions.maxR,
              min_eq_left h, max_eq_right h, min_eq_right hm, max_eq_left hm, hx, hy]
          · have hm := hf.antitoneOn hy hx h
            apply refines_of_eq
            simp [Function1.apply, Function2.apply, Functions.minR, Functions.maxR,
              min_eq_right h, max_eq_left h, min_eq_left hm, max_eq_right hm, hx, hy]
        · simp [Refines, Function1.apply, Function2.apply, hx, hy]
      · simp [Refines, Function1.apply, Function2.apply, hx]

theorem refines_max_increasing {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (hf : FunctionOrder.Increasing f) :
    Refines (Functions.maxR.apply (f.apply x) (f.apply y))
      (f.apply (Functions.maxR.apply x y)) := by
  classical
  cases x with
  | none => simp [Refines, Function1.apply, Function2.apply]
  | some x =>
    cases y with
    | none => simp [Refines, Function1.apply, Function2.apply]
    | some y =>
      by_cases hx : f.domain x
      · by_cases hy : f.domain y
        · rcases le_total x y with h | h
          · have hm := hf.monotoneOn hx hy h
            apply refines_of_eq
            simp [Function1.apply, Function2.apply, Functions.minR, Functions.maxR,
              min_eq_left h, max_eq_right h, min_eq_left hm, max_eq_right hm, hx, hy]
          · have hm := hf.monotoneOn hy hx h
            apply refines_of_eq
            simp [Function1.apply, Function2.apply, Functions.minR, Functions.maxR,
              min_eq_right h, max_eq_left h, min_eq_right hm, max_eq_left hm, hx, hy]
        · simp [Refines, Function1.apply, Function2.apply, hx, hy]
      · simp [Refines, Function1.apply, Function2.apply, hx]

theorem refines_max_decreasing {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (hf : FunctionOrder.Decreasing f) :
    Refines (Functions.maxR.apply (f.apply x) (f.apply y))
      (f.apply (Functions.minR.apply x y)) := by
  classical
  cases x with
  | none => simp [Refines, Function1.apply, Function2.apply]
  | some x =>
    cases y with
    | none => simp [Refines, Function1.apply, Function2.apply]
    | some y =>
      by_cases hx : f.domain x
      · by_cases hy : f.domain y
        · rcases le_total x y with h | h
          · have hm := hf.antitoneOn hx hy h
            apply refines_of_eq
            simp [Function1.apply, Function2.apply, Functions.minR, Functions.maxR,
              min_eq_left h, max_eq_right h, min_eq_right hm, max_eq_left hm, hx, hy]
          · have hm := hf.antitoneOn hy hx h
            apply refines_of_eq
            simp [Function1.apply, Function2.apply, Functions.minR, Functions.maxR,
              min_eq_right h, max_eq_left h, min_eq_left hm, max_eq_right hm, hx, hy]
        · simp [Refines, Function1.apply, Function2.apply, hx, hy]
      · simp [Refines, Function1.apply, Function2.apply, hx]

end QSym.Value

namespace QSym

-- Try the generic partial-function contraction before expanding definitions.
macro "qsym_extrema" : tactic => `(tactic| (
  first
  | apply Value.refines_min_increasing
  | apply Value.refines_max_increasing
  | apply Value.refines_min_decreasing
  | apply Value.refines_max_decreasing
  all_goals first
  | exact FunctionOrder.exponential
  | exact FunctionOrder.logarithm
  | exact FunctionOrder.squareRoot
  | exact FunctionOrder.sinh
  | exact FunctionOrder.asinh
  | exact FunctionOrder.tanh
  | exact FunctionOrder.atan
  | exact FunctionOrder.asin
  | exact FunctionOrder.cbrt
  | exact FunctionOrder.acosh
  | exact FunctionOrder.atanh
  | exact FunctionOrder.erf
  | exact FunctionOrder.acos
  | exact FunctionOrder.erfc
))

end QSym

namespace QSym.ScalarOrder

theorem nonnegative_inverse_lt {x y : ℚ} (hx : 0≤x) (hy : 0≤y) (hnx : x≠0) (hny : y≠0) :
    x⁻¹<y⁻¹ ↔ y<x := inv_lt_inv₀ (lt_of_le_of_ne hx hnx.symm) (lt_of_le_of_ne hy hny.symm)
theorem nonnegative_inverse_le {x y : ℚ} (hx : 0≤x) (hy : 0≤y) (hnx : x≠0) (hny : y≠0) :
    x⁻¹≤y⁻¹ ↔ y≤x := inv_le_inv₀ (lt_of_le_of_ne hx hnx.symm) (lt_of_le_of_ne hy hny.symm)
theorem nonpositive_inverse_lt {x y : ℚ} (hx : x≤0) (hy : y≤0) (hnx : x≠0) (hny : y≠0) :
    x⁻¹<y⁻¹ ↔ y<x := inv_lt_inv_of_neg (lt_of_le_of_ne hx hnx) (lt_of_le_of_ne hy hny)
theorem nonpositive_inverse_le {x y : ℚ} (hx : x≤0) (hy : y≤0) (hnx : x≠0) (hny : y≠0) :
    x⁻¹≤y⁻¹ ↔ y≤x := inv_le_inv_of_neg (lt_of_le_of_ne hx hnx) (lt_of_le_of_ne hy hny)

theorem sign_mul (x y : ℝ) :
    Functions.signR.value (x*y)=Functions.signR.value x*Functions.signR.value y := by
  rcases lt_trichotomy x 0 with hx | hx | hx <;>
    rcases lt_trichotomy y 0 with hy | hy | hy <;>
    simp_all [Functions.signR]
  all_goals split_ifs <;> norm_num at * <;> nlinarith

theorem sign_abs (x : ℝ) : Functions.signR.value |x|=(Functions.signR.value x)^2 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [Functions.signR, abs_of_neg hx, hx, not_lt.mpr hx.le, not_lt.mpr (neg_nonneg.mpr hx.le)]
  · simp [Functions.signR, hx]
  · simp [Functions.signR, abs_of_pos hx, hx, not_lt.mpr hx.le]

end QSym.ScalarOrder

namespace QSym.Value

private theorem sign_apply (x : ℝ) :
    Functions.signR.apply (some x)=some (Functions.signR.value x) := by
  simp [Function1.apply, Functions.signR]

theorem refines_sign_product (x y : Option ℝ) :
    Refines (Functions.signR.apply (mul x y))
      (Functions.mulZ.apply (Functions.signR.apply x) (Functions.signR.apply y)) := by
  cases x with
  | none => simp [Refines, Function1.apply, Function2.apply, mul]
  | some x =>
    cases y with
    | none => simp [Refines, Function1.apply, Function2.apply, mul, Functions.signR]
    | some y =>
      apply refines_of_eq
      simpa [Function2.apply, Functions.mulZ, mul, sign_apply] using congrArg some (ScalarOrder.sign_mul x y)

theorem refines_sign_abs (x : Option ℝ) :
    Refines (Functions.signR.apply (abs x)) ((Functions.signR.apply x).map (fun k => k^2)) := by
  cases x with
  | none => simp [Refines, Function1.apply, abs]
  | some x =>
    apply refines_of_eq
    simpa [abs, sign_apply] using congrArg some (ScalarOrder.sign_abs x)

end QSym.Value
