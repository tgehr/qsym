import QSym.RefinementBase

namespace QSym.Value

theorem refines_sign_decreasing_difference (f : Function1 ℝ ℝ)
    (hf : FunctionOrder.Decreasing f) (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (f.apply x) (mul (some (-1)) (f.apply y))))
      (Functions.signR.apply (add y (mul (some (-1)) x))) := by
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

theorem refines_sign_acos_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.acosR.apply x) (mul (some (-1)) (Functions.acosR.apply y))))
      (Functions.signR.apply (add y (mul (some (-1)) x))) :=
  refines_sign_decreasing_difference Functions.acosR FunctionOrder.acos x y

theorem refines_sign_erfc_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.erfcR.apply x) (mul (some (-1)) (Functions.erfcR.apply y))))
      (Functions.signR.apply (add y (mul (some (-1)) x))) :=
  refines_sign_decreasing_difference Functions.erfcR FunctionOrder.erfc x y

end QSym.Value
