import QSym.RefinementBase

namespace QSym.Value

theorem refines_sign_increasing_difference (f : Function1 ℝ ℝ)
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

theorem refines_sign_exp_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.expR.apply x) (mul (some (-1)) (Functions.expR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.expR (Real.exp_strictMono.strictMonoOn _) x y

theorem refines_sign_log_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.logR.apply x) (mul (some (-1)) (Functions.logR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.logR (by
    intro x hx y _ hxy
    exact Real.log_lt_log hx hxy) x y

theorem refines_sign_sinh_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.sinhR.apply x) (mul (some (-1)) (Functions.sinhR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.sinhR (FunctionOrder.sinh) x y

theorem refines_sign_tanh_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.tanhR.apply x) (mul (some (-1)) (Functions.tanhR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.tanhR (FunctionOrder.tanh) x y

theorem refines_sign_asinh_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.asinhR.apply x) (mul (some (-1)) (Functions.asinhR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.asinhR (FunctionOrder.asinh) x y

theorem refines_sign_atan_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.atanR.apply x) (mul (some (-1)) (Functions.atanR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.atanR (FunctionOrder.atan) x y

theorem refines_sign_asin_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.asinR.apply x) (mul (some (-1)) (Functions.asinR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.asinR (FunctionOrder.asin) x y

theorem refines_sign_atanh_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.atanhR.apply x) (mul (some (-1)) (Functions.atanhR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.atanhR (FunctionOrder.atanh) x y

theorem refines_sign_cbrt_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.cbrtR.apply x) (mul (some (-1)) (Functions.cbrtR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.cbrtR (FunctionOrder.cbrt) x y

theorem refines_sign_acosh_pair_difference (x y : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.acoshR.apply x) (mul (some (-1)) (Functions.acoshR.apply y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) :=
  refines_sign_increasing_difference Functions.acoshR (FunctionOrder.acosh) x y

end QSym.Value
