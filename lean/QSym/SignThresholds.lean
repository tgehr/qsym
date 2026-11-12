import QSym.RefinementBase

namespace QSym.Value

theorem refines_sign_log (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.logR.apply x))
      (Functions.signR.apply (add x (mul (some (-1)) (some 1)))) := by
  cases x with
  | none => simp [Refines, Function1.apply, add, mul, ← sub_eq_add_neg]
  | some x =>
    by_cases hx : 0<x
    · simp [Refines, Function1.apply, Functions.logR, Functions.signR, add, mul, ← sub_eq_add_neg,
        hx, Real.log_neg_iff hx, Real.log_pos_iff hx.le, sub_neg, sub_pos]
    · simp [Refines, Function1.apply, Functions.logR, hx]

theorem refines_sign_exp_difference (x : Option ℝ) :
    Refines (Functions.signR.apply (add (Functions.expR.apply x) (mul (some (-1)) (some 1))))
      (Functions.signR.apply x) := by
  cases x with
  | none => simp [Refines, Function1.apply, add, mul, ← sub_eq_add_neg]
  | some x =>
    simp [Refines, Function1.apply, Functions.expR, Functions.signR, add, mul, ← sub_eq_add_neg,
      sub_neg, sub_pos, Real.exp_lt_one_iff, Real.one_lt_exp_iff]

end QSym.Value
