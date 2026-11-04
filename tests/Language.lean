import QSym

namespace QSym.Language

theorem real_power_domain : ¬Functions.powerR.domain (-2) (1/2) := by
  simp only [Functions.powerR, not_or, not_and, not_exists]
  refine ⟨by norm_num, by norm_num, fun _ n hn => ?_⟩
  have h0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have h1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

theorem invalid_real_root : Functions.powerR.apply (some (-2)) (some (1/2)) = none := by
  exact if_neg real_power_domain

theorem zero_real_power : Functions.powerR.apply (some 0) (some 0) = some 1 := by
  norm_num [Function2.apply, Functions.powerR]

theorem zero_complex_power : Functions.powerC.apply (some 0) (some 0) = some 1 := by
  norm_num [Function2.apply, Functions.powerC]

theorem invalid_complex_power : Functions.powerC.apply (some 0) (some Complex.I) = none := by
  norm_num [Function2.apply, Functions.powerC]

theorem invalid_integer_power : Functions.powQZ.apply (some 0) (some (-1)) = none := by
  norm_num [Function2.apply, Functions.powQZ]

theorem invalid_log : Functions.logR.apply (some 0) = none := by
  norm_num [Function1.apply, Functions.logR]

theorem invalid_sqrt : Functions.sqrtR.apply (some (-1)) = none := by
  norm_num [Function1.apply, Functions.sqrtR]

theorem invalid_asin : Functions.asinR.apply (some 2) = none := by
  norm_num [Function1.apply, Functions.asinR]

theorem invalid_tan : Functions.tanR.apply (some (Real.pi/2)) = none := by
  simp [Function1.apply, Functions.tanR]

theorem invalid_rational : Functions.makeQ.apply (some 1) (some 0) = none := by
  norm_num [Function2.apply, Functions.makeQ]

theorem complex_cosh_zero : Functions.coshC.apply (some 0) = some 1 := by
  simp [Function1.apply, Functions.coshC]

theorem strict_function : Functions.expR.apply (Functions.logR.apply (some 0)) = none := by
  rw [invalid_log]
  rfl

theorem masked_function (ρ : Env) :
    Expr.eval ρ (.maskR (.bool false) (.logR (.real 0))) = some 0 := by
  simp [Expr.eval, Value.mask]

theorem exact_rational (ρ : Env) :
    Expr.eval ρ (.castQR (.addQ (.rat (1/3)) (.rat (1/6)))) = some (1/2) := by
  norm_num [Expr.eval, Function1.apply, Function2.apply, Functions.addQ, Functions.castQR]

#qsym_check_axioms real_power_domain
#qsym_check_axioms invalid_real_root
#qsym_check_axioms zero_real_power
#qsym_check_axioms zero_complex_power
#qsym_check_axioms invalid_complex_power
#qsym_check_axioms invalid_integer_power
#qsym_check_axioms invalid_log
#qsym_check_axioms invalid_sqrt
#qsym_check_axioms invalid_asin
#qsym_check_axioms invalid_tan
#qsym_check_axioms invalid_rational
#qsym_check_axioms complex_cosh_zero
#qsym_check_axioms strict_function
#qsym_check_axioms masked_function
#qsym_check_axioms exact_rational

end QSym.Language
