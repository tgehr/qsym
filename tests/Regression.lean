import QSym

namespace QSym.Regression
open MeasureTheory

example (ρ : Env) :
    Expr.eval ρ (.densityAt (.puncture .lebesgue) (.real 0)) = some 0 := by
  simp [Expr.eval, Value.densityAt, Density.puncture]

example (ρ : Env) :
    Expr.eval ρ (.densityAt .lebesgue (.real 0)) = some 1 := by
  simp [Expr.eval, Value.densityAt, Density.lebesgue]

example (ρ : Env) : Expr.eval ρ (.mulR (.real 0) (.invR (.real 0))) = none := by
  simp [Expr.eval, Value.inv, Value.mul]

example (ρ : Env) : Expr.eval ρ (.maskR (.bool false) (.invR (.real 0))) = some 0 := by
  simp [Expr.eval, Value.mask]

example : Value.Refines (Value.mul (some (0 : ℝ)) (Value.inv (some 0))) (some 0) := by
  qsym_scalar

example : ¬Value.Refines (some (0 : ℝ)) (Value.inv (some 0)) := by
  simp [Value.Refines, Value.inv]

example (x : ℂ) : Value.Refines (Value.mul (some x) (Value.inv (some x))) (some 1) := by
  qsym_scalar

-- Infinite positive mass is a valid measure; a divergent finite-valued
-- Bochner integral has no value. They must not share a type or failure policy.
example : partialIntegral volume (fun _ : ℝ => some (1 : ℝ)) = none := by
  apply partialIntegral_invalid
  simp [integrable_const_iff, isFiniteMeasure_iff]

end QSym.Regression
