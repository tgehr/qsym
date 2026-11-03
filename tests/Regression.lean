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

-- Infinite positive mass is a valid measure; a divergent finite-valued
-- Bochner integral has no value. They must not share a type or failure policy.
example : partialIntegral volume (fun _ : ℝ => some (1 : ℝ)) = none := by
  apply partialIntegral_invalid
  simp [integrable_const_iff, isFiniteMeasure_iff]

end QSym.Regression
