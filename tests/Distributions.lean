import QSym.DistributionIntegral
import QSym.DistributionSquareIntegral
import QSym.DistributionGraphBridge
import QSym.PositiveIntegral
import QSym.AxiomCheck

namespace QSym.DistributionTests
open Distribution

example : densityAtValue lebesgueValue (some 0) = some 1 := by
  simp [densityAtValue, lebesgueValue, densityValue]

example (a : ℝ) : densityAtValue (diracValue (some a)) (some a) = none := by
  simp [densityAtValue, diracValue]

example (a x : ℝ) (h : x ≠ a) :
    densityAtValue (diracValue (some a)) (some x) = some 0 := by
  simp [densityAtValue, diracValue, h]

-- Undefined pointwise density data is retained, even at a singleton.
example : densityAtValue (weightValue (some (fun x => if x = 0 then none else some 1))
    lebesgueValue) (some 0) = none := by
  rw [weighted_lebesgue_density]; simp

-- Finite scalar integration works for atoms over higher-order values, with no
-- measurable-space structure imposed on the value type.
example : massValue (diracValue (some (fun n : ℕ => n + 1))) = some 1 := rfl
example : massValue (scaleValue (some (-2)) (diracValue (some Unit.unit))) = some (-2) := by
  norm_num [massValue, scaleValue, diracValue, integrate, Value.mul]

-- Observing only the negative root distinguishes this fibre from its marginal.
theorem negative_branch_at_four :
    (GraphFibre.fibre GraphFibre.square 4).bind (fun atoms =>
      GraphFibre.observe atoms (fun x => some (if x < 0 then 1 else 0))) =
      some (1/4 : ℝ) := by
  rw [GraphFibre.square_observe (by norm_num)]
  norm_num [GraphFibre.jac, Value.add, Value.mul, Real.sqrt_eq_iff_mul_self_eq]

theorem partial_test_at_root :
    (GraphFibre.fibre GraphFibre.square 4).bind (fun atoms =>
      GraphFibre.observe atoms (fun x => if x < 0 then none else some 1)) = none := by
  rw [GraphFibre.square_observe (by norm_num)]
  norm_num [Value.add, Value.mul, Real.sqrt_eq_iff_mul_self_eq]

theorem restricted_square_density (y : ℝ) :
    GraphFibre.marginalOn (Set.Ioo 0 1) GraphFibre.square y =
      some (if 0 < y ∧ y < 1 then GraphFibre.jac y else 0) := by qsym_rule

#qsym_check_axioms restricted_square_density
#qsym_check_axioms GraphFibre.square_marginal_zero
#qsym_check_axioms GraphFibre.mass_eq_marginal
#qsym_check_axioms GraphFibre.square_mass_rule
#qsym_check_axioms constant_weight_dirac
#qsym_check_axioms GraphFibre.integrate_presentation
#qsym_check_axioms GraphFibre.square_marginal_tendsto
#qsym_check_axioms GraphFibre.square_marginal_integral
#qsym_check_axioms GraphFibre.square_disintegrates
#qsym_check_axioms GraphFibre.square_rule
#qsym_check_axioms negative_branch_at_four
#qsym_check_axioms partial_test_at_root
#qsym_check_axioms partialIntegral_interval
#qsym_check_axioms partialIntegral_congr_away
#qsym_check_axioms weighted_lebesgue_density
#qsym_check_axioms punctured_at_zero
#qsym_check_axioms mass_dirac
#qsym_check_axioms mass_diracValue
#qsym_check_axioms density_lebesgueValue
#qsym_check_axioms mass_weight_diracValue
#qsym_check_axioms density_weight_lebesgueValue
#qsym_check_axioms PositiveIntegral.zeroExtend_sup
#qsym_check_axioms PositiveIntegral.integralHom
#qsym_check_axioms PositiveIntegral.partialIntegralHom
end QSym.DistributionTests
