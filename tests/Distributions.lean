import QSym.DistributionIntegral
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
