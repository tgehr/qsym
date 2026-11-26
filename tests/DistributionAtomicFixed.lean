import QSym.DistributionAtomicFixed
import QSym.AxiomCheck

noncomputable section
open scoped ENNReal
open QSym.Distribution QSym.Distribution.Atomic

namespace AtomicFixedTest

theorem fairRetry (a : α) :
    (retryStep (fun x => (1-(1/2 : ℝ≥0∞)) * atom a x) (1/2)).lfp = atom a :=
  lfp_stop_or_retry (atom a) _ (by norm_num)

-- The loop visits the atom even when its first emission is scaled by zero.
theorem visitsZeroWeight (n : ℕ) :
    integrate (approximate (.scale 0 (.dirac (0 : ℝ))) (1/2) (n+1)) (fun _ => none) = none := by
  rw [integrate_approximate]
  rfl

theorem fairAtomDensity (x : ℝ) :
    densityAt (.scale ((1-1/2 : ℝ)⁻¹) (.scale (1/2) (.dirac (0 : ℝ)))) x =
      if x = 0 then none else some 0 := by
  have h := ((Represents.dirac (0 : ℝ)).scale (r := 1/2) (by norm_num)).retry
    (r := 1/2) (by norm_num) (by norm_num)
  rw [h.density, lfp_retry]
  by_cases e : x = 0 <;> simp [atom, e]

#qsym_check_axioms fairRetry
#qsym_check_axioms visitsZeroWeight
#qsym_check_axioms fairAtomDensity
#qsym_check_axioms Represents.pairing
#qsym_check_axioms approximate_limit
end AtomicFixedTest
