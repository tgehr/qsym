import QSym.DistributionAtomicAffine
import QSym.DistributionAtomicObservation
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

theorem visitedZeroWeight : visited (.scale 0 (.dirac (0 : ℝ))) = {0} := by simp

theorem zeroWeightDiffers : ∃ t : ℝ → Option ℝ,
    integrate (.scale 0 (.dirac 0)) t ≠ integrate .zero t :=
  ⟨fun _ => none, by decide⟩

#qsym_check_axioms Observation.retry
#qsym_check_axioms Observation.weight
#qsym_check_axioms Observation.bind
#qsym_check_axioms Observation.realBind
#qsym_check_axioms fixed_tail
#qsym_check_axioms fixed_add_tail
#qsym_check_axioms fixed_of_step
#qsym_check_axioms fixed_of_step_on
#qsym_check_axioms fixed_affine
#qsym_check_axioms Affine.add_left_zero
#qsym_check_axioms Affine.scale_zero
#qsym_check_axioms fixed_retry
#qsym_check_axioms retry_empty
#qsym_check_axioms retry_zero_point
#qsym_check_axioms point_add
#qsym_check_axioms point_add_empty
#qsym_check_axioms retry_point
#qsym_check_axioms mass_retry
#qsym_check_axioms density_retry
#qsym_check_axioms Presents.eq_iff
#qsym_check_axioms Presents.unfold_retry
#qsym_check_axioms fairRetry
#qsym_check_axioms visitsZeroWeight
#qsym_check_axioms fairAtomDensity
#qsym_check_axioms Represents.pairing
#qsym_check_axioms approximate_limit
end AtomicFixedTest
