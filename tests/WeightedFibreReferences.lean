import QSym.WeightedFibreReference
import QSym.AxiomCheck

noncomputable section
namespace QSym.WeightedParameter.ReferenceTests
open MeasureTheory
open scoped ProbabilityTheory

def standard : Fibre.Reference ℝ Bool where
  base := volume
  fibres := ProbabilityTheory.Kernel.const ℝ (Measure.dirac false)

def switchedKernel : ProbabilityTheory.Kernel ℝ Bool :=
  ProbabilityTheory.Kernel.piecewise (measurableSet_singleton (0 : ℝ))
    (ProbabilityTheory.Kernel.const ℝ (Measure.dirac true))
    (ProbabilityTheory.Kernel.const ℝ (Measure.dirac false))

instance : ProbabilityTheory.IsMarkovKernel switchedKernel := by
  unfold switchedKernel
  infer_instance

def switched : Fibre.Reference ℝ Bool where
  base := volume
  fibres := switchedKernel

def score (_ : ℝ) (b : Bool) : ℝ := if b then 1 else 0

theorem same_joint : standard.joint = switched.joint := by
  change volume ⊗ₘ (ProbabilityTheory.Kernel.const ℝ (Measure.dirac false)) = volume ⊗ₘ switchedKernel
  apply Measure.compProd_congr
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [h0] with x hx
  simp [switchedKernel, ProbabilityTheory.Kernel.piecewise_apply, hx]

theorem standard_mean : standard.mean score 0 = 0 := by
  simp [Fibre.Reference.mean, standard, score]

theorem switched_mean : switched.mean score 0 = 1 := by
  simp [Fibre.Reference.mean, switched, switchedKernel, ProbabilityTheory.Kernel.piecewise_apply, score]

-- The new reference data retains the chosen pointwise family even when its
-- induced joint measure is identical. This is needed for density preservation.
theorem distinct_references : standard ≠ switched := by
  intro h
  have hm := congrArg (fun R : Fibre.Reference ℝ Bool => R.mean score 0) h
  change standard.mean score 0 = switched.mean score 0 at hm
  rw [standard_mean, switched_mean] at hm
  exact zero_ne_one hm

theorem standard_rows : Fibre.Reference.IntegrableRows standard score := by
  constructor
  intro x
  simp [standard]

theorem switched_rows : Fibre.Reference.IntegrableRows switched score := by
  constructor
  intro x
  simp [switched, switchedKernel, ProbabilityTheory.Kernel.piecewise_apply]
  split_ifs <;> simp

#qsym_check_axioms Fibre.Reference.joint_product
#qsym_check_axioms Fibre.Reference.finiteIntegral_row
#qsym_check_axioms Fibre.Reference.integrable_weighted_iff
#qsym_check_axioms Fibre.Reference.mean_reparam
#qsym_check_axioms Fibre.Reference.variation_reparam
#qsym_check_axioms Fibre.Reference.rows_reparam_iff
#qsym_check_axioms Fibre.Reference.FibreIso.refl
#qsym_check_axioms Fibre.Reference.FibreIso.symm
#qsym_check_axioms Fibre.Reference.FibreIso.trans
#qsym_check_axioms same_joint
#qsym_check_axioms standard_mean
#qsym_check_axioms switched_mean
#qsym_check_axioms distinct_references
#qsym_check_axioms standard_rows
#qsym_check_axioms switched_rows
end QSym.WeightedParameter.ReferenceTests
