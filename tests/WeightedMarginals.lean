import QSym.WeightedFibreObstruction
import QSym.AxiomCheck

noncomputable section
namespace QSym.WeightedParameter.MarginalTests
open MeasureTheory FibreObstruction

def gated (x : ℝ) : ℝ := if x = 0 then 0 else box (-1) 1 x

theorem gated_ae : gated =ᵐ[volume] box (-1) 1 := by
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [h0] with x hx
  simp [gated, hx]

theorem gated_integrable : Integrable gated volume :=
  (integrable_congr gated_ae).mpr (box_integrable (-1) 1)

def productWeight (_ : PUnit.{1}) (x y : ℝ) : ℝ := gated x * box 0 1 y

theorem product_rows (a : PUnit.{1}) : Fibre.IntegrableRows volume (productWeight a) :=
  Fibre.rows_separable gated (box_integrable 0 1)

def projected : Kernel (ℝ × ℝ) PUnit.{1} ℝ := Kernel.projected productWeight (fun _ x => x)

def marginal : Kernel ℝ PUnit.{1} ℝ :=
  Kernel.marginal volume productWeight (fun _ x => x) product_rows

theorem marginal_weight (x : ℝ) : marginal.weight PUnit.unit x = gated x := by
  change Fibre.mean volume (fun x y => gated x * box 0 1 y) x = gated x
  rw [Fibre.mean_separable, box_integral 0 1 (by norm_num)]
  norm_num

theorem marginal_preserves_puncture : marginal.weight PUnit.unit 0 = 0 := by
  rw [marginal_weight]
  simp [gated]

theorem marginal_mass : Kernel.integrate volume marginal PUnit.unit (fun _ => 1) = some 2 := by
  simp only [Kernel.integrate, marginal_weight, mul_one]
  rw [finiteIntegral_congr_ae gated_ae]
  have h := finiteIntegral_interval (-1) 1 1 (by norm_num)
  norm_num at h
  exact h

theorem product_integrable :
    Integrable (fun z : ℝ × ℝ => productWeight PUnit.unit z.1 z.2 * 1) (volume.prod volume) := by
  simpa only [productWeight, mul_one] using gated_integrable.mul_prod (box_integrable 0 1)

theorem product_mass :
    Kernel.integrate (volume.prod volume) projected PUnit.unit (fun _ => 1) = some 2 :=
  (Kernel.integrate_marginal volume volume productWeight (fun _ x => x) product_rows
    PUnit.unit (fun _ => 1) product_integrable).trans marginal_mass

theorem checked_marginal_mass :
    Fibre.observe volume volume (productWeight PUnit.unit) (product_rows PUnit.unit)
      (fun _ => 1) product_integrable.aestronglyMeasurable = some 2 :=
  (Fibre.observe_eq_joint volume volume (productWeight PUnit.unit) (product_rows PUnit.unit)
    (fun _ => 1) product_integrable.aestronglyMeasurable).trans product_mass

-- An excluded latent point may be removed on every fibre. The retained
-- puncture at x = 0 survives: the resulting equality is pointwise in x.
theorem latent_puncture :
    Fibre.mean volume (fun x y : ℝ => if y = 0 then 0 else productWeight PUnit.unit x y) =
      gated := by
  have he : Fibre.mean volume
      (fun x y : ℝ => if y = 0 then 0 else productWeight PUnit.unit x y) =
      Fibre.mean volume (productWeight PUnit.unit) := by
    apply Fibre.mean_congr
    intro x
    have h0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [h0] with y hy
    simp [hy]
  rw [he]
  funext x
  exact marginal_weight x

-- Signed cancellation can make the marginal zero while the joint absolute
-- integral diverges. Row integrability alone does not preserve scalar domains.
abbrev twoAtoms : Measure Bool := Measure.dirac false + Measure.dirac true
def balanced (_ : ℝ) (b : Bool) : ℝ := if b then 1 else -1

theorem balanced_rows : Fibre.IntegrableRows twoAtoms balanced := by
  constructor
  intro x
  simp [twoAtoms]

theorem balanced_mean (x : ℝ) : Fibre.mean twoAtoms balanced x = 0 := by
  rw [Fibre.mean, twoAtoms, integral_add_measure (by simp) (by simp)]
  norm_num [balanced]

theorem balanced_variation (x : ℝ) : Fibre.variation twoAtoms balanced x = 2 := by
  rw [Fibre.variation, twoAtoms, integral_add_measure (by simp) (by simp)]
  norm_num [balanced]

theorem balanced_measurable :
    AEStronglyMeasurable (fun z : ℝ × Bool => balanced z.1 z.2 * 1) (volume.prod twoAtoms) := by
  simpa [balanced] using
    ((measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
      measurable_snd).aestronglyMeasurable

theorem balanced_joint_not_integrable :
    ¬ Integrable (fun z : ℝ × Bool => balanced z.1 z.2 * 1) (volume.prod twoAtoms) := by
  rw [Fibre.integrable_weighted_iff balanced_rows (fun _ => 1) balanced_measurable]
  simp only [balanced_variation, abs_one, mul_one]
  simp [integrable_const_iff, isFiniteMeasure_iff, Real.volume_univ]

theorem balanced_joint_none :
    finiteIntegral (volume.prod twoAtoms) (fun z : ℝ × Bool => balanced z.1 z.2 * 1) = none := by
  unfold finiteIntegral
  exact if_neg balanced_joint_not_integrable

theorem balanced_marginal_zero :
    finiteIntegral volume (fun x : ℝ => Fibre.mean twoAtoms balanced x * 1) = some 0 := by
  simp [balanced_mean, finiteIntegral]

theorem checked_cancellation_none :
    Fibre.observe volume twoAtoms balanced balanced_rows (fun _ => 1) balanced_measurable = none :=
  (Fibre.observe_eq_joint volume twoAtoms balanced balanced_rows (fun _ => 1)
    balanced_measurable).trans balanced_joint_none

#qsym_check_axioms Fibre.finiteIntegral_row
#qsym_check_axioms Fibre.finiteIntegral_row_of_integrable
#qsym_check_axioms Fibre.mean_congr
#qsym_check_axioms Fibre.rows_reweight
#qsym_check_axioms Fibre.rows_add
#qsym_check_axioms Fibre.mean_add
#qsym_check_axioms Fibre.mean_reweight
#qsym_check_axioms Fibre.variation_reweight
#qsym_check_axioms Fibre.rows_separable
#qsym_check_axioms Fibre.mean_separable
#qsym_check_axioms Fibre.mean_reparam
#qsym_check_axioms Fibre.variation_reparam
#qsym_check_axioms Fibre.rows_reparam_iff
#qsym_check_axioms Fibre.variation_nonneg
#qsym_check_axioms Fibre.abs_mean_le_variation
#qsym_check_axioms Fibre.variation_eq_mean_of_nonneg
#qsym_check_axioms Fibre.integrable_weighted_iff
#qsym_check_axioms Fibre.mean_measurable
#qsym_check_axioms Fibre.finiteIntegral_project
#qsym_check_axioms Fibre.observe_eq_joint
#qsym_check_axioms Kernel.marginal_weight
#qsym_check_axioms Kernel.integrate_marginal
#qsym_check_axioms FibreObstruction.nullScale_preserving
#qsym_check_axioms FibreObstruction.same_quotient
#qsym_check_axioms FibreObstruction.original_mass
#qsym_check_axioms FibreObstruction.rescaled_mass
#qsym_check_axioms FibreObstruction.original_rows
#qsym_check_axioms FibreObstruction.rescaled_rows
#qsym_check_axioms FibreObstruction.original_nonnegative
#qsym_check_axioms FibreObstruction.rescaled_nonnegative
#qsym_check_axioms FibreObstruction.no_quotient_fibre_observer
#qsym_check_axioms marginal_preserves_puncture
#qsym_check_axioms marginal_mass
#qsym_check_axioms product_mass
#qsym_check_axioms checked_marginal_mass
#qsym_check_axioms latent_puncture
#qsym_check_axioms balanced_rows
#qsym_check_axioms balanced_mean
#qsym_check_axioms balanced_variation
#qsym_check_axioms balanced_joint_not_integrable
#qsym_check_axioms balanced_joint_none
#qsym_check_axioms balanced_marginal_zero
#qsym_check_axioms checked_cancellation_none
end QSym.WeightedParameter.MarginalTests
