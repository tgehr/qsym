import QSym.WeightedFibreReindex
import QSym.WeightedFibreObstruction
import QSym.AxiomCheck

noncomputable section
namespace QSym.WeightedParameter.FibreModelTests
open MeasureTheory
open scoped ENNReal ProbabilityTheory
open Fibre

def nullCoordinates : Coordinates ℝ ℝ ℝ where
  coord := fun x =>
    { toEquiv :=
        { toFun := fun y => if x = 0 then 2 * y else y
          invFun := fun y => if x = 0 then (1 / 2) * y else y
          left_inv := by intro y; by_cases hx : x = 0 <;> simp [hx, ← mul_assoc]
          right_inv := by intro y; by_cases hx : x = 0 <;> simp [hx, ← mul_assoc] }
      measurable_toFun := by
        change Measurable (fun y : ℝ => if x = 0 then 2 * y else y)
        by_cases hx : x = 0 <;> simp only [hx, ↓reduceIte] <;> fun_prop
      measurable_invFun := by
        change Measurable (fun y : ℝ => if x = 0 then (1 / 2) * y else y)
        by_cases hx : x = 0 <;> simp only [hx, ↓reduceIte] <;> fun_prop }
  forward := Measurable.ite (measurable_fst (measurableSet_singleton 0))
    (measurable_const.mul measurable_snd) measurable_snd
  backward := Measurable.ite (measurable_fst (measurableSet_singleton 0))
    (measurable_const.mul measurable_snd) measurable_snd

def original : Family ℝ PUnit.{1} ℝ where
  space := Space.ofMeasure ℝ volume
  body := fun x =>
    ⟨fun _ y => FibreObstruction.original.body.weight PUnit.unit (x, y), fun _ _ => x⟩

/-- The old counterexample changes the weight but leaves every reference as volume. -/
def uncorrected : Family ℝ PUnit.{1} ℝ where
  space := Space.ofMeasure ℝ volume
  body := fun x =>
    ⟨fun _ y => FibreObstruction.rescaled.body.weight PUnit.unit (x, y), fun _ _ => x⟩

/-- A valid reparametrization also transports the chosen reference. -/
def corrected : Family ℝ PUnit.{1} ℝ := original.pull nullCoordinates

theorem corrected_weight_eq_uncorrected (x y : ℝ) :
    (corrected.body x).weight PUnit.unit y = (uncorrected.body x).weight PUnit.unit y := rfl

theorem original_at_zero : original.observe 0 PUnit.unit (fun _ => 1) = some 1 := by
  change finiteIntegral volume (fun y : ℝ =>
    FibreObstruction.original.body.weight PUnit.unit ((0 : ℝ), y) * 1) = some 1
  simp only [mul_one]
  rw [finiteIntegral, if_pos (FibreObstruction.original_rows.integrable 0),
    FibreObstruction.original_fibre_zero]

theorem uncorrected_at_zero : uncorrected.observe 0 PUnit.unit (fun _ => 1) = some (1 / 2) := by
  change finiteIntegral volume (fun y : ℝ =>
    FibreObstruction.rescaled.body.weight PUnit.unit ((0 : ℝ), y) * 1) = some (1 / 2)
  simp only [mul_one]
  rw [finiteIntegral, if_pos (FibreObstruction.rescaled_rows.integrable 0),
    FibreObstruction.rescaled_fibre_zero]

theorem corrected_same : Fibre.Hom.ofFamily corrected = Fibre.Hom.ofFamily original :=
  Fibre.Hom.ofFamily_pull original nullCoordinates

theorem corrected_at_zero : corrected.observe 0 PUnit.unit (fun _ => 1) = some 1 :=
  ((original.pullIso nullCoordinates).observe_eq 0 PUnit.unit (fun _ => 1)).trans original_at_zero

/-- The new quotient excludes the former equality, not just this particular
coordinate witness: any fibre-preserving witness would preserve the observer. -/
theorem uncorrected_distinct : Fibre.Hom.ofFamily uncorrected ≠ Fibre.Hom.ofFamily original := by
  intro h
  have ho := congrArg (fun p : Fibre.Trace ℝ ℝ => Fibre.Hom.observe p 0 PUnit.unit (fun _ => 1)) h
  change uncorrected.observe 0 PUnit.unit (fun _ => 1) = original.observe 0 PUnit.unit (fun _ => 1) at ho
  rw [uncorrected_at_zero, original_at_zero] at ho
  norm_num at ho

theorem corrected_reference_zero : corrected.space.reference 0 = (2 : ℝ≥0∞) • (volume : Measure ℝ) := by
  change nullCoordinates.symm.transport (ProbabilityTheory.Kernel.const ℝ (volume : Measure ℝ)) 0 = _
  rw [Coordinates.transport_apply]
  change Measure.map (fun y : ℝ => if (0 : ℝ) = 0 then (1 / 2) * y else y) volume = _
  simp only [eq_self_iff_true, ite_true]
  rw [Real.map_volume_mul_left (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  norm_num

theorem corrected_reference_elsewhere (x : ℝ) (hx : x ≠ 0) :
    corrected.space.reference x = (volume : Measure ℝ) := by
  change nullCoordinates.symm.transport (ProbabilityTheory.Kernel.const ℝ (volume : Measure ℝ)) x = _
  rw [Coordinates.transport_apply]
  change Measure.map (fun y : ℝ => if x = 0 then (1 / 2) * y else y) volume = _
  simp [hx]

theorem corrected_same_joint_reference :
    (volume : Measure ℝ) ⊗ₘ corrected.space.reference =
      (volume : Measure ℝ) ⊗ₘ original.space.reference := by
  apply Measure.compProd_congr
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [h0] with x hx
  exact corrected_reference_elsewhere x hx

theorem original_joint_mass : original.observeJoint volume PUnit.unit (fun _ _ => 1) = some 2 := by
  change finiteIntegral (volume ⊗ₘ ProbabilityTheory.Kernel.const ℝ volume)
    (fun z : ℝ × ℝ => FibreObstruction.original.body.weight PUnit.unit z * 1) = some 2
  rw [Measure.compProd_const]
  exact FibreObstruction.original_mass

theorem uncorrected_joint_mass : uncorrected.observeJoint volume PUnit.unit (fun _ _ => 1) = some 2 := by
  change finiteIntegral (volume ⊗ₘ ProbabilityTheory.Kernel.const ℝ volume)
    (fun z : ℝ × ℝ => FibreObstruction.rescaled.body.weight PUnit.unit z * 1) = some 2
  rw [Measure.compProd_const]
  exact FibreObstruction.rescaled_mass

theorem corrected_joint_mass : corrected.observeJoint volume PUnit.unit (fun _ _ => 1) = some 2 :=
  ((original.pullIso nullCoordinates).observeJoint_eq volume PUnit.unit (fun _ _ => 1)).trans
    original_joint_mass

/-- A real density is a fibre over its output coordinate with one latent point. -/
def density (w : ℝ → ℝ) : Fibre.Trace ℝ ℝ :=
  Fibre.Hom.reweight (fun x _ _ => w x) (Fibre.Hom.pure (fun x _ => x))

theorem density_at (w : ℝ → ℝ) (x : ℝ) :
    Fibre.Hom.observe (density w) x PUnit.unit (fun _ => 1) = some (w x) := by
  rw [density, Fibre.Hom.observe_reweight, Fibre.Hom.observe_pure]
  simp

theorem puncture_preserved :
    Fibre.Hom.observe (density (fun x => if x = 0 then 0 else 1)) 0 PUnit.unit (fun _ => 1) = some 0 := by
  simp [density_at]

theorem density_right_unit (w : ℝ → ℝ) :
    Fibre.Hom.comp (density w) (Fibre.Hom.pure (fun _ => id)) = density w :=
  Fibre.Hom.comp_pure _

/-- Evaluating a retained coordinate includes null points; no AE version is chosen. -/
theorem evaluate_null_point :
    Fibre.Hom.observe
      (Fibre.Hom.reindex (Fibre.Hom.ofFamily corrected) (fun _ : PUnit => (0 : ℝ)) measurable_const)
      PUnit.unit PUnit.unit (fun _ => 1) = some 1 := by
  rw [Fibre.Hom.observe_reindex]
  exact corrected_at_zero

def unbounded : Family ℝ PUnit.{1} ℝ where
  space := Space.ofMeasure ℝ volume
  body := fun x => ⟨fun _ _ => 1, fun _ _ => x⟩

theorem unbounded_none : unbounded.observe 0 PUnit.unit (fun _ => 1) = none := by
  change finiteIntegral (volume : Measure ℝ) (fun _ => (1 : ℝ) * 1) = none
  simp [finiteIntegral, integrable_const_iff, isFiniteMeasure_iff, Real.volume_univ]

theorem transported_none :
    (unbounded.pull nullCoordinates).observe 0 PUnit.unit (fun _ => 1) = none :=
  ((unbounded.pullIso nullCoordinates).observe_eq 0 PUnit.unit (fun _ => 1)).trans unbounded_none

-- Returned values require no measurable-space structure, including universes.
example : Fibre.Trace ℝ (ℕ → ℕ) := Fibre.Hom.pure (fun _ _ n => n + 1)
example : Fibre.Trace ℝ Type := Fibre.Hom.pure (fun _ _ => {x : ℝ // 0 ≤ x})
example : Fibre.Trace ℝ (Fibre.Trace ℝ ℝ) := Fibre.Hom.pure (fun _ _ => density (fun _ => 1))

#qsym_check_axioms Coordinates.transport_apply
#qsym_check_axioms Coordinates.preserving_transport
#qsym_check_axioms Coordinates.preserving_joint
#qsym_check_axioms Family.Iso.refl
#qsym_check_axioms Family.Iso.symm
#qsym_check_axioms Family.Iso.trans
#qsym_check_axioms Family.Iso.comp
#qsym_check_axioms Family.Iso.observe_eq
#qsym_check_axioms Family.Iso.observeJoint_eq
#qsym_check_axioms Fibre.Hom.comp_pure
#qsym_check_axioms Fibre.Hom.pure_comp
#qsym_check_axioms Fibre.Hom.comp_assoc
#qsym_check_axioms Fibre.Hom.observe_pure
#qsym_check_axioms Fibre.Hom.observe_reweight
#qsym_check_axioms Fibre.Hom.reweight_one
#qsym_check_axioms Fibre.Hom.reweight_mul
#qsym_check_axioms Fibre.Hom.ofFamily_pull
#qsym_check_axioms Fibre.Hom.reindex_id
#qsym_check_axioms Fibre.Hom.reindex_reindex
#qsym_check_axioms Fibre.Hom.reindex_pure
#qsym_check_axioms Fibre.Hom.reindex_comp
#qsym_check_axioms Fibre.Hom.observe_reindex
#qsym_check_axioms corrected_weight_eq_uncorrected
#qsym_check_axioms original_at_zero
#qsym_check_axioms uncorrected_at_zero
#qsym_check_axioms corrected_same
#qsym_check_axioms corrected_at_zero
#qsym_check_axioms uncorrected_distinct
#qsym_check_axioms corrected_reference_zero
#qsym_check_axioms corrected_reference_elsewhere
#qsym_check_axioms corrected_same_joint_reference
#qsym_check_axioms original_joint_mass
#qsym_check_axioms uncorrected_joint_mass
#qsym_check_axioms corrected_joint_mass
#qsym_check_axioms density_at
#qsym_check_axioms puncture_preserved
#qsym_check_axioms density_right_unit
#qsym_check_axioms evaluate_null_point
#qsym_check_axioms unbounded_none
#qsym_check_axioms transported_none

end QSym.WeightedParameter.FibreModelTests
