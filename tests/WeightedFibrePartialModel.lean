import QSym.DistributionPartialModel
import QSym.AxiomCheck

noncomputable section
namespace QSym.PartialFibreTests
open MeasureTheory Distribution
open scoped ProbabilityTheory
open WeightedParameter.Fibre

/-- Zero weight must not erase an undefined stored value, even at a Dirac point. -/
def undefinedValueFamily : PartialFamily PUnit.{1} PUnit.{1} ℝ where
  space := Space.point
  body := fun _ =>
    { weight := fun _ _ => some 0
      value := fun _ _ => none }

def undefinedValueHom : PartialHom PUnit.{1} PUnit.{1} ℝ :=
  PartialHom.ofFamily undefinedValueFamily

theorem zero_weight_preserves_undefined :
    PartialHom.observe undefinedValueHom (PUnit.unit : PUnit.{1})
      (PUnit.unit : PUnit.{1}) (fun _ => some 1) = none := by
  change partialIntegral (Measure.dirac (PUnit.unit : PUnit.{1}))
    (fun _ : PUnit.{1} => Value.mul (some 0) none) = none
  rw [partialIntegral_point]
  rfl

/-- A finite-mass program whose direct semantics is checked by an interval proof. -/
def unitInterval : DensityProgram :=
  .weight (fun x => some (if 0 ≤ x ∧ x ≤ 1 then (1 : ℝ) else 0)) .lebesgue

def unitIntervalCertificate : IntervalCertificate unitInterval.density 0 1 1 [] where
  ordered := by norm_num
  total := fun _ => ⟨_, rfl⟩
  away := by
    intro x _
    simp [unitInterval, DensityProgram.density, Value.mul]

theorem unitInterval_semanticMass : unitInterval.semanticMass = some 1 := by
  rw [DensityProgram.semanticMass_eq]
  simpa using unitInterval.mass_interval unitIntervalCertificate

theorem unitInterval_semanticDensityAt :
    unitInterval.semanticDensityAt (1 / 2 : ℝ) = some 1 := by
  rw [DensityProgram.semanticDensityAt_eq]
  norm_num [unitInterval, DensityProgram.density, Value.mul]

/-- The totalized function is integrable zero, but strict mass retains the hole. -/
def hole : DensityProgram :=
  .weight (fun x => if x = 0 then none else some (0 : ℝ)) .lebesgue

theorem hole_totalization_integrable :
    Integrable (fun x => (hole.density x).getD 0) volume := by
  have h : (fun x => (hole.density x).getD 0) = fun _ : ℝ => (0 : ℝ) := by
    funext x
    by_cases hx : x = 0 <;>
      simp [hole, DensityProgram.density, Value.mul, hx]
  rw [h]
  exact integrable_zero _ _ _

theorem hole_semanticDensityAt : hole.semanticDensityAt 0 = none := by
  rw [DensityProgram.semanticDensityAt_eq]
  simp [hole, DensityProgram.density, Value.mul]

theorem hole_semanticMass : hole.semanticMass = none := by
  rw [DensityProgram.semanticMass_eq, DensityProgram.mass, Model.densityMassValue_eq]
  change partialIntegral volume hole.density = none
  apply if_neg
  intro h
  have hd := h.1 0
  simp [hole, DensityProgram.density, Value.mul, Value.Defined] at hd

#qsym_check_axioms PartialFamily.Iso.observe_eq
#qsym_check_axioms PartialFamily.Iso.observeJoint_eq
#qsym_check_axioms PartialHom.observe_pure
#qsym_check_axioms PartialHom.observe_reweight
#qsym_check_axioms PartialHom.ofHom_pure
#qsym_check_axioms PartialHom.ofHom_comp
#qsym_check_axioms PartialHom.ofHom_reweight
#qsym_check_axioms PartialHom.ofHom_observePartial
#qsym_check_axioms PartialHom.ofHom_observeJointPartial
#qsym_check_axioms DensityProgram.semantic_weight
#qsym_check_axioms DensityProgram.semanticDensityAt_eq
#qsym_check_axioms DensityProgram.semanticMass_eq
#qsym_check_axioms DensityProgram.semanticDensityAt_bridge
#qsym_check_axioms DensityProgram.semanticMass_bridge
#qsym_check_axioms zero_weight_preserves_undefined
#qsym_check_axioms unitInterval_semanticMass
#qsym_check_axioms unitInterval_semanticDensityAt
#qsym_check_axioms hole_totalization_integrable
#qsym_check_axioms hole_semanticDensityAt
#qsym_check_axioms hole_semanticMass

end QSym.PartialFibreTests
