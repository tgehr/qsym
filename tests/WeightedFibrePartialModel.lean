import QSym.DistributionPartialSequential
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

theorem unitInterval_rootedMass : unitInterval.rootedSemantic.mass = some 1 := by
  rw [← unitInterval.semanticMass_rooted]
  exact unitInterval_semanticMass

/-- The same unrooted semantics has zero mass at the zero-measure root. -/
theorem unitInterval_zeroRoot_mass :
    (RootedPartialHom.ofPartialHom (μ := (0 : Measure ℝ)) unitInterval.semantic).mass = some 0 := by
  change partialIntegral ((0 : Measure ℝ) ⊗ₘ
    ProbabilityTheory.Kernel.const ℝ (Measure.dirac (PUnit.unit : PUnit.{1})))
    (fun z : ℝ × PUnit.{1} => Value.mul (unitInterval.density z.1) (some 1)) = some 0
  simp [partialIntegral, Value.Defined, unitInterval, DensityProgram.density, Value.mul]

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

theorem hole_rootedMass : hole.rootedSemantic.mass = none := by
  rw [← hole.semanticMass_rooted]
  exact hole_semanticMass

/-- Even a zero root does not erase an undefined point from strict mass. -/
theorem hole_zeroRoot_mass :
    (RootedPartialHom.ofPartialHom (μ := (0 : Measure ℝ)) hole.semantic).mass = none := by
  change partialIntegral ((0 : Measure ℝ) ⊗ₘ
    ProbabilityTheory.Kernel.const ℝ (Measure.dirac (PUnit.unit : PUnit.{1})))
    (fun z : ℝ × PUnit.{1} => Value.mul (hole.density z.1) (some 1)) = none
  simp only [Measure.compProd_zero_left]
  apply if_neg
  intro h
  have hd := h.1 (0, PUnit.unit)
  simp [hole, DensityProgram.density, Value.mul, Value.Defined] at hd

/-- A successful dependent continuation can both reweight and change the value. -/
def weightedBind : DensityBind ℝ := ⟨unitInterval, fun x => some (2, x)⟩

/-- A zero source density must not erase a failing dependent continuation. -/
def failingBind : DensityBind ℝ :=
  ⟨.weight (fun _ => some (0 : ℝ)) .lebesgue, fun _ => none⟩

theorem weightedBind_row (x : ℝ) :
    weightedBind.tower.observeRow x (PUnit.unit : PUnit.{1})
      (PUnit.unit : PUnit.{1}) (fun _ => some 1) =
      Value.mul (unitInterval.density x) (some 2) := by
  rw [DensityBind.observeRow_eq]
  simp [weightedBind, Value.mul]

theorem failingBind_row :
    failingBind.tower.observeRow 0 (PUnit.unit : PUnit.{1})
      (PUnit.unit : PUnit.{1}) (fun _ => some 1) = none := by
  rw [DensityBind.observeRow_eq]
  simp [failingBind, DensityProgram.density, Value.mul]

theorem weightedBind_semanticMass : weightedBind.semanticMass = some 2 := by
  rw [DensityBind.semanticMass_eq]
  simp only [weightedBind, Option.map_some]
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  change partialIntegral volume
    (fun x => Value.mul (unitInterval.density x) (some (2 : ℝ))) = some 2
  have hcomm : (fun x => Value.mul (unitInterval.density x) (some (2 : ℝ))) =
      (fun x => Value.mul (some (2 : ℝ)) (unitInterval.density x)) := by
    funext x
    cases unitInterval.density x <;> simp [Value.mul, mul_comm]
  rw [hcomm, partialIntegral_scale_nonzero volume 2 (by norm_num) unitInterval.density]
  have hm := unitInterval.mass_interval unitIntervalCertificate
  rw [DensityProgram.mass, Model.densityMassValue_eq] at hm
  simp only [Option.some_bind] at hm
  rw [hm]
  simp [Value.mul]

theorem failingBind_semanticMass : failingBind.semanticMass = none := by
  rw [DensityBind.semanticMass_eq, DensityProgram.observe, Model.densityMassValue_eq]
  apply if_neg
  intro h
  have hd := h.1 0
  simp [failingBind, DensityProgram.density, Value.mul, Value.Defined] at hd

theorem weightedBind_presentationMass : massValue weightedBind.presentation = some 2 := by
  rw [← DensityBind.semanticMass_bridge]
  exact weightedBind_semanticMass

theorem failingBind_presentationMass : massValue failingBind.presentation = none := by
  rw [← DensityBind.semanticMass_bridge]
  exact failingBind_semanticMass

#qsym_check_axioms PartialFamily.Iso.observe_eq
#qsym_check_axioms PartialFamily.Iso.observeJoint_eq
#qsym_check_axioms PartialHom.observe_pure
#qsym_check_axioms PartialHom.observe_reweight
#qsym_check_axioms PartialHom.ofHom_pure
#qsym_check_axioms PartialHom.ofHom_comp
#qsym_check_axioms PartialHom.ofHom_reweight
#qsym_check_axioms PartialHom.ofHom_observePartial
#qsym_check_axioms PartialHom.ofHom_observeJointPartial
#qsym_check_axioms PartialHom.observeJoint_reweight
#qsym_check_axioms RootedPartialHom.observe_pure
#qsym_check_axioms RootedPartialHom.observe_reweight
#qsym_check_axioms RootedPartialHom.observeJoint_reweight
#qsym_check_axioms RootedPartialHom.ofTotalHom_observeJoint
#qsym_check_axioms RootedPartialHom.eraseRoot_comp
#qsym_check_axioms RootedPartialHom.mass_eraseRoot
#qsym_check_axioms DensityProgram.semantic_weight
#qsym_check_axioms DensityProgram.rootedSemantic_weight
#qsym_check_axioms DensityProgram.eraseRoot_rootedSemantic
#qsym_check_axioms DensityProgram.semanticMass_rooted
#qsym_check_axioms DensityProgram.semanticDensityAt_eq
#qsym_check_axioms DensityProgram.semanticMass_eq
#qsym_check_axioms DensityProgram.semanticDensityAt_bridge
#qsym_check_axioms DensityProgram.semanticMass_bridge
#qsym_check_axioms zero_weight_preserves_undefined
#qsym_check_axioms unitInterval_semanticMass
#qsym_check_axioms unitInterval_rootedMass
#qsym_check_axioms unitInterval_zeroRoot_mass
#qsym_check_axioms unitInterval_semanticDensityAt
#qsym_check_axioms hole_totalization_integrable
#qsym_check_axioms hole_semanticDensityAt
#qsym_check_axioms hole_semanticMass
#qsym_check_axioms hole_rootedMass
#qsym_check_axioms hole_zeroRoot_mass

#qsym_check_axioms PartialFamily.observe_depCompUniform
#qsym_check_axioms PartialFamily.Iso.depComp
#qsym_check_axioms PartialFamily.ofFamily_depComp_observe
#qsym_check_axioms PartialTower.observe_hom
#qsym_check_axioms PartialTower.eraseRoot_rootedFlatten
#qsym_check_axioms PartialTower.Iso.observe_eq
#qsym_check_axioms PartialTower.Iso.observeRow_eq
#qsym_check_axioms PartialTower.observe_fubini
#qsym_check_axioms PartialTower.observe_fubini_refines
#qsym_check_axioms DensityBind.observeRow_eq
#qsym_check_axioms DensityBind.eraseRoot_rootedSemantic
#qsym_check_axioms DensityBind.mass_continuationPresentation
#qsym_check_axioms DensityBind.semanticMass_eq
#qsym_check_axioms DensityBind.semanticMass_bridge
#qsym_check_axioms weightedBind_row
#qsym_check_axioms failingBind_row
#qsym_check_axioms weightedBind_semanticMass
#qsym_check_axioms failingBind_semanticMass
#qsym_check_axioms weightedBind_presentationMass
#qsym_check_axioms failingBind_presentationMass

end QSym.PartialFibreTests
