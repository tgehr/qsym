import QSym.DistributionModelBridge
import QSym.AxiomCheck

noncomputable section
namespace QSym.DependentReferenceTests
open MeasureTheory WeightedParameter.Fibre
open scoped ProbabilityTheory

theorem generic_fubini (T : DependentIntegralTheory ℝ ℝ) (f : ℝ × ℝ → Option ℝ)
    (hr : T.Rows f) (hi : T.JointL1 f) :
    T.joint f = T.outer (fun y => T.row y (fun z => f (y, z))) := by qsym_rule

theorem generic_forward (T : DependentIntegralTheory ℝ ℝ) (f : ℝ × ℝ → Option ℝ)
    (hr : T.Rows f) :
    Value.Refines (T.joint f) (T.outer (fun y => T.row y (fun z => f (y, z)))) := by
  fail_if_success
    have bad : T.joint f = T.outer (fun y => T.row y (fun z => f (y, z))) := by
      qsym_distribution
  fail_if_success
    have bad : Value.Refines (T.outer (fun y => T.row y (fun z => f (y, z)))) (T.joint f) := by
      qsym_distribution
  qsym_rule

theorem missing_rows_rejected (T : DependentIntegralTheory ℝ ℝ) (f : ℝ × ℝ → Option ℝ)
    (hi : T.JointL1 f) : T.JointL1 f := by
  fail_if_success
    have bad : Value.Refines (T.joint f) (T.outer (fun y => T.row y (fun z => f (y, z)))) := by
      qsym_distribution
  exact hi

theorem concrete_fubini (μ : Measure ℝ) (κ : ProbabilityTheory.Kernel ℝ ℝ)
    [SFinite μ] [ProbabilityTheory.IsSFiniteKernel κ] (f : ℝ × ℝ → Option ℝ)
    (hr : IntegrableEveryRow κ f) (hi : Integrable (fun p => (f p).getD 0) (μ ⊗ₘ κ)) :
    partialIntegral (μ ⊗ₘ κ) f =
      partialIntegral μ (fun y => partialIntegral (κ y) (fun z => f (y, z))) := by qsym_rule

theorem tower_fubini {A B C : Type} (t : Tower ℝ A B C) (x : ℝ) (a : A) (f : C → Option ℝ)
    (hr : t.Rows x a f) (hi : t.JointL1 x a f) :
    t.observe x a f = partialIntegral (t.first.space.reference x) (fun y => t.observeRow x a y f) := by
  qsym_rule

-- Joint L1 alone is insufficient: the false row has zero outer measure, but
-- strict iterated integration still sees its divergent integral.
abbrev ignored : Measure Bool := Measure.dirac true
abbrev realRows : ProbabilityTheory.Kernel Bool ℝ := ProbabilityTheory.Kernel.const Bool volume
def badRow (p : Bool × ℝ) : Option ℝ := some (if p.1 then 0 else 1)

theorem badRow_joint_integrable : Integrable (fun p => (badRow p).getD 0) (ignored ⊗ₘ realRows) := by
  have hm : Measurable (fun p : Bool × ℝ => (badRow p).getD 0) :=
    (measurable_of_finite (fun b : Bool => if b then (0 : ℝ) else 1)).comp measurable_fst
  rw [Measure.integrable_compProd_iff hm.aestronglyMeasurable]
  simp [ignored, realRows, badRow]

theorem badRow_joint : partialIntegral (ignored ⊗ₘ realRows) badRow = some 0 := by
  rw [partialIntegral_valid (ignored ⊗ₘ realRows) badRow (fun _ => ⟨_, rfl⟩) badRow_joint_integrable,
    Measure.integral_compProd badRow_joint_integrable]
  simp [ignored, realRows, badRow]

theorem badRow_nested : partialIntegral ignored
    (fun y => partialIntegral (realRows y) (fun z => badRow (y, z))) = none := by
  have hrow : partialIntegral (realRows false) (fun z => badRow (false, z)) = none := by
    simp [partialIntegral, realRows, badRow, integrable_const_iff, isFiniteMeasure_iff, Real.volume_univ]
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro r h
  have hd := ((partialIntegral_defined_iff _ _).mp ⟨r, h⟩).1 false
  rw [hrow] at hd
  simp only [Value.Defined, reduceCtorEq, exists_false] at hd

theorem no_fubini_from_joint_l1 : ¬ Value.Refines (partialIntegral (ignored ⊗ₘ realRows) badRow)
    (partialIntegral ignored (fun y => partialIntegral (realRows y) (fun z => badRow (y, z)))) := by
  rw [badRow_joint, badRow_nested]
  simp [Value.Refines]

theorem zero_rows (f : Bool × ℝ → Option ℝ) :
    IntegrableEveryRow realRows (fun p => Value.mul (some 0) (f p)) :=
  IntegrableEveryRow.zero_scale realRows f

-- A genuinely dependent reference (second sample is the first sample),
-- unnormalized first reference and signed weights.
abbrev twoAtoms : Measure Bool := Measure.dirac false + Measure.dirac true

-- The reverse obstruction: all row integrals are zero, but absolute mass is
-- infinite. Iterating a signed integral cannot justify flattening it.
abbrev atomRows : ProbabilityTheory.Kernel ℝ Bool := ProbabilityTheory.Kernel.const ℝ twoAtoms
def balanced (p : ℝ × Bool) : Option ℝ := some (if p.2 then 1 else -1)

theorem balanced_rows : IntegrableEveryRow atomRows balanced := by
  intro y
  simp [atomRows, balanced, twoAtoms]

theorem balanced_row (y : ℝ) : partialIntegral (atomRows y) (fun z => balanced (y, z)) = some 0 := by
  norm_num [partialIntegral, Value.Defined, atomRows, balanced, twoAtoms, integral_add_measure]

theorem balanced_variation (y : ℝ) : (∫ z, |(balanced (y, z)).getD 0| ∂atomRows y) = 2 := by
  norm_num [atomRows, balanced, twoAtoms, integral_add_measure]

theorem balanced_not_l1 : ¬ Integrable (fun p => (balanced p).getD 0) (volume ⊗ₘ atomRows) := by
  have hm : Measurable (fun p => (balanced p).getD 0) :=
    (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp measurable_snd
  rw [integrable_compProd_iff_variation volume atomRows balanced balanced_rows hm.aestronglyMeasurable]
  simp only [balanced_variation]
  simp [integrable_const_iff, isFiniteMeasure_iff, Real.volume_univ]

theorem balanced_joint : partialIntegral (volume ⊗ₘ atomRows) balanced = none :=
  partialIntegral_invalid _ _ balanced_not_l1

theorem balanced_nested : partialIntegral volume
    (fun y => partialIntegral (atomRows y) (fun z => balanced (y, z))) = some 0 := by
  simp only [balanced_row, partialIntegral_zero]

theorem no_reverse_fubini : ¬ Value.Refines
    (partialIntegral volume (fun y => partialIntegral (atomRows y) (fun z => balanced (y, z))))
    (partialIntegral (volume ⊗ₘ atomRows) balanced) := by
  rw [balanced_nested, balanced_joint]
  simp [Value.Refines]

def sampleBool : Family PUnit.{1} PUnit.{1} Bool where
  space := Space.ofMeasure Bool twoAtoms
  body := fun _ => ⟨fun _ _ => 1, fun _ b => b⟩

def dependentBool : Family (PUnit.{1} × Bool) Bool Bool where
  space := ⟨Bool, ProbabilityTheory.Kernel.deterministic Prod.snd measurable_snd⟩
  body := fun _ => ⟨fun _ b => if b then 3 else -1, fun _ b => b⟩

def signedTower : Tower PUnit.{1} PUnit.{1} Bool Bool := ⟨sampleBool, dependentBool⟩

theorem signed_integrand (p : Bool × Bool) :
    signedTower.integrand PUnit.unit PUnit.unit (fun _ => some 1) p =
      some (if p.2 then 3 else -1) := by
  change some ((1 * (if p.2 then (3 : ℝ) else -1)) * 1) = _
  rw [one_mul, mul_one]

theorem signed_rows : signedTower.Rows PUnit.unit PUnit.unit (fun _ => some 1) := by
  intro y
  change Integrable (fun z : Bool =>
    (signedTower.integrand PUnit.unit PUnit.unit (fun _ => some 1) (y, z)).getD 0) (Measure.dirac y)
  exact integrable_dirac

theorem signed_joint : signedTower.JointL1 PUnit.unit PUnit.unit (fun _ => some 1) := by
  change Integrable (fun p => (signedTower.integrand PUnit.unit PUnit.unit (fun _ => some 1) p).getD 0)
    ((sampleBool.space.reference ⊗ₖ dependentBool.space.reference) PUnit.unit)
  simp_rw [signed_integrand, Option.getD_some]
  change Integrable (fun p : Bool × Bool => if p.2 then (3 : ℝ) else -1)
    ((ProbabilityTheory.Kernel.const PUnit.{1} twoAtoms ⊗ₖ
      ProbabilityTheory.Kernel.deterministic Prod.snd measurable_snd) PUnit.unit)
  have hm : Measurable (fun p : Bool × Bool => if p.2 then (3 : ℝ) else -1) := measurable_of_finite _
  apply (ProbabilityTheory.integrable_compProd_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro y
    exact integrable_dirac
  · change Integrable _ (Measure.dirac false + Measure.dirac true)
    simp

theorem signed_row (b : Bool) : signedTower.observeRow PUnit.unit PUnit.unit b (fun _ => some 1) =
    some (if b then 3 else -1) := by
  change partialIntegral (Measure.dirac b)
    (fun z : Bool => signedTower.integrand PUnit.unit PUnit.unit (fun _ => some 1) (b, z)) = _
  simp_rw [signed_integrand]
  simp [partialIntegral, Value.Defined]

theorem signed_mass : signedTower.observe PUnit.unit PUnit.unit (fun _ => some 1) = some 2 := by
  rw [Tower.observe_fubini _ _ _ _ signed_rows signed_joint]
  simp_rw [signed_row]
  change partialIntegral (Measure.dirac false + Measure.dirac true) _ = _
  norm_num [partialIntegral, Value.Defined, integral_add_measure]

-- Changing an intermediate null fibre leaves the flattened joint reference
-- unchanged, while the retained row observation still distinguishes it.
def fixedTrue : Family PUnit.{1} PUnit.{1} Bool where
  space := Space.ofMeasure Bool ignored
  body := fun _ => ⟨fun _ _ => 1, fun _ b => b⟩

def constantTrue : Family (PUnit.{1} × Bool) Bool Bool where
  space := Space.ofMeasure Bool (Measure.dirac true)
  body := dependentBool.body

def chosenTower : Tower PUnit.{1} PUnit.{1} Bool Bool := ⟨fixedTrue, dependentBool⟩
def erasedTower : Tower PUnit.{1} PUnit.{1} Bool Bool := ⟨fixedTrue, constantTrue⟩

abbrev chosenReference : ProbabilityTheory.Kernel PUnit.{1} (Bool × Bool) :=
  ProbabilityTheory.Kernel.const PUnit.{1} ignored ⊗ₖ
    ProbabilityTheory.Kernel.deterministic Prod.snd measurable_snd
abbrev erasedReference : ProbabilityTheory.Kernel PUnit.{1} (Bool × Bool) :=
  ProbabilityTheory.Kernel.const PUnit.{1} ignored ⊗ₖ
    ProbabilityTheory.Kernel.const (PUnit.{1} × Bool) (Measure.dirac true)

theorem equal_reference_kernels : chosenReference = erasedReference := by
  apply ProbabilityTheory.Kernel.compProd_congr
  intro x
  simp [ignored, ProbabilityTheory.Kernel.deterministic_apply]

theorem distinct_intermediate_observations :
    chosenTower.observeRow PUnit.unit PUnit.unit false (fun _ => some 1) ≠
      erasedTower.observeRow PUnit.unit PUnit.unit false (fun _ => some 1) := by
  change partialIntegral (Measure.dirac false)
      (fun z : Bool => signedTower.integrand PUnit.unit PUnit.unit (fun _ => some 1) (false, z)) ≠
    partialIntegral (Measure.dirac true)
      (fun z : Bool => signedTower.integrand PUnit.unit PUnit.unit (fun _ => some 1) (false, z))
  simp_rw [signed_integrand]
  norm_num [partialIntegral, Value.Defined]

private theorem family_reference_congr {X Ω A B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    {κ η : ProbabilityTheory.Kernel X Ω}
    [ProbabilityTheory.IsSFiniteKernel κ] [ProbabilityTheory.IsSFiniteKernel η]
    (h : κ = η) (body : X → WeightedParameter.Kernel Ω A B) :
    (⟨⟨Ω, κ⟩, body⟩ : Family X A B) = ⟨⟨Ω, η⟩, body⟩ := by
  cases h
  rfl

theorem equal_flattened_families :
    Hom.ofFamily chosenTower.flatten = Hom.ofFamily erasedTower.flatten :=
  congrArg Hom.ofFamily (family_reference_congr (κ := chosenReference) (η := erasedReference)
    equal_reference_kernels (fun _ : PUnit.{1} =>
      ⟨fun _ : PUnit.{1} => fun p : Bool × Bool => 1 * (if p.2 then 3 else -1), fun _ p => p.2⟩))

theorem no_intermediate_observer_on_flattening :
    ¬ ∃ observe : Hom PUnit.{1} PUnit.{1} Bool → Option ℝ,
      observe (Hom.ofFamily chosenTower.flatten) =
        chosenTower.observeRow PUnit.unit PUnit.unit false (fun _ => some 1) ∧
      observe (Hom.ofFamily erasedTower.flatten) =
        erasedTower.observeRow PUnit.unit PUnit.unit false (fun _ => some 1) := by
  rintro ⟨observe, hc, he⟩
  apply distinct_intermediate_observations
  rw [← hc, ← he, equal_flattened_families]

#qsym_check_axioms Coordinates.dependent
#qsym_check_axioms Coordinates.preserving_dependent
#qsym_check_axioms preserving_depAssoc
#qsym_check_axioms Family.Iso.depComp
#qsym_check_axioms Family.depAssocIso
#qsym_check_axioms Family.depCompUniformIso
#qsym_check_axioms Tower.Iso.flatten
#qsym_check_axioms Tower.Iso.observe_eq
#qsym_check_axioms Tower.Iso.observeRow_eq
#qsym_check_axioms partialIntegral_compProd_of_integrable
#qsym_check_axioms partialIntegral_compProd_refines
#qsym_check_axioms integrable_compProd_iff_variation
#qsym_check_axioms IntegrableEveryRow.scale
#qsym_check_axioms IntegrableEveryRow.zero_scale
#qsym_check_axioms dependentIntegralTheory
#qsym_check_axioms Tower.observe_fubini
#qsym_check_axioms Tower.observe_fubini_refines
#qsym_check_axioms generic_fubini
#qsym_check_axioms generic_forward
#qsym_check_axioms missing_rows_rejected
#qsym_check_axioms concrete_fubini
#qsym_check_axioms tower_fubini
#qsym_check_axioms badRow_joint_integrable
#qsym_check_axioms badRow_joint
#qsym_check_axioms badRow_nested
#qsym_check_axioms no_fubini_from_joint_l1
#qsym_check_axioms zero_rows
#qsym_check_axioms balanced_rows
#qsym_check_axioms balanced_row
#qsym_check_axioms balanced_variation
#qsym_check_axioms balanced_not_l1
#qsym_check_axioms balanced_joint
#qsym_check_axioms balanced_nested
#qsym_check_axioms no_reverse_fubini
#qsym_check_axioms signed_integrand
#qsym_check_axioms signed_rows
#qsym_check_axioms signed_joint
#qsym_check_axioms signed_row
#qsym_check_axioms signed_mass
#qsym_check_axioms equal_reference_kernels
#qsym_check_axioms distinct_intermediate_observations
#qsym_check_axioms equal_flattened_families
#qsym_check_axioms no_intermediate_observer_on_flattening

end QSym.DependentReferenceTests
