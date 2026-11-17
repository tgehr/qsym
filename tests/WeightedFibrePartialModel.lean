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

def primitiveInvalid : PrimitiveProgram ℝ := .invalid
def primitiveZero : PrimitiveProgram ℝ := .zero
def primitiveDiracTwo : PrimitiveProgram ℝ := .dirac 2

theorem primitiveInvalid_semanticMass : primitiveInvalid.semanticMass = none := by
  rw [PrimitiveProgram.semanticMass_eq]
  exact PrimitiveProgram.observe_invalid _

/-- The empty fibre makes zero defined even for an everywhere-undefined test. -/
theorem primitiveZero_observeUndefined :
    primitiveZero.observe (fun _ => none) = some 0 :=
  PrimitiveProgram.observe_zero _

theorem primitiveZero_semanticMass : primitiveZero.semanticMass = some 0 := by
  rw [PrimitiveProgram.semanticMass_eq]
  exact PrimitiveProgram.observe_zero _

theorem primitiveDiracTwo_observeThree :
    primitiveDiracTwo.observe (fun _ => some 3) = some 3 :=
  PrimitiveProgram.observe_dirac 2 _

theorem primitiveDiracTwo_semanticMass : primitiveDiracTwo.semanticMass = some 1 := by
  rw [PrimitiveProgram.semanticMass_eq]
  exact PrimitiveProgram.observe_dirac 2 _

theorem primitiveInvalid_presentationMass : massValue primitiveInvalid.presentation = none := by
  rw [← PrimitiveProgram.semanticMass_bridge]
  exact primitiveInvalid_semanticMass

theorem primitiveZero_presentationObserveUndefined :
    primitiveZero.presentation.bind (fun d => integrate d (fun _ => none)) = some 0 := by
  rw [← PrimitiveProgram.observe_bridge]
  exact primitiveZero_observeUndefined

theorem primitiveDiracTwo_presentationMass : massValue primitiveDiracTwo.presentation = some 1 := by
  rw [← PrimitiveProgram.semanticMass_bridge]
  exact primitiveDiracTwo_semanticMass

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

/-- A continuous unit-square bind with a defined observation on every row. -/
def continuousUnit : ContinuousDensityBind := ⟨unitInterval, fun _ => unitInterval⟩

/-- A zero source weight must not erase an undefined continuous density point. -/
def failingContinuous : ContinuousDensityBind :=
  ⟨.weight (fun _ => some (0 : ℝ)) .lebesgue, fun _ => hole⟩

/-- A zero source followed by a nonintegrable but total continuous density. -/
def zeroContinuous : ContinuousDensityBind :=
  ⟨.weight (fun _ => some (0 : ℝ)) .lebesgue, fun _ => .lebesgue⟩

theorem unitInterval_observe_one : unitInterval.observe (fun _ => some 1) = some 1 := by
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  simp only [Option.some_bind, Value.mul_one_right]
  have hm := unitInterval.mass_interval unitIntervalCertificate
  rw [DensityProgram.mass, Model.densityMassValue_eq] at hm
  norm_num at hm
  simpa only [Option.some_bind] using hm

theorem continuousUnit_rowDefined : continuousUnit.RowDefined (fun _ => some 1) := by
  intro x
  change Value.Defined (unitInterval.observe (fun _ => some 1))
  rw [unitInterval_observe_one]
  exact ⟨1, rfl⟩

theorem continuousUnit_jointL1 : continuousUnit.JointL1 (fun _ => some 1) := by
  unfold ContinuousDensityBind.JointL1
  have hfun : (fun p : ℝ × ℝ =>
      (continuousUnit.rowIntegrand p.1 (fun _ => some 1) p.2).getD 0) =
      (Set.Icc (0 : ℝ) (1 : ℝ) ×ˢ Set.Icc (0 : ℝ) (1 : ℝ)).indicator
        (fun _ => (1 : ℝ)) := by
    funext p
    rcases p with ⟨x, y⟩
    by_cases hx0 : (0 : ℝ) ≤ x <;> by_cases hx1 : x ≤ (1 : ℝ) <;>
      by_cases hy0 : (0 : ℝ) ≤ y <;> by_cases hy1 : y ≤ (1 : ℝ) <;>
      simp [ContinuousDensityBind.rowIntegrand, continuousUnit, unitInterval,
        DensityProgram.density, Value.mul, hx0, hx1, hy0, hy1, Set.indicator,
        Set.mem_Icc, Prod.le_def]
  rw [hfun]
  apply (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).mpr
  have hmeasure : (volume.prod volume)
      (Set.Icc (0 : ℝ) (1 : ℝ) ×ˢ Set.Icc (0 : ℝ) (1 : ℝ)) < ⊤ := by
    rw [Measure.prod_prod]
    simp [Real.volume_Icc]
  exact integrableOn_const.mpr (Or.inr hmeasure)

theorem continuousUnit_row (x : ℝ) :
    continuousUnit.tower.observeRow x (PUnit.unit : PUnit.{1})
      (PUnit.unit : PUnit.{1}) (fun _ => some 1) = unitInterval.density x := by
  rw [ContinuousDensityBind.observeRow_eq_observe _ _ _ (continuousUnit_rowDefined x)]
  change Value.mul (unitInterval.density x) (unitInterval.observe (fun _ => some 1)) = _
  rw [unitInterval_observe_one, Value.mul_one_right]

theorem continuousUnit_semanticMass : continuousUnit.semanticMass = some 1 := by
  rw [ContinuousDensityBind.semanticMass_eq _ continuousUnit_rowDefined continuousUnit_jointL1]
  have hm : unitInterval.mass = some 1 := by
    simpa using unitInterval.mass_interval unitIntervalCertificate
  simpa only [continuousUnit, hm] using unitInterval_observe_one

theorem continuousUnit_presentationMass : massValue continuousUnit.presentation = some 1 := by
  rw [← ContinuousDensityBind.semanticMass_bridge _ continuousUnit_rowDefined continuousUnit_jointL1]
  exact continuousUnit_semanticMass

/-- Constant observations of the unit interval, including zero, are exact. -/
theorem unitInterval_observe_const (c : ℝ) :
    unitInterval.observe (fun _ => some c) = some c := by
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  simp only [Option.some_bind]
  have hm : partialIntegral volume unitInterval.density = some 1 := by
    have hm := unitInterval.mass_interval unitIntervalCertificate
    rw [DensityProgram.mass, Model.densityMassValue_eq] at hm
    norm_num at hm
    simpa only [Option.some_bind] using hm
  have hcomm : (fun x => Value.mul (unitInterval.density x) (some c)) =
      (fun x => Value.mul (some c) (unitInterval.density x)) := by
    funext x
    cases unitInterval.density x <;> simp [Value.mul, mul_comm]
  rw [hcomm, partialIntegral_scale_defined volume c unitInterval.density ⟨1, hm⟩, hm]
  simp [Value.mul]

theorem unitInterval_observe_two : unitInterval.observe (fun _ => some 2) = some 2 :=
  unitInterval_observe_const 2

/-- A non-mass observation of a weighted-Dirac continuation. -/
theorem weightedBind_observeTwo :
    weightedBind.observeJoint (fun _ => some 2) = some 4 := by
  rw [DensityBind.observeJoint_eq]
  have hrow : (fun x => (weightedBind.continuation x).bind fun wx =>
      Value.mul (some wx.1) ((fun _ : ℝ => some (2 : ℝ)) wx.2)) =
      fun _ : ℝ => some (4 : ℝ) := by
    funext x
    norm_num [weightedBind, Value.mul]
  rw [hrow]
  exact unitInterval_observe_const 4

theorem weightedBind_presentationObserveTwo :
    weightedBind.presentation.bind (fun d => integrate d (fun _ => some 2)) = some 4 := by
  rw [← DensityBind.observeJoint_bridge]
  exact weightedBind_observeTwo

theorem continuousUnit_rowDefined_two : continuousUnit.RowDefined (fun _ => some 2) := by
  intro x
  change Value.Defined (unitInterval.observe (fun _ => some 2))
  rw [unitInterval_observe_two]
  exact ⟨2, rfl⟩

theorem continuousUnit_jointL1_two : continuousUnit.JointL1 (fun _ => some 2) := by
  unfold ContinuousDensityBind.JointL1
  have hscale : (fun p : ℝ × ℝ =>
      (continuousUnit.rowIntegrand p.1 (fun _ => some 2) p.2).getD 0) =
      (fun p => (2 : ℝ) *
        (continuousUnit.rowIntegrand p.1 (fun _ => some 1) p.2).getD 0) := by
    funext p
    rcases p with ⟨x, y⟩
    cases hs : continuousUnit.source.density x <;>
      cases hc : (continuousUnit.continuation x).density y <;>
      simp [ContinuousDensityBind.rowIntegrand, hs, hc, Value.mul, mul_comm,
        mul_left_comm, mul_assoc]
  rw [hscale]
  exact continuousUnit_jointL1.const_mul 2

theorem continuousUnit_observeTwo :
    continuousUnit.observeJoint (fun _ => some 2) = some 2 := by
  rw [ContinuousDensityBind.observeJoint_source _ _
    continuousUnit_rowDefined_two continuousUnit_jointL1_two]
  simp only [continuousUnit, unitInterval_observe_two]

theorem continuousUnit_presentationObserveTwo :
    continuousUnit.presentation.bind (fun d => integrate d (fun _ => some 2)) = some 2 := by
  rw [← ContinuousDensityBind.observeJoint_bridge _ _
    continuousUnit_rowDefined_two continuousUnit_jointL1_two]
  exact continuousUnit_observeTwo

/-- A finite dependent integral: the continuation at `x` is the unit interval
reweighted by the source density at `x`. Its joint law is the unit square. -/
def continuousIntegralUnit : ContinuousDensityIntegral :=
  ⟨fun x => .weight (fun _ => unitInterval.density x) unitInterval⟩

theorem continuousIntegralUnit_rowIntegrand (x : ℝ) (f : ℝ → Option ℝ) (y : ℝ) :
    continuousIntegralUnit.rowIntegrand x f y = continuousUnit.rowIntegrand x f y := by
  cases hx : unitInterval.density x <;> cases hy : unitInterval.density y <;>
    cases hf : f y <;>
    simp [ContinuousDensityIntegral.rowIntegrand, ContinuousDensityBind.rowIntegrand,
      continuousIntegralUnit, ContinuousDensityIntegral.toBind, continuousUnit,
      DensityProgram.density, hx, hy, hf, Value.mul, mul_comm, mul_left_comm, mul_assoc]

theorem continuousIntegralUnit_rowDefined :
    continuousIntegralUnit.RowDefined (fun _ => some 1) := by
  intro x
  change Value.Defined ((DensityProgram.weight (fun _ => unitInterval.density x)
    unitInterval).observe (fun _ => some 1))
  rw [DensityProgram.observe_weight_const _ _ _ ⟨1, unitInterval_observe_one⟩,
    unitInterval_observe_one, Value.mul_one_right]
  exact unitIntervalCertificate.total x

theorem continuousIntegralUnit_jointL1 :
    continuousIntegralUnit.JointL1 (fun _ => some 1) := by
  change Integrable (fun p : ℝ × ℝ =>
    (continuousIntegralUnit.rowIntegrand p.1 (fun _ => some 1) p.2).getD 0)
    (volume.prod volume)
  have hfun : (fun p : ℝ × ℝ =>
      (continuousIntegralUnit.rowIntegrand p.1 (fun _ => some 1) p.2).getD 0) =
      (fun p : ℝ × ℝ =>
        (continuousUnit.rowIntegrand p.1 (fun _ => some 1) p.2).getD 0) := by
    funext p
    rcases p with ⟨x, y⟩
    rw [continuousIntegralUnit_rowIntegrand]
  rw [hfun]
  exact continuousUnit_jointL1

/-- The direct joint observer needs no compatibility hypothesis. -/
theorem continuousIntegralUnit_observeJoint (f : ℝ → Option ℝ) :
    continuousIntegralUnit.observeJoint f = continuousUnit.observeJoint f := by
  calc
    continuousIntegralUnit.observeJoint f = partialIntegral (volume.prod volume)
        (fun p => continuousIntegralUnit.rowIntegrand p.1 f p.2) :=
      ContinuousDensityIntegral.observeJoint_eq _ _
    _ = partialIntegral (volume.prod volume)
        (fun p => continuousUnit.rowIntegrand p.1 f p.2) := by
      congr 1
      funext p
      rcases p with ⟨x, y⟩
      exact continuousIntegralUnit_rowIntegrand x f y
    _ = continuousUnit.observeJoint f :=
      (ContinuousDensityBind.observeJoint_eq _ _).symm

theorem continuousIntegralUnit_semanticMass :
    continuousIntegralUnit.semanticMass = some 1 := by
  change continuousIntegralUnit.observeJoint (fun _ => some 1) = some 1
  rw [continuousIntegralUnit_observeJoint]
  exact continuousUnit_semanticMass

theorem continuousIntegralUnit_presentationMass :
    massValue continuousIntegralUnit.presentation = some 1 := by
  rw [← ContinuousDensityIntegral.semanticMass_bridge _
    continuousIntegralUnit_rowDefined continuousIntegralUnit_jointL1]
  exact continuousIntegralUnit_semanticMass

theorem failingContinuous_row :
    failingContinuous.tower.observeRow 0 (PUnit.unit : PUnit.{1})
      (PUnit.unit : PUnit.{1}) (fun _ => some 1) = none := by
  rw [ContinuousDensityBind.observeRow_eq]
  apply if_neg
  intro h
  have hd := h.1 0
  simp [ContinuousDensityBind.rowIntegrand, failingContinuous, hole,
    DensityProgram.density, Value.mul, Value.Defined] at hd

theorem failingContinuous_semanticMass : failingContinuous.semanticMass = none := by
  change failingContinuous.observeJoint (fun _ => some 1) = none
  rw [ContinuousDensityBind.observeJoint_eq]
  apply if_neg
  intro h
  have hd := h.1 (0, 0)
  simp [ContinuousDensityBind.rowIntegrand, failingContinuous, hole,
    DensityProgram.density, Value.mul, Value.Defined] at hd

/-- Joint integration can turn a zero-weighted divergent row into zero. -/
theorem zeroContinuous_semanticMass : zeroContinuous.semanticMass = some 0 := by
  change zeroContinuous.observeJoint (fun _ => some 1) = some 0
  rw [ContinuousDensityBind.observeJoint_eq]
  have hfun : (fun p : ℝ × ℝ => zeroContinuous.rowIntegrand p.1 (fun _ => some 1) p.2) =
      fun _ => some (0 : ℝ) := by
    funext p
    rcases p with ⟨x, y⟩
    simp [ContinuousDensityBind.rowIntegrand, zeroContinuous,
      DensityProgram.density, Value.mul]
  rw [hfun]
  exact partialIntegral_zero _

/-- The old ordered observer still rejects that nonintegrable row. -/
theorem zeroContinuous_presentationMass : massValue zeroContinuous.presentation = none := by
  rw [ContinuousDensityBind.presentation, DensityProgram.bind_mass_bridge]
  have hunbounded : DensityProgram.lebesgue.mass = none := by
    simp [DensityProgram.mass, Model.densityMassValue_eq, DensityProgram.density,
      partialIntegral, Value.Defined, integrable_const_iff, isFiniteMeasure_iff, Real.volume_univ]
  have hm : massValue DensityProgram.lebesgue.presentation = none :=
    DensityProgram.lebesgue.mass_bridge.trans hunbounded
  simp only [zeroContinuous, hm]
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  simp only [Option.some_bind]
  apply if_neg
  intro h
  have hd := h.1 0
  simp [DensityProgram.density, Value.mul, Value.Defined] at hd

theorem zeroContinuous_observers_differ :
    zeroContinuous.semanticMass ≠ massValue zeroContinuous.presentation := by
  rw [zeroContinuous_semanticMass, zeroContinuous_presentationMass]
  simp

/-- Constant scaling acts directly on rooted traces of any source fragment. -/
def scaledUnitInterval : RootedPartialTrace ℝ volume ℝ :=
  RootedPartialHom.scale 2 unitInterval.rootedSemantic

def scaledDiracTwo : RootedPartialTrace PUnit.{1}
    (Measure.dirac (PUnit.unit : PUnit.{1})) ℝ :=
  RootedPartialHom.scale 3 primitiveDiracTwo.rootedSemantic

def zeroScaledHole : RootedPartialTrace ℝ volume ℝ :=
  RootedPartialHom.scale 0 hole.rootedSemantic

def zeroScaledLebesgue : RootedPartialTrace ℝ volume ℝ :=
  RootedPartialHom.scale 0 DensityProgram.lebesgue.rootedSemantic

theorem scaledUnitInterval_semanticMass : scaledUnitInterval.mass = some 2 := by
  rw [scaledUnitInterval, RootedPartialHom.mass_scale_defined _
    _ ⟨1, unitInterval_rootedMass⟩, unitInterval_rootedMass]
  norm_num [Value.mul]

theorem scaledUnitInterval_presentationMass :
    massValue (scaleValue (some 2) unitInterval.presentation) = some 2 := by
  rw [← RootedScale.mass_bridge unitInterval.rootedSemantic 2 unitInterval.presentation
    unitInterval.semanticMass_bridge ⟨1, unitInterval_rootedMass⟩]
  exact scaledUnitInterval_semanticMass

theorem scaledDiracTwo_observeSucc :
    scaledDiracTwo.observeJoint PUnit.unit (fun _ x => some (x + 1)) = some 9 := by
  have hd : Value.Defined (primitiveDiracTwo.rootedSemantic.observeJoint PUnit.unit
      (fun _ x => some (x + 1))) := by
    change Value.Defined (primitiveDiracTwo.observe (fun x => some (x + 1)))
    rw [show primitiveDiracTwo.observe (fun x => some (x + 1)) = some 3 by
      norm_num [primitiveDiracTwo, PrimitiveProgram.observe_dirac]]
    exact ⟨3, rfl⟩
  change (RootedPartialHom.scale 3 primitiveDiracTwo.rootedSemantic).observeJoint
    PUnit.unit (fun _ x => some (x + 1)) = some 9
  rw [RootedPartialHom.observeJoint_scale_defined _ _ _ _ hd]
  change Value.mul (some (3 : ℝ)) (primitiveDiracTwo.observe (fun x => some (x + 1))) = some 9
  norm_num [primitiveDiracTwo, PrimitiveProgram.observe_dirac, Value.mul]

/-- Zero does not erase the source's undefined point under strict scaling. -/
theorem zeroScaledHole_semanticMass : zeroScaledHole.mass = none := by
  change (RootedPartialHom.scale 0 hole.rootedSemantic).observeJoint
    PUnit.unit (fun _ _ => some 1) = none
  rw [RootedPartialHom.observeJoint_scale]
  change partialIntegral (volume ⊗ₘ
    ProbabilityTheory.Kernel.const ℝ (Measure.dirac (PUnit.unit : PUnit.{1})))
    (fun z : ℝ × PUnit.{1} => Value.mul (hole.density z.1)
      (Value.mul (some (0 : ℝ)) (some 1))) = none
  apply if_neg
  intro h
  have hd := h.1 (0, PUnit.unit)
  simp [hole, DensityProgram.density, Value.mul, Value.Defined] at hd

/-- A total source needs no source integrability for direct zero scaling. -/
theorem zeroScaledLebesgue_semanticMass : zeroScaledLebesgue.mass = some 0 := by
  change (RootedPartialHom.scale 0 DensityProgram.lebesgue.rootedSemantic).observeJoint
    PUnit.unit (fun _ _ => some 1) = some 0
  rw [RootedPartialHom.observeJoint_scale]
  change partialIntegral (volume ⊗ₘ
    ProbabilityTheory.Kernel.const ℝ (Measure.dirac (PUnit.unit : PUnit.{1})))
    (fun z : ℝ × PUnit.{1} => Value.mul (DensityProgram.lebesgue.density z.1)
      (Value.mul (some (0 : ℝ)) (some 1))) = some 0
  have hfun : (fun z : ℝ × PUnit.{1} => Value.mul (DensityProgram.lebesgue.density z.1)
      (Value.mul (some (0 : ℝ)) (some 1))) = fun _ => some (0 : ℝ) := by
    funext z
    simp [DensityProgram.density, Value.mul]
  rw [hfun]
  exact partialIntegral_zero _

/-- The old ordered observer rejects the nonintegrable source before scaling. -/
theorem zeroScaledLebesgue_presentationMass :
    massValue (scaleValue (some 0) DensityProgram.lebesgue.presentation) = none := by
  have hunbounded : DensityProgram.lebesgue.mass = none := by
    simp [DensityProgram.mass, Model.densityMassValue_eq, DensityProgram.density,
      partialIntegral, Value.Defined, integrable_const_iff, isFiniteMeasure_iff, Real.volume_univ]
  have hm : massValue DensityProgram.lebesgue.presentation = none :=
    DensityProgram.lebesgue.mass_bridge.trans hunbounded
  rw [mass_scaleValue, hm]
  rfl

theorem zeroScaledLebesgue_observers_differ :
    zeroScaledLebesgue.mass ≠
      massValue (scaleValue (some 0) DensityProgram.lebesgue.presentation) := by
  rw [zeroScaledLebesgue_semanticMass, zeroScaledLebesgue_presentationMass]
  simp

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
#qsym_check_axioms RootedPartialHom.observeJoint_scale
#qsym_check_axioms RootedPartialHom.observeJoint_scale_defined
#qsym_check_axioms RootedPartialHom.ofTotalHom_observeJoint
#qsym_check_axioms RootedPartialHom.eraseRoot_comp
#qsym_check_axioms RootedPartialHom.eraseRoot_scale
#qsym_check_axioms RootedPartialHom.mass_eraseRoot
#qsym_check_axioms RootedPartialHom.mass_scale_defined
#qsym_check_axioms RootedScale.observeJoint_bridge
#qsym_check_axioms RootedScale.mass_bridge
#qsym_check_axioms PrimitiveProgram.eraseRoot_rootedSemantic
#qsym_check_axioms PrimitiveProgram.observe_invalid
#qsym_check_axioms PrimitiveProgram.observe_zero
#qsym_check_axioms PrimitiveProgram.observe_dirac
#qsym_check_axioms PrimitiveProgram.observe_eq
#qsym_check_axioms PrimitiveProgram.observe_bridge
#qsym_check_axioms PrimitiveProgram.semanticMass_eq
#qsym_check_axioms PrimitiveProgram.semanticMass_bridge
#qsym_check_axioms DensityProgram.semantic_weight
#qsym_check_axioms DensityProgram.rootedSemantic_weight
#qsym_check_axioms DensityProgram.eraseRoot_rootedSemantic
#qsym_check_axioms DensityProgram.semanticMass_rooted
#qsym_check_axioms DensityProgram.semanticDensityAt_eq
#qsym_check_axioms DensityProgram.semanticMass_eq
#qsym_check_axioms DensityProgram.semanticDensityAt_bridge
#qsym_check_axioms DensityProgram.semanticMass_bridge
#qsym_check_axioms DensityProgram.observe_bridge
#qsym_check_axioms DensityProgram.observe_weight_const
#qsym_check_axioms DensityProgram.bind_observe_bridge
#qsym_check_axioms DensityProgram.integral_observe_bridge
#qsym_check_axioms DensityProgram.bind_mass_bridge
#qsym_check_axioms DensityProgram.integral_mass_bridge
#qsym_check_axioms zero_weight_preserves_undefined
#qsym_check_axioms primitiveInvalid_semanticMass
#qsym_check_axioms primitiveZero_observeUndefined
#qsym_check_axioms primitiveZero_semanticMass
#qsym_check_axioms primitiveDiracTwo_observeThree
#qsym_check_axioms primitiveDiracTwo_semanticMass
#qsym_check_axioms primitiveInvalid_presentationMass
#qsym_check_axioms primitiveZero_presentationObserveUndefined
#qsym_check_axioms primitiveDiracTwo_presentationMass
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
#qsym_check_axioms PartialFamily.depAssocIso
#qsym_check_axioms PartialFamily.observe_depAssoc
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
#qsym_check_axioms DensityBind.observe_continuationPresentation
#qsym_check_axioms DensityBind.observeJoint_eq
#qsym_check_axioms DensityBind.observeJoint_bridge
#qsym_check_axioms DensityBind.semanticMass_eq
#qsym_check_axioms DensityBind.semanticMass_bridge
#qsym_check_axioms weightedBind_row
#qsym_check_axioms failingBind_row
#qsym_check_axioms weightedBind_semanticMass
#qsym_check_axioms failingBind_semanticMass
#qsym_check_axioms weightedBind_presentationMass
#qsym_check_axioms failingBind_presentationMass
#qsym_check_axioms weightedBind_observeTwo
#qsym_check_axioms weightedBind_presentationObserveTwo

#qsym_check_axioms ContinuousDensityBind.towerFlattenIso
#qsym_check_axioms ContinuousDensityBind.tower_hom
#qsym_check_axioms ContinuousDensityBind.eraseRoot_rootedSemantic
#qsym_check_axioms ContinuousDensityBind.observe_tower
#qsym_check_axioms ContinuousDensityBind.observeRow_eq
#qsym_check_axioms ContinuousDensityBind.observeJoint_eq
#qsym_check_axioms ContinuousDensityBind.observeJoint_iterated
#qsym_check_axioms ContinuousDensityBind.rowIntegral_eq
#qsym_check_axioms ContinuousDensityBind.observeRow_eq_observe
#qsym_check_axioms ContinuousDensityBind.rows_of_rowDefined
#qsym_check_axioms ContinuousDensityBind.observeJoint_source
#qsym_check_axioms ContinuousDensityBind.observeJoint_bridge
#qsym_check_axioms ContinuousDensityBind.semanticMass_eq
#qsym_check_axioms ContinuousDensityBind.semanticMass_bridge
#qsym_check_axioms unitInterval_observe_one
#qsym_check_axioms continuousUnit_rowDefined
#qsym_check_axioms continuousUnit_jointL1
#qsym_check_axioms continuousUnit_row
#qsym_check_axioms continuousUnit_semanticMass
#qsym_check_axioms continuousUnit_presentationMass
#qsym_check_axioms unitInterval_observe_const
#qsym_check_axioms unitInterval_observe_two
#qsym_check_axioms continuousUnit_rowDefined_two
#qsym_check_axioms continuousUnit_jointL1_two
#qsym_check_axioms continuousUnit_observeTwo
#qsym_check_axioms continuousUnit_presentationObserveTwo
#qsym_check_axioms ContinuousDensityIntegral.eraseRoot_rootedSemantic
#qsym_check_axioms ContinuousDensityIntegral.tower_hom
#qsym_check_axioms ContinuousDensityIntegral.observe_tower
#qsym_check_axioms ContinuousDensityIntegral.observeRow_eq
#qsym_check_axioms ContinuousDensityIntegral.observeJoint_eq
#qsym_check_axioms ContinuousDensityIntegral.observeJoint_source
#qsym_check_axioms ContinuousDensityIntegral.observeJoint_bridge
#qsym_check_axioms ContinuousDensityIntegral.semanticMass_eq
#qsym_check_axioms ContinuousDensityIntegral.semanticMass_bridge
#qsym_check_axioms continuousIntegralUnit_rowIntegrand
#qsym_check_axioms continuousIntegralUnit_rowDefined
#qsym_check_axioms continuousIntegralUnit_jointL1
#qsym_check_axioms continuousIntegralUnit_observeJoint
#qsym_check_axioms continuousIntegralUnit_semanticMass
#qsym_check_axioms continuousIntegralUnit_presentationMass
#qsym_check_axioms failingContinuous_row
#qsym_check_axioms failingContinuous_semanticMass
#qsym_check_axioms zeroContinuous_semanticMass
#qsym_check_axioms zeroContinuous_presentationMass
#qsym_check_axioms zeroContinuous_observers_differ
#qsym_check_axioms scaledUnitInterval_semanticMass
#qsym_check_axioms scaledUnitInterval_presentationMass
#qsym_check_axioms scaledDiracTwo_observeSucc
#qsym_check_axioms zeroScaledHole_semanticMass
#qsym_check_axioms zeroScaledLebesgue_semanticMass
#qsym_check_axioms zeroScaledLebesgue_presentationMass
#qsym_check_axioms zeroScaledLebesgue_observers_differ

end QSym.PartialFibreTests
