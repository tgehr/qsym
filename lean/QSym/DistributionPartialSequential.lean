import QSym.DistributionPartialModel
import QSym.DistributionSequentialModel
import QSym.WeightedFibrePartialDependent

/-! Direct partial-fibre semantics for sequential density programs.

Weighted Dirac continuations may fail and return both a real weight and an
arbitrary output value. Continuous continuations instead return a real density
program and retain their own Lebesgue reference. Both source and continuation
fibres remain available in `tower`; flattened families are observation
representatives. Compatibility with the old presentation interpreter is a
proved observer equation, not the semantic route. For continuous programs the
joint observer is primary and iterated presentation compatibility requires
explicit row-definedness and joint-L1 capabilities.
-/
noncomputable section
namespace QSym.Distribution
open MeasureTheory
open scoped ProbabilityTheory
open WeightedParameter.Fibre

/-- A density source followed by a partial weighted deterministic kernel.
The real component of a successful continuation is its weight. -/
structure DensityBind (α : Type) where
  source : DensityProgram
  continuation : ℝ → Option (ℝ × α)

namespace DensityBind
variable {α : Type}

/-- The continuation as a strict partial family over the retained source and
its trivial first latent coordinate. -/
def next (b : DensityBind α) : PartialFamily (ℝ × PUnit.{1}) ℝ α where
  space := Space.point
  body := fun _ =>
    { weight := fun x _ => (b.continuation x).map Prod.fst
      value := fun x _ => (b.continuation x).map Prod.snd }

/-- The direct two-stage semantics, retaining the intermediate source fibre. -/
def tower (b : DensityBind α) : PartialTower ℝ PUnit.{1} ℝ α where
  first := b.source.semanticFamily
  next := b.next

/-- Flattening is only the observation representative of the retained tower. -/
def semanticFamily (b : DensityBind α) : PartialFamily ℝ PUnit.{1} α :=
  b.tower.flatten

def semantic (b : DensityBind α) : PartialHom ℝ PUnit.{1} α := b.tower.hom

def rootedSemantic (b : DensityBind α) : RootedPartialTrace ℝ volume α :=
  b.tower.rootedFlatten volume

/-- Joint observation at the intrinsic root for an arbitrary strict test. -/
def observeJoint (b : DensityBind α) (f : α → Option ℝ) : Option ℝ :=
  b.rootedSemantic.observeJoint PUnit.unit (fun _ a => f a)

def semanticMass (b : DensityBind α) : Option ℝ := b.rootedSemantic.mass

/-- The weighted-Dirac continuation in the old presentation language. This is
used exclusively by compatibility theorems. -/
def continuationPresentation (b : DensityBind α) (x : ℝ) : Option (D α) :=
  (b.continuation x).map fun wx => .scale wx.1 (.dirac wx.2)

def presentation (b : DensityBind α) : Option (D α) :=
  bindValue b.source.presentation (some b.continuationPresentation)

@[simp] theorem eraseRoot_rootedSemantic (b : DensityBind α) :
    b.rootedSemantic.eraseRoot = b.semantic := rfl

@[simp] theorem semanticFamily_eq (b : DensityBind α) :
    b.semantic = PartialHom.ofFamily b.semanticFamily := rfl

/-- A retained source row is exactly a strict weighted-Dirac observation. -/
theorem observeRow_eq (b : DensityBind α) (x : ℝ) (f : α → Option ℝ) :
    b.tower.observeRow x (PUnit.unit : PUnit.{1}) (PUnit.unit : PUnit.{1}) f =
      Value.mul (b.source.density x) ((b.continuation x).bind fun wx =>
        Value.mul (some wx.1) (f wx.2)) := by
  unfold PartialTower.observeRow
  change partialIntegral (Measure.dirac (PUnit.unit : PUnit.{1})) _ = _
  have hpoint : (fun z : PUnit.{1} =>
      b.tower.integrand x (PUnit.unit : PUnit.{1}) f (PUnit.unit, z)) =
      (fun _ : PUnit.{1} => b.tower.integrand x (PUnit.unit : PUnit.{1}) f
        (PUnit.unit, PUnit.unit)) := by
    funext z
    cases z
    rfl
  refine (congrArg (partialIntegral (Measure.dirac (PUnit.unit : PUnit.{1}))) hpoint).trans ?_
  rw [partialIntegral_point]
  cases hk : b.continuation x with
  | none =>
    simp [PartialTower.integrand, tower, next, DensityProgram.semanticFamily,
      densityFamily, PartialTower.flatten, PartialFamily.depComp, hk, Value.mul]
  | some wx =>
    cases hd : b.source.density x <;> cases hf : f wx.2 <;>
      simp [PartialTower.integrand, tower, next, DensityProgram.semanticFamily,
        densityFamily, PartialTower.flatten, PartialFamily.depComp, hk, hd, hf,
        Value.mul, mul_assoc]

@[simp] theorem mass_continuationPresentation (b : DensityBind α) (x : ℝ) :
    massValue (b.continuationPresentation x) = (b.continuation x).map Prod.fst := by
  cases hk : b.continuation x <;>
    simp [continuationPresentation, hk, massValue, integrate, Value.mul]

@[simp] theorem observe_continuationPresentation (b : DensityBind α) (x : ℝ)
    (f : α → Option ℝ) :
    (b.continuationPresentation x).bind (fun d => integrate d f) =
      (b.continuation x).bind fun wx => Value.mul (some wx.1) (f wx.2) := by
  cases hk : b.continuation x <;>
    simp [continuationPresentation, hk, integrate, Value.mul]

/-- Collapse the two trivial latent coordinates in a rooted mass observation. -/
private def realProdPoints : ℝ × (PUnit.{1} × PUnit.{1}) ≃ᵐ ℝ where
  toEquiv :=
    { toFun := Prod.fst
      invFun := fun x => (x, (PUnit.unit, PUnit.unit))
      left_inv := by rintro ⟨x, ⟨⟩, ⟨⟩⟩; rfl
      right_inv := fun _ => rfl }
  measurable_toFun := measurable_fst
  measurable_invFun := measurable_id.prodMk measurable_const

private theorem measurePreserving_realProdPoints :
    MeasurePreserving realProdPoints
      (volume.prod (Measure.dirac (PUnit.unit, PUnit.unit))) volume where
  measurable := realProdPoints.measurable
  map_eq := by
    change Measure.map Prod.fst
      (volume.prod (Measure.dirac (PUnit.unit, PUnit.unit))) = volume
    rw [Measure.prod_dirac, Measure.map_map measurable_fst measurable_prodMk_right]
    exact Measure.map_id

private theorem partialIntegral_realProdPoints (f : ℝ → Option ℝ) :
    partialIntegral (volume.prod (Measure.dirac (PUnit.unit, PUnit.unit)))
      (fun z => f z.1) = partialIntegral volume f :=
  partialIntegral_comp realProdPoints measurePreserving_realProdPoints f

/-- Joint observation is the source density observed against the strict
weighted-Dirac continuation observation. No Fubini or integrability assumption
is needed: both sides are the same integral after removing the two Dirac latent
coordinates. -/
theorem observeJoint_eq (b : DensityBind α) (f : α → Option ℝ) :
    b.observeJoint f = b.source.observe (fun x =>
      (b.continuation x).bind fun wx => Value.mul (some wx.1) (f wx.2)) := by
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  change partialIntegral
      (volume ⊗ₘ ((ProbabilityTheory.Kernel.const ℝ
        (Measure.dirac (PUnit.unit : PUnit.{1}))) ⊗ₖ
       (ProbabilityTheory.Kernel.const (ℝ × PUnit.{1})
        (Measure.dirac (PUnit.unit : PUnit.{1}))))) _ = partialIntegral volume _
  have hκ : ((ProbabilityTheory.Kernel.const ℝ
        (Measure.dirac (PUnit.unit : PUnit.{1}))) ⊗ₖ
      (ProbabilityTheory.Kernel.const (ℝ × PUnit.{1})
        (Measure.dirac (PUnit.unit : PUnit.{1})))) =
      ProbabilityTheory.Kernel.const ℝ
        (Measure.dirac ((PUnit.unit : PUnit.{1}), (PUnit.unit : PUnit.{1}))) := by
    classical
    ext x s hs
    rw [ProbabilityTheory.Kernel.compProd_apply hs]
    simp [Measure.compProd_const, Measure.dirac_prod]
    by_cases hmem : ((PUnit.unit : PUnit.{1}), (PUnit.unit : PUnit.{1})) ∈ s <;>
      simp [Set.indicator, hmem]
  rw [hκ, Measure.compProd_const]
  rw [← partialIntegral_realProdPoints]
  congr 1
  funext z
  rcases z with ⟨x, ⟨⟩, ⟨⟩⟩
  cases hk : b.continuation x with
  | none =>
    cases hd : b.source.density x <;>
      simp [tower, next, DensityProgram.semanticFamily, densityFamily,
        PartialTower.flatten, PartialFamily.depComp, hk, hd, Value.mul]
  | some wx =>
    cases hd : b.source.density x <;> cases hf : f wx.2 <;>
      simp [tower, next, DensityProgram.semanticFamily, densityFamily,
        PartialTower.flatten, PartialFamily.depComp, hk, hd, hf, Value.mul, mul_assoc]

/-- Rooted mass is the mass special case of joint observation. -/
theorem semanticMass_eq (b : DensityBind α) :
    b.semanticMass = b.source.observe (fun x => (b.continuation x).map Prod.fst) := by
  change b.observeJoint (fun _ => some 1) = _
  rw [observeJoint_eq]
  congr 1
  funext x
  cases hk : b.continuation x <;> simp [hk, Value.mul]

/-- Exact compatibility with the old ordered presentation observer for every
strict partial test. -/
theorem observeJoint_bridge (b : DensityBind α) (f : α → Option ℝ) :
    b.observeJoint f = b.presentation.bind (fun d => integrate d f) := by
  rw [presentation, DensityProgram.bind_observe_bridge, observeJoint_eq]
  congr 1
  funext x
  rw [observe_continuationPresentation]

/-- Exact compatibility with the old ordered presentation mass observer. -/
theorem semanticMass_bridge (b : DensityBind α) :
    b.semanticMass = massValue b.presentation := by
  change b.observeJoint (fun _ => some 1) =
    b.presentation.bind (fun d => integrate d (fun _ => some 1))
  exact observeJoint_bridge b _

end DensityBind

/-- A density source followed by a value-dependent continuous real density. -/
structure ContinuousDensityBind where
  source : DensityProgram
  continuation : ℝ → DensityProgram

namespace ContinuousDensityBind

/-- The continuation has its own real latent sample and Lebesgue reference. -/
def next (b : ContinuousDensityBind) : PartialFamily (ℝ × PUnit.{1}) ℝ ℝ where
  space := Space.ofMeasure ℝ volume
  body := fun _ =>
    { weight := fun x y => (b.continuation x).density y
      value := fun _ y => some y }

/-- The direct two-stage semantics, retaining the source and continuation fibres. -/
def tower (b : ContinuousDensityBind) : PartialTower ℝ PUnit.{1} ℝ ℝ where
  first := b.source.semanticFamily
  next := b.next

/-- The strict integrand on a retained source row. -/
def rowIntegrand (b : ContinuousDensityBind) (x : ℝ) (f : ℝ → Option ℝ) (y : ℝ) : Option ℝ :=
  Value.mul (Value.mul (b.source.density x) ((b.continuation x).density y)) (f y)

/-- A flattened representative without the tower's trivial first latent point. -/
def flat (b : ContinuousDensityBind) : PartialFamily ℝ PUnit.{1} ℝ where
  space := Space.ofMeasure ℝ volume
  body := fun x =>
    { weight := fun _ y => Value.mul (b.source.density x) ((b.continuation x).density y)
      value := fun _ y => some y }

/-- Removing the trivial source latent coordinate preserves the dependent reference. -/
def towerFlattenIso (b : ContinuousDensityBind) : PartialFamily.Iso b.tower.flatten b.flat where
  coordinates := Coordinates.const MeasurableEquiv.punitProd
  preserving := by
    intro x
    have hκ : ((ProbabilityTheory.Kernel.const ℝ
          (Measure.dirac (PUnit.unit : PUnit.{1}))) ⊗ₖ
        (ProbabilityTheory.Kernel.const (ℝ × PUnit.{1}) (volume : Measure ℝ))) =
        ProbabilityTheory.Kernel.const ℝ
          ((Measure.dirac (PUnit.unit : PUnit.{1})).prod (volume : Measure ℝ)) := by
      ext z s hs
      rw [ProbabilityTheory.Kernel.compProd_apply hs]
      simp only [ProbabilityTheory.Kernel.const_apply]
      rw [Measure.prod_apply hs]
    change MeasurePreserving MeasurableEquiv.punitProd
      (((ProbabilityTheory.Kernel.const ℝ
        (Measure.dirac (PUnit.unit : PUnit.{1}))) ⊗ₖ
       (ProbabilityTheory.Kernel.const (ℝ × PUnit.{1}) (volume : Measure ℝ))) x) volume
    rw [hκ, ProbabilityTheory.Kernel.const_apply]
    exact WeightedParameter.measurePreserving_punitProd volume
  weight := by
    rintro x _ ⟨u, y⟩
    cases u
    rfl
  value := by
    rintro x _ ⟨u, y⟩
    cases u
    rfl

def semanticFamily (b : ContinuousDensityBind) : PartialFamily ℝ PUnit.{1} ℝ := b.flat

def semantic (b : ContinuousDensityBind) : PartialHom ℝ PUnit.{1} ℝ :=
  PartialHom.ofFamily b.flat

def rootedSemantic (b : ContinuousDensityBind) : RootedPartialTrace ℝ volume ℝ :=
  RootedPartialHom.ofFamily b.flat

/-- Joint observation at the intrinsic root. -/
def observeJoint (b : ContinuousDensityBind) (f : ℝ → Option ℝ) : Option ℝ :=
  b.rootedSemantic.observeJoint PUnit.unit (fun _ y => f y)

def semanticMass (b : ContinuousDensityBind) : Option ℝ := b.rootedSemantic.mass

/-- The old nested presentation is used only at the compatibility boundary. -/
def presentation (b : ContinuousDensityBind) : Option (D ℝ) :=
  bindValue b.source.presentation (some fun x => (b.continuation x).presentation)

@[simp] theorem eraseRoot_rootedSemantic (b : ContinuousDensityBind) :
    b.rootedSemantic.eraseRoot = b.semantic := rfl

/-- Flattening the retained tower gives the same quotient-level semantics. -/
theorem tower_hom (b : ContinuousDensityBind) : b.tower.hom = b.semantic :=
  Quotient.sound ⟨b.towerFlattenIso⟩

@[simp] theorem observe_tower (b : ContinuousDensityBind) (x : ℝ) (f : ℝ → Option ℝ) :
    b.tower.observe x (PUnit.unit : PUnit.{1}) f = b.flat.observe x PUnit.unit f :=
  b.towerFlattenIso.observe_eq x PUnit.unit f

/-- A retained source row is exactly its strict continuous integral. -/
theorem observeRow_eq (b : ContinuousDensityBind) (x : ℝ) (f : ℝ → Option ℝ) :
    b.tower.observeRow x (PUnit.unit : PUnit.{1}) (PUnit.unit : PUnit.{1}) f =
      partialIntegral volume (b.rowIntegrand x f) := by
  unfold PartialTower.observeRow
  change partialIntegral ((ProbabilityTheory.Kernel.const (ℝ × PUnit.{1})
    (volume : Measure ℝ)) (x, PUnit.unit)) _ = _
  rw [ProbabilityTheory.Kernel.const_apply]
  rfl

/-- Every-row L1 and joint L1 remain separate capabilities. -/
def Rows (b : ContinuousDensityBind) (f : ℝ → Option ℝ) : Prop :=
  ∀ x, Integrable (fun y => (b.rowIntegrand x f y).getD 0) volume

def JointL1 (b : ContinuousDensityBind) (f : ℝ → Option ℝ) : Prop :=
  Integrable (fun p : ℝ × ℝ => (b.rowIntegrand p.1 f p.2).getD 0) (volume.prod volume)

/-- Joint observation is a strict integral over the two real coordinates. -/
theorem observeJoint_eq (b : ContinuousDensityBind) (f : ℝ → Option ℝ) :
    b.observeJoint f = partialIntegral (volume.prod volume)
      (fun p => b.rowIntegrand p.1 f p.2) := by
  unfold observeJoint rootedSemantic RootedPartialHom.observeJoint PartialHom.observeJoint
    RootedPartialHom.ofFamily RootedPartialHom.ofPartialHom PartialHom.ofFamily
  rw [Quotient.liftOn_mk]
  unfold PartialFamily.observeJoint flat
  change partialIntegral (volume ⊗ₘ ProbabilityTheory.Kernel.const ℝ (volume : Measure ℝ))
    (fun p : ℝ × ℝ => b.rowIntegrand p.1 f p.2) = _
  rw [Measure.compProd_const]

/-- Guarded Fubini for a flattened continuous observation. -/
theorem observeJoint_iterated (b : ContinuousDensityBind) (f : ℝ → Option ℝ)
    (hr : b.Rows f) (hi : b.JointL1 f) :
    b.observeJoint f = partialIntegral volume
      (fun x => partialIntegral volume (b.rowIntegrand x f)) := by
  unfold observeJoint rootedSemantic RootedPartialHom.observeJoint PartialHom.observeJoint
    RootedPartialHom.ofFamily RootedPartialHom.ofPartialHom PartialHom.ofFamily
  rw [Quotient.liftOn_mk]
  unfold PartialFamily.observeJoint flat
  change partialIntegral (volume ⊗ₘ ProbabilityTheory.Kernel.const ℝ (volume : Measure ℝ))
    (fun p : ℝ × ℝ => b.rowIntegrand p.1 f p.2) = _
  apply partialIntegral_compProd_of_integrable _ _ _
  · exact hr
  · simpa only [Measure.compProd_const] using hi

/-- The continuation observation must be defined on every source row before its
integral can be pulled outside the source weight. -/
def RowDefined (b : ContinuousDensityBind) (f : ℝ → Option ℝ) : Prop :=
  ∀ x, Value.Defined ((b.continuation x).observe f)

/-- Pulling out a source weight is exact when the continuation observation is
defined. This includes zero source weights, but not nonintegrable continuations. -/
theorem rowIntegral_eq (b : ContinuousDensityBind) (x : ℝ) (f : ℝ → Option ℝ)
    (hd : Value.Defined ((b.continuation x).observe f)) :
    partialIntegral volume (b.rowIntegrand x f) =
      Value.mul (b.source.density x) ((b.continuation x).observe f) := by
  rw [DensityProgram.observe, Model.densityMassValue_eq] at hd ⊢
  simp only [Option.some_bind] at hd ⊢
  cases hs : b.source.density x with
  | none =>
    have hrow : b.rowIntegrand x f = fun _ : ℝ => none := by
      funext y
      simp [rowIntegrand, hs, Value.mul]
    rw [hrow]
    simp [partialIntegral, Value.Defined, Value.mul]
  | some d =>
    have hrow : b.rowIntegrand x f = fun y =>
        Value.mul (some d) (Value.mul ((b.continuation x).density y) (f y)) := by
      funext y
      cases hc : (b.continuation x).density y <;> cases hf : f y <;>
        simp [rowIntegrand, hs, hc, hf, Value.mul, mul_assoc]
    rw [hrow]
    exact partialIntegral_scale_defined volume d
      (fun y => Value.mul ((b.continuation x).density y) (f y)) hd

theorem observeRow_eq_observe (b : ContinuousDensityBind) (x : ℝ) (f : ℝ → Option ℝ)
    (hd : Value.Defined ((b.continuation x).observe f)) :
    b.tower.observeRow x (PUnit.unit : PUnit.{1}) (PUnit.unit : PUnit.{1}) f =
      Value.mul (b.source.density x) ((b.continuation x).observe f) := by
  rw [observeRow_eq, rowIntegral_eq b x f hd]

/-- Defined continuation observations supply the every-row L1 capability for
the source-weighted integrand. -/
theorem rows_of_rowDefined (b : ContinuousDensityBind) (f : ℝ → Option ℝ)
    (hd : b.RowDefined f) : b.Rows f := by
  intro x
  have hdi : Integrable
      (fun y => (Value.mul ((b.continuation x).density y) (f y)).getD 0) volume := by
    apply ((partialIntegral_defined_iff volume
      (fun y => Value.mul ((b.continuation x).density y) (f y))).mp ?_).2
    simpa only [DensityProgram.observe, Model.densityMassValue_eq, Option.some_bind] using hd x
  cases hs : b.source.density x with
  | none =>
    have hget : (fun y => (b.rowIntegrand x f y).getD 0) = fun _ : ℝ => (0 : ℝ) := by
      funext y
      simp [rowIntegrand, hs, Value.mul]
    rw [hget]
    exact integrable_zero _ _ _
  | some d =>
    have hget : (fun y => (b.rowIntegrand x f y).getD 0) = fun y =>
        d * (Value.mul ((b.continuation x).density y) (f y)).getD 0 := by
      funext y
      cases hc : (b.continuation x).density y <;> cases hf : f y <;>
        simp [rowIntegrand, hs, hc, hf, Value.mul, mul_assoc]
    rw [hget]
    exact hdi.const_mul d

/-- Under explicit row and joint capabilities, every strict joint observation
agrees with the old ordered source-then-continuation observer. -/
theorem observeJoint_source (b : ContinuousDensityBind) (f : ℝ → Option ℝ)
    (hr : b.RowDefined f) (hi : b.JointL1 f) :
    b.observeJoint f = b.source.observe (fun x => (b.continuation x).observe f) := by
  rw [observeJoint_iterated b _ (b.rows_of_rowDefined _ hr) hi]
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  simp only [Option.some_bind]
  congr 1
  funext x
  rw [rowIntegral_eq b x _ (hr x)]

/-- Exact compatibility with the old presentation observer for an arbitrary
strict partial test, guarded by the same domain capabilities. -/
theorem observeJoint_bridge (b : ContinuousDensityBind) (f : ℝ → Option ℝ)
    (hr : b.RowDefined f) (hi : b.JointL1 f) :
    b.observeJoint f = b.presentation.bind (fun d => integrate d f) := by
  rw [presentation, DensityProgram.bind_observe_bridge,
    observeJoint_source b f hr hi]
  congr 1
  funext x
  rw [DensityProgram.observe_bridge]

private theorem observe_one (p : DensityProgram) : p.observe (fun _ => some 1) = p.mass := by
  rw [DensityProgram.observe, DensityProgram.mass, Model.densityMassValue_eq,
    Model.densityMassValue_eq]
  simp only [Option.some_bind, Value.mul_one_right]

/-- Intrinsic joint mass is the mass special case of ordered observation. -/
theorem semanticMass_eq (b : ContinuousDensityBind)
    (hr : b.RowDefined (fun _ => some 1)) (hi : b.JointL1 (fun _ => some 1)) :
    b.semanticMass = b.source.observe (fun x => (b.continuation x).mass) := by
  change b.observeJoint (fun _ => some 1) = _
  rw [observeJoint_source b _ hr hi]
  congr 1
  funext x
  rw [observe_one]

/-- Exact compatibility with the old presentation mass observer. -/
theorem semanticMass_bridge (b : ContinuousDensityBind)
    (hr : b.RowDefined (fun _ => some 1)) (hi : b.JointL1 (fun _ => some 1)) :
    b.semanticMass = massValue b.presentation := by
  change b.observeJoint (fun _ => some 1) =
    b.presentation.bind (fun d => integrate d (fun _ => some 1))
  exact observeJoint_bridge b _ hr hi

end ContinuousDensityBind

/-- A Lebesgue integral of a value-dependent continuous real density. -/
structure ContinuousDensityIntegral where
  continuation : ℝ → DensityProgram

namespace ContinuousDensityIntegral

/-- The integral is the continuous bind whose source is the Lebesgue density. -/
def toBind (p : ContinuousDensityIntegral) : ContinuousDensityBind :=
  ⟨.lebesgue, p.continuation⟩

/-- The direct two-stage semantics retains the integral and continuation fibres. -/
def tower (p : ContinuousDensityIntegral) : PartialTower ℝ PUnit.{1} ℝ ℝ :=
  p.toBind.tower

/-- The strict integrand on a retained integral row. -/
def rowIntegrand (p : ContinuousDensityIntegral) (x : ℝ)
    (f : ℝ → Option ℝ) (y : ℝ) : Option ℝ :=
  p.toBind.rowIntegrand x f y

def semanticFamily (p : ContinuousDensityIntegral) : PartialFamily ℝ PUnit.{1} ℝ :=
  p.toBind.semanticFamily

def semantic (p : ContinuousDensityIntegral) : PartialHom ℝ PUnit.{1} ℝ :=
  p.toBind.semantic

def rootedSemantic (p : ContinuousDensityIntegral) : RootedPartialTrace ℝ volume ℝ :=
  p.toBind.rootedSemantic

/-- Joint observation at the intrinsic Lebesgue root. -/
def observeJoint (p : ContinuousDensityIntegral) (f : ℝ → Option ℝ) : Option ℝ :=
  p.toBind.observeJoint f

def semanticMass (p : ContinuousDensityIntegral) : Option ℝ := p.toBind.semanticMass

/-- The old integral presentation is used only at the compatibility boundary. -/
def presentation (p : ContinuousDensityIntegral) : Option (D ℝ) :=
  integralValue (some fun x => (p.continuation x).presentation)

/-- Joint L1 remains separate from continuation row-definedness. -/
def JointL1 (p : ContinuousDensityIntegral) (f : ℝ → Option ℝ) : Prop :=
  p.toBind.JointL1 f

/-- Ordered observation additionally requires every continuation observation to
be defined, including on zero-weight and null rows. -/
def RowDefined (p : ContinuousDensityIntegral) (f : ℝ → Option ℝ) : Prop :=
  p.toBind.RowDefined f

@[simp] theorem eraseRoot_rootedSemantic (p : ContinuousDensityIntegral) :
    p.rootedSemantic.eraseRoot = p.semantic := rfl

/-- Flattening the retained tower gives the same quotient-level semantics. -/
theorem tower_hom (p : ContinuousDensityIntegral) : p.tower.hom = p.semantic :=
  p.toBind.tower_hom

@[simp] theorem observe_tower (p : ContinuousDensityIntegral) (x : ℝ)
    (f : ℝ → Option ℝ) :
    p.tower.observe x (PUnit.unit : PUnit.{1}) f =
      p.semanticFamily.observe x PUnit.unit f :=
  p.toBind.observe_tower x f

/-- A retained integral row is exactly its strict continuous integral. -/
theorem observeRow_eq (p : ContinuousDensityIntegral) (x : ℝ) (f : ℝ → Option ℝ) :
    p.tower.observeRow x (PUnit.unit : PUnit.{1}) (PUnit.unit : PUnit.{1}) f =
      partialIntegral volume (p.rowIntegrand x f) :=
  p.toBind.observeRow_eq x f

/-- Joint observation is a strict integral over the two real coordinates. -/
theorem observeJoint_eq (p : ContinuousDensityIntegral) (f : ℝ → Option ℝ) :
    p.observeJoint f = partialIntegral (volume.prod volume)
      (fun z => p.rowIntegrand z.1 f z.2) :=
  p.toBind.observeJoint_eq f

/-- Under explicit row and joint capabilities, direct observation agrees with
the ordered Lebesgue-then-continuation observer. -/
theorem observeJoint_source (p : ContinuousDensityIntegral) (f : ℝ → Option ℝ)
    (hr : p.RowDefined f) (hi : p.JointL1 f) :
    p.observeJoint f = DensityProgram.lebesgue.observe
      (fun x => (p.continuation x).observe f) :=
  p.toBind.observeJoint_source f hr hi

/-- Guarded compatibility with `integralValue` for every strict partial test. -/
theorem observeJoint_bridge (p : ContinuousDensityIntegral) (f : ℝ → Option ℝ)
    (hr : p.RowDefined f) (hi : p.JointL1 f) :
    p.observeJoint f = p.presentation.bind (fun d => integrate d f) := by
  rw [presentation, DensityProgram.integral_observe_bridge,
    observeJoint_source p f hr hi]
  congr 1
  funext x
  rw [DensityProgram.observe_bridge]

/-- Intrinsic joint mass is the mass special case of ordered observation. -/
theorem semanticMass_eq (p : ContinuousDensityIntegral)
    (hr : p.RowDefined (fun _ => some 1)) (hi : p.JointL1 (fun _ => some 1)) :
    p.semanticMass = DensityProgram.lebesgue.observe
      (fun x => (p.continuation x).mass) :=
  p.toBind.semanticMass_eq hr hi

/-- Guarded compatibility with the old `integralValue` mass observer. -/
theorem semanticMass_bridge (p : ContinuousDensityIntegral)
    (hr : p.RowDefined (fun _ => some 1)) (hi : p.JointL1 (fun _ => some 1)) :
    p.semanticMass = massValue p.presentation := by
  change p.observeJoint (fun _ => some 1) =
    p.presentation.bind (fun d => integrate d (fun _ => some 1))
  exact observeJoint_bridge p _ hr hi

end ContinuousDensityIntegral

namespace DensityProgram

/-- Arbitrary strict observation of the direct rooted density semantics. -/
def observeJoint (p : DensityProgram) (f : ℝ → Option ℝ) : Option ℝ :=
  p.rootedSemantic.observeJoint PUnit.unit (fun _ x => f x)

/-- Removing the trivial latent coordinate recovers the source observer. -/
theorem observeJoint_eq (p : DensityProgram) (f : ℝ → Option ℝ) :
    p.observeJoint f = p.observe f := by
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  change partialIntegral
      (volume ⊗ₘ ProbabilityTheory.Kernel.const ℝ (Measure.dirac (PUnit.unit : PUnit.{1})))
      (fun z : ℝ × PUnit.{1} => Value.mul (p.density z.1) (f z.1)) =
    partialIntegral volume (fun x => Value.mul (p.density x) (f x))
  simp only [Measure.compProd_const]
  exact partialIntegral_comp MeasurableEquiv.prodPUnit
    (WeightedParameter.measurePreserving_prodPUnit volume)
    (fun x => Value.mul (p.density x) (f x))

end DensityProgram

/-- Intrinsic roots supported by the currently covered direct source fragments. -/
inductive CoveredRoot where
  | point
  | real

namespace CoveredRoot

def Carrier : CoveredRoot → Type
  | .point => PUnit.{1}
  | .real => ℝ

instance measurable : (r : CoveredRoot) → MeasurableSpace r.Carrier
  | .point => (inferInstance : MeasurableSpace PUnit.{1})
  | .real => (inferInstance : MeasurableSpace ℝ)

def measure : (r : CoveredRoot) → @Measure r.Carrier (measurable r)
  | .point => (Measure.dirac (PUnit.unit : PUnit.{1}) : Measure PUnit.{1})
  | .real => (volume : Measure ℝ)

instance sfinite : (r : CoveredRoot) → SFinite (r.measure)
  | .point => (inferInstance : SFinite (Measure.dirac (PUnit.unit : PUnit.{1})))
  | .real => (inferInstance : SFinite (volume : Measure ℝ))

end CoveredRoot

/-- The covered direct fragment, indexed by its intrinsic root and output type.
Continuous leaves retain their existing restricted continuation types; this is
not an interpreter for arbitrary `Presentation` values or mixed-root addition. -/
inductive CoveredProgram : CoveredRoot → Type → Type 1 where
  | primitive {α : Type} (p : PrimitiveProgram α) : CoveredProgram .point α
  | density (p : DensityProgram) : CoveredProgram .real ℝ
  | bind {α : Type} (b : DensityBind α) : CoveredProgram .real α
  | continuousBind (b : ContinuousDensityBind) : CoveredProgram .real ℝ
  | integral (p : ContinuousDensityIntegral) : CoveredProgram .real ℝ
  | scale {root : CoveredRoot} {α : Type} (r : ℝ)
      (p : CoveredProgram root α) : CoveredProgram root α
  | add {root : CoveredRoot} {α : Type}
      (p q : CoveredProgram root α) : CoveredProgram root α

namespace CoveredProgram
variable {root : CoveredRoot} {α : Type}

/-- One recursive direct semantics; each base case is an existing fragment. -/
def semantic (p : CoveredProgram root α) :
    RootedPartialTrace root.Carrier root.measure α :=
  CoveredProgram.rec
    (motive := fun {r} {a} _ => RootedPartialTrace r.Carrier r.measure a)
    (fun p => p.rootedSemantic)
    (fun p => p.rootedSemantic)
    (fun b => b.rootedSemantic)
    (fun b => b.rootedSemantic)
    (fun p => p.rootedSemantic)
    (fun r _ ih => RootedPartialHom.scale r ih)
    (fun _ _ ihp ihq => RootedPartialHom.add ihp ihq)
    p

/-- Legacy syntax is reconstructed only at the compatibility boundary. -/
def presentation (p : CoveredProgram root α) : Option (D α) :=
  CoveredProgram.rec
    (motive := fun {_} {a} _ => Option (D a))
    (fun p => p.presentation)
    (fun p => p.presentation)
    (fun b => b.presentation)
    (fun b => b.presentation)
    (fun p => p.presentation)
    (fun r _ ih => scaleValue (some r) ih)
    (fun _ _ ihp ihq => addValue ihp ihq)
    p

/-- Arbitrary strict observation of the one direct semantic object. -/
def observe (p : CoveredProgram root α) (f : α → Option ℝ) : Option ℝ :=
  p.semantic.observeJoint PUnit.unit (fun _ a => f a)

def semanticMass (p : CoveredProgram root α) : Option ℝ := p.semantic.mass

/-- Capabilities needed by the existing ordered-observer compatibility proofs.
Addition adds no definedness requirement; scaling retains its source guard. -/
def ObservationCompatible (p : CoveredProgram root α) : (α → Option ℝ) → Prop :=
  CoveredProgram.rec
    (motive := fun {_} {a} _ => (a → Option ℝ) → Prop)
    (fun _ _ => True)
    (fun _ _ => True)
    (fun _ _ => True)
    (fun b f => b.RowDefined f ∧ b.JointL1 f)
    (fun p f => p.RowDefined f ∧ p.JointL1 f)
    (fun _ p ih f => ih f ∧ Value.Defined (p.observe f))
    (fun _ _ ihp ihq f => ihp f ∧ ihq f)
    p

/-- A single compatibility theorem for every covered constructor. -/
theorem observe_bridge (p : CoveredProgram root α) (f : α → Option ℝ)
    (h : p.ObservationCompatible f) :
    p.observe f = p.presentation.bind (fun d => integrate d f) := by
  induction p with
  | primitive p => exact p.observe_bridge f
  | density p => exact (p.observeJoint_eq f).trans (p.observe_bridge f)
  | bind b => exact b.observeJoint_bridge f
  | continuousBind b => exact b.observeJoint_bridge f h.1 h.2
  | integral p => exact p.observeJoint_bridge f h.1 h.2
  | scale r p ih =>
      exact RootedScale.observeJoint_bridge p.semantic r p.presentation f
        (ih f h.1) h.2
  | add p q ihp ihq =>
      exact RootedAdd.observeJoint_bridge p.semantic q.semantic
        p.presentation q.presentation f (ihp f h.1) (ihq f h.2)

/-- Mass compatibility is the unit-test instance of the unified theorem. -/
def MassCompatible (p : CoveredProgram root α) : Prop :=
  p.ObservationCompatible (fun _ => some 1)

theorem semanticMass_eq (p : CoveredProgram root α) :
    p.semanticMass = p.observe (fun _ => some 1) := rfl

theorem semanticMass_bridge (p : CoveredProgram root α) (h : p.MassCompatible) :
    p.semanticMass = massValue p.presentation := by
  change p.observe (fun _ => some 1) =
    p.presentation.bind (fun d => integrate d (fun _ => some 1))
  exact p.observe_bridge _ h

end CoveredProgram
end QSym.Distribution
