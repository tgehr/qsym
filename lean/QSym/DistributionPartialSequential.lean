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

/-- Source-first success of a zero continuation, before any output fibre is
observed. -/
def zeroGuard (p : DensityProgram) : Option PUnit.{1} := by
  classical
  exact if (∀ x, Value.Defined (p.density x)) then some PUnit.unit else none

/-- A zero continuation observes exactly the source's pointwise definedness.
Source integrability is irrelevant because no nonzero output weight is formed. -/
theorem observe_zero (p : DensityProgram) :
    p.observe (fun _ => some 0) = p.zeroGuard.bind fun _ => some 0 := by
  classical
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  simp only [Option.some_bind]
  by_cases hd : ∀ x, Value.Defined (p.density x)
  · have hzero : (fun x => Value.mul (p.density x) (some 0)) =
        fun _ => some (0 : ℝ) := by
      funext x
      have hx := hd x
      cases hp : p.density x <;>
        simp [hp, Value.mul, Value.Defined] at hx ⊢
    rw [hzero, partialIntegral_zero]
    simp [zeroGuard, hd]
  · have hg : p.zeroGuard = none := by simp [zeroGuard, hd]
    rw [hg]
    simp only [Option.none_bind]
    apply if_neg
    intro h
    apply hd
    intro x
    have hx := h.1 x
    cases hp : p.density x <;>
      simp [hp, Value.mul, Value.Defined] at hx ⊢

end DensityProgram

/-- A density source followed by the empty `zero` continuation.  The semantic
output fibre is empty, while `sourceGuard` retains the source-first observation
that legacy `bind` performs before it can return that zero. -/
structure DensityZeroBind (α : Type) where
  source : DensityProgram

namespace DensityZeroBind
variable {α : Type}

/-- Source-first success of the ordered zero continuation. -/
def sourceGuard (b : DensityZeroBind α) : Option PUnit.{1} := b.source.zeroGuard

/-- Empty output fibres plus an explicit source-first strictness guard. -/
def rootedSemantic (b : DensityZeroBind α) :
    GuardedRootedPartialTrace ℝ volume α :=
  GuardedRootedPartialTrace.zero b.sourceGuard

/-- Direct observation is independent of the final test after the guard. -/
def observeJoint (b : DensityZeroBind α) (f : α → Option ℝ) : Option ℝ :=
  b.rootedSemantic.observeJoint (fun _ a => f a)

def semanticMass (b : DensityZeroBind α) : Option ℝ := b.rootedSemantic.mass

/-- The empty output cannot erase failure in the source density. -/
theorem observeJoint_eq (b : DensityZeroBind α) (f : α → Option ℝ) :
    b.observeJoint f = b.source.observe (fun _ => some 0) := by
  change (GuardedRootedPartialTrace.zero b.sourceGuard).observeJoint
    (fun _ a => f a) = _
  rw [GuardedRootedPartialTrace.observeJoint_zero, DensityProgram.observe_zero]
  rfl

theorem semanticMass_eq (b : DensityZeroBind α) :
    b.semanticMass = b.observeJoint (fun _ => some 1) := rfl

/-- Legacy syntax is reconstructed only at the compatibility boundary. -/
def zeroValue : Option (D α) := some .zero

def presentation (b : DensityZeroBind α) : Option (D α) :=
  bindValue b.source.presentation (some fun _ => zeroValue)

/-- Exact arbitrary-test compatibility, with no source mass or integrability
side condition: the old bind likewise observes the source before `zero`. -/
theorem observeJoint_bridge (b : DensityZeroBind α) (f : α → Option ℝ) :
    b.observeJoint f = b.presentation.bind (fun d => integrate d f) := by
  rw [observeJoint_eq, presentation, DensityProgram.bind_observe_bridge]
  rfl

theorem semanticMass_bridge (b : DensityZeroBind α) :
    b.semanticMass = massValue b.presentation := by
  change b.observeJoint (fun _ => some 1) =
    b.presentation.bind (fun d => integrate d (fun _ => some 1))
  exact b.observeJoint_bridge _

end DensityZeroBind

/-- A fixed finite tree of partial weighted Dirac continuations. There is no
empty continuation leaf: an empty latent sum could erase a source failure that
the ordered legacy bind observes before entering the continuation. -/
inductive PointContinuation (A α : Type) where
  | weighted (run : A → Option (ℝ × α))
  | scale (r : ℝ) (rest : PointContinuation A α)
  | add (left right : PointContinuation A α)

namespace PointContinuation
variable {A α : Type}

/-- Ordered strict observation of one continuation, before source integration. -/
def eval (c : PointContinuation A α) (a : A) (f : α → Option ℝ) : Option ℝ :=
  match c with
  | .weighted k => (k a).bind fun wx => Value.mul (some wx.1) (f wx.2)
  | .scale r c => Value.mul (some r) (c.eval a f)
  | .add c d => Value.add (c.eval a f) (d.eval a f)

/-- The old continuation syntax is used only at the compatibility boundary. -/
def presentation (c : PointContinuation A α) (a : A) : Option (D α) :=
  match c with
  | .weighted k => (k a).map fun wx => .scale wx.1 (.dirac wx.2)
  | .scale r c => scaleValue (some r) (c.presentation a)
  | .add c d => addValue (c.presentation a) (d.presentation a)

/-- Finite strict continuation scaling commutes with an arbitrary partial test.
This is a pointwise algebra law, not an unguarded continuous integral law. -/
theorem eval_scale_test (c : PointContinuation A α) (a : A)
    (f : α → Option ℝ) (r : ℝ) :
    c.eval a (fun b => Value.mul (some r) (f b)) =
      Value.mul (some r) (c.eval a f) := by
  induction c generalizing a f with
  | weighted k =>
      cases hk : k a with
      | none => simp [eval, hk, Value.mul]
      | some wx =>
          cases hf : f wx.2 <;>
            simp [eval, hk, hf, Value.mul, mul_assoc, mul_left_comm]
  | scale s c ih =>
      simp only [eval]
      rw [ih]
      cases hc : c.eval a f <;>
        simp [hc, Value.mul, mul_assoc, mul_left_comm]
  | add c d ihc ihd =>
      simp only [eval]
      rw [ihc, ihd]
      cases c.eval a f <;> cases d.eval a f <;>
        simp [Value.mul, Value.add, mul_add]

private theorem integrate_scaleValue (r : ℝ) (d : Option (D α))
    (f : α → Option ℝ) :
    (scaleValue (some r) d).bind (fun a => integrate a f) =
      Value.mul (some r) (d.bind (fun a => integrate a f)) := by
  cases d <;> rfl

private theorem integrate_addValue (a b : Option (D α)) (f : α → Option ℝ) :
    (addValue a b).bind (fun d => integrate d f) =
      Value.add (a.bind (fun d => integrate d f)) (b.bind (fun d => integrate d f)) := by
  cases a <;> cases b <;> simp [addValue, integrate, Value.add]

/-- Every finite continuation observation agrees with its legacy observer. -/
theorem eval_bridge (c : PointContinuation A α) (a : A) (f : α → Option ℝ) :
    c.eval a f = (c.presentation a).bind (fun d => integrate d f) := by
  induction c generalizing a f with
  | weighted k =>
      cases hk : k a <;> simp [eval, presentation, hk, integrate, Value.mul]
  | scale r c ih =>
      simp only [eval, presentation]
      rw [integrate_scaleValue, ← ih]
  | add c d ihc ihd =>
      simp only [eval, presentation]
      rw [integrate_addValue, ← ihc, ← ihd]

end PointContinuation

/-- Primitive sources observe strict addition pointwise, without an
integrability or branch-definedness hypothesis. -/
theorem PrimitiveProgram.observe_add (p : PrimitiveProgram ℝ) (u v : ℝ → Option ℝ) :
    p.observe (fun x => Value.add (u x) (v x)) =
      Value.add (p.observe u) (p.observe v) := by
  cases p <;> simp [Value.add]

/-- Ordered legacy bind over a primitive source agrees with source observation. -/
theorem PrimitiveProgram.bind_observe_bridge (p : PrimitiveProgram ℝ)
    (k : ℝ → Option (D α)) (f : α → Option ℝ) :
    (bindValue p.presentation (some k)).bind (fun d => integrate d f) =
      p.observe (fun x => (k x).bind (fun d => integrate d f)) := by
  cases p <;> simp [PrimitiveProgram.presentation, bindValue, bind, integrate]

/-- A primitive real source followed by a partial weighted deterministic kernel. -/
structure PrimitiveBind (α : Type) where
  source : PrimitiveProgram ℝ
  continuation : ℝ → Option (ℝ × α)

namespace PrimitiveBind
variable {α : Type}

/-- The continuation uses a trivial latent point over each retained source row. -/
def next (b : PrimitiveBind α) : PartialFamily
    (PUnit.{1} × b.source.semanticFamily.space.Carrier) ℝ α where
  space := Space.point
  body := fun _ =>
    { weight := fun x _ => (b.continuation x).map Prod.fst
      value := fun x _ => (b.continuation x).map Prod.snd }

/-- The direct two-stage semantics retains the primitive source fibre. -/
def tower (b : PrimitiveBind α) : PartialTower PUnit.{1} PUnit.{1} ℝ α where
  first := b.source.semanticFamily
  next := b.next

def semanticFamily (b : PrimitiveBind α) : PartialFamily PUnit.{1} PUnit.{1} α :=
  b.tower.flatten

def semantic (b : PrimitiveBind α) : PartialHom PUnit.{1} PUnit.{1} α := b.tower.hom

def rootedSemantic (b : PrimitiveBind α) : RootedPartialTrace PUnit.{1}
    (Measure.dirac (PUnit.unit : PUnit.{1})) α :=
  b.tower.rootedFlatten _

def observeJoint (b : PrimitiveBind α) (f : α → Option ℝ) : Option ℝ :=
  b.rootedSemantic.observeJoint PUnit.unit (fun _ a => f a)

def semanticMass (b : PrimitiveBind α) : Option ℝ := b.rootedSemantic.mass

@[simp] theorem eraseRoot_rootedSemantic (b : PrimitiveBind α) :
    b.rootedSemantic.eraseRoot = b.semantic := rfl

@[simp] theorem semanticFamily_eq (b : PrimitiveBind α) :
    b.semantic = PartialHom.ofFamily b.semanticFamily := rfl

private def pointProdPoints : PUnit.{1} × (PUnit.{1} × PUnit.{1}) ≃ᵐ PUnit.{1} where
  toEquiv :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => (PUnit.unit, (PUnit.unit, PUnit.unit))
      left_inv := by rintro ⟨⟨⟩, ⟨⟩, ⟨⟩⟩; rfl
      right_inv := by intro x; cases x; rfl }
  measurable_toFun := measurable_const
  measurable_invFun := measurable_const

private theorem measurePreserving_pointProdPoints :
    MeasurePreserving pointProdPoints
      (Measure.dirac (PUnit.unit, (PUnit.unit, PUnit.unit)))
      (Measure.dirac (PUnit.unit : PUnit.{1})) where
  measurable := pointProdPoints.measurable
  map_eq := by
    change Measure.map (fun _ : PUnit.{1} × (PUnit.{1} × PUnit.{1}) =>
      (PUnit.unit : PUnit.{1}))
      (Measure.dirac (PUnit.unit, (PUnit.unit, PUnit.unit))) = _
    rw [Measure.map_dirac measurable_const]

private theorem partialIntegral_pointProdPoints
    (g : PUnit.{1} × (PUnit.{1} × PUnit.{1}) → Option ℝ) :
    partialIntegral (Measure.dirac (PUnit.unit, (PUnit.unit, PUnit.unit))) g =
      g (PUnit.unit, (PUnit.unit, PUnit.unit)) := by
  have hpoint : g = fun z => (fun _ : PUnit.{1} =>
      g (PUnit.unit, (PUnit.unit, PUnit.unit))) (pointProdPoints z) := by
    funext z
    rcases z with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
    rfl
  rw [hpoint]
  exact (partialIntegral_comp pointProdPoints measurePreserving_pointProdPoints
    (fun _ : PUnit.{1} => g (PUnit.unit, (PUnit.unit, PUnit.unit)))).trans
    (partialIntegral_point _)

/-- Joint observation is ordered primitive-source observation of the strict
weighted-Dirac continuation. Zero never enters its continuation. -/
theorem observeJoint_eq (b : PrimitiveBind α) (f : α → Option ℝ) :
    b.observeJoint f = b.source.observe (fun x =>
      (b.continuation x).bind fun wx => Value.mul (some wx.1) (f wx.2)) := by
  cases b with
  | mk source k =>
    cases source with
    | invalid =>
      rw [PrimitiveProgram.observe_invalid]
      unfold observeJoint rootedSemantic PartialTower.rootedFlatten
        RootedPartialHom.observeJoint PartialHom.observeJoint RootedPartialHom.ofFamily
        RootedPartialHom.ofPartialHom PartialHom.ofFamily
      rw [Quotient.liftOn_mk]
      unfold PartialFamily.observeJoint
      apply if_neg
      intro h
      have hd := h.1 (PUnit.unit, (PUnit.unit, PUnit.unit))
      simp [tower, next, PrimitiveProgram.semanticFamily, PrimitiveProgram.invalidFamily,
        PartialTower.flatten, PartialFamily.depComp, Value.mul, Value.Defined] at hd
    | zero =>
      rw [PrimitiveProgram.observe_zero]
      unfold observeJoint rootedSemantic PartialTower.rootedFlatten
        RootedPartialHom.observeJoint PartialHom.observeJoint RootedPartialHom.ofFamily
        RootedPartialHom.ofPartialHom PartialHom.ofFamily
      rw [Quotient.liftOn_mk]
      unfold PartialFamily.observeJoint
      change partialIntegral
        ((Measure.dirac (PUnit.unit : PUnit.{1})) ⊗ₘ
          ((ProbabilityTheory.Kernel.const PUnit.{1} (0 : Measure Empty)) ⊗ₖ
           (ProbabilityTheory.Kernel.const (PUnit.{1} × Empty)
            (Measure.dirac (PUnit.unit : PUnit.{1}))))) _ = some 0
      rw [partialIntegral_valid _ _ (fun z => isEmptyElim z.2.1) Integrable.of_isEmpty,
        integral_of_isEmpty]
    | dirac a =>
      rw [PrimitiveProgram.observe_dirac]
      unfold observeJoint rootedSemantic PartialTower.rootedFlatten
        RootedPartialHom.observeJoint PartialHom.observeJoint RootedPartialHom.ofFamily
        RootedPartialHom.ofPartialHom PartialHom.ofFamily
      rw [Quotient.liftOn_mk]
      unfold PartialFamily.observeJoint
      change partialIntegral
        ((Measure.dirac (PUnit.unit : PUnit.{1})) ⊗ₘ
          ((ProbabilityTheory.Kernel.const PUnit.{1}
            (Measure.dirac (PUnit.unit : PUnit.{1}))) ⊗ₖ
           (ProbabilityTheory.Kernel.const (PUnit.{1} × PUnit.{1})
            (Measure.dirac (PUnit.unit : PUnit.{1}))))) _ = _
      have hκ : ((ProbabilityTheory.Kernel.const PUnit.{1}
            (Measure.dirac (PUnit.unit : PUnit.{1}))) ⊗ₖ
          (ProbabilityTheory.Kernel.const (PUnit.{1} × PUnit.{1})
            (Measure.dirac (PUnit.unit : PUnit.{1})))) =
          ProbabilityTheory.Kernel.const PUnit.{1}
            (Measure.dirac ((PUnit.unit : PUnit.{1}), (PUnit.unit : PUnit.{1}))) := by
        classical
        ext x s hs
        rw [ProbabilityTheory.Kernel.compProd_apply hs]
        simp [Measure.compProd_const, Measure.dirac_prod]
        by_cases hmem : ((PUnit.unit : PUnit.{1}), (PUnit.unit : PUnit.{1})) ∈ s <;>
          simp [Set.indicator, hmem]
      rw [hκ, Measure.compProd_const, Measure.dirac_prod_dirac,
        partialIntegral_pointProdPoints]
      cases hk : k a with
      | none =>
        simp [tower, next, PrimitiveProgram.semanticFamily, PrimitiveProgram.diracFamily,
          PartialFamily.pure, PartialKernel.pure, PartialTower.flatten, PartialFamily.depComp,
          hk, Value.mul]
      | some wx =>
        cases hf : f wx.2 <;>
          simp [tower, next, PrimitiveProgram.semanticFamily, PrimitiveProgram.diracFamily,
            PartialFamily.pure, PartialKernel.pure, PartialTower.flatten, PartialFamily.depComp,
            hk, hf, Value.mul]

/-- Rooted mass is the unit-test special case of joint observation. -/
theorem semanticMass_eq (b : PrimitiveBind α) :
    b.semanticMass = b.source.observe (fun x => (b.continuation x).map Prod.fst) := by
  change b.observeJoint (fun _ => some 1) = _
  rw [observeJoint_eq]
  congr 1
  funext x
  cases hk : b.continuation x <;> simp [hk, Value.mul]

end PrimitiveBind

/-- A primitive real source followed by a finite weighted continuation tree. -/
structure PrimitivePointBind (α : Type) where
  source : PrimitiveProgram ℝ
  continuation : PointContinuation ℝ α

namespace PrimitivePointBind
variable {α : Type}

/-- Composite continuations reuse direct rooted scaling and strict addition. -/
def semanticAux (source : PrimitiveProgram ℝ) : PointContinuation ℝ α →
    RootedPartialTrace PUnit.{1} (Measure.dirac (PUnit.unit : PUnit.{1})) α
  | .weighted k => (PrimitiveBind.mk source k).rootedSemantic
  | .scale r c => RootedPartialHom.scale r (semanticAux source c)
  | .add c d => RootedPartialHom.add (semanticAux source c) (semanticAux source d)

def rootedSemantic (b : PrimitivePointBind α) : RootedPartialTrace PUnit.{1}
    (Measure.dirac (PUnit.unit : PUnit.{1})) α :=
  semanticAux b.source b.continuation

def observeJoint (b : PrimitivePointBind α) (f : α → Option ℝ) : Option ℝ :=
  b.rootedSemantic.observeJoint PUnit.unit (fun _ a => f a)

def semanticMass (b : PrimitivePointBind α) : Option ℝ := b.rootedSemantic.mass

/-- Legacy syntax occurs only in this compatibility representation. -/
def presentation (b : PrimitivePointBind α) : Option (D α) :=
  bindValue b.source.presentation (some fun x => b.continuation.presentation x)

/-- Every primitive-source continuation tree has exact ordered observation.
There are no continuous row, integrability, or branch-definedness guards. -/
theorem observeJoint_aux (source : PrimitiveProgram ℝ) (c : PointContinuation ℝ α)
    (f : α → Option ℝ) :
    observeJoint ⟨source, c⟩ f = source.observe (fun x => c.eval x f) := by
  induction c generalizing source f with
  | weighted k => exact PrimitiveBind.observeJoint_eq ⟨source, k⟩ f
  | scale r c ih =>
      change (RootedPartialHom.scale r (semanticAux source c)).observeJoint
        PUnit.unit (fun _ a => f a) = _
      rw [RootedPartialHom.observeJoint_scale]
      change observeJoint ⟨source, c⟩ (fun a => Value.mul (some r) (f a)) = _
      rw [ih source _]
      congr 1
      funext x
      exact PointContinuation.eval_scale_test c x f r
  | add c d ihc ihd =>
      change (RootedPartialHom.add (semanticAux source c) (semanticAux source d)).observeJoint
        PUnit.unit (fun _ a => f a) = _
      rw [RootedPartialHom.observeJoint_add]
      change Value.add (observeJoint ⟨source, c⟩ f) (observeJoint ⟨source, d⟩ f) = _
      rw [ihc source f, ihd source f]
      exact (PrimitiveProgram.observe_add source _ _).symm

theorem observeJoint_eq (b : PrimitivePointBind α) (f : α → Option ℝ) :
    b.observeJoint f = b.source.observe (fun x => b.continuation.eval x f) :=
  observeJoint_aux b.source b.continuation f

/-- Exact compatibility with the ordered legacy observer for every strict test. -/
theorem observeJoint_bridge (b : PrimitivePointBind α) (f : α → Option ℝ) :
    b.observeJoint f = b.presentation.bind (fun d => integrate d f) := by
  rw [presentation, PrimitiveProgram.bind_observe_bridge, observeJoint_eq]
  congr 1
  funext x
  exact PointContinuation.eval_bridge b.continuation x f

theorem semanticMass_eq (b : PrimitivePointBind α) :
    b.semanticMass = b.observeJoint (fun _ => some 1) := rfl

theorem semanticMass_bridge (b : PrimitivePointBind α) :
    b.semanticMass = massValue b.presentation := by
  change b.observeJoint (fun _ => some 1) =
    b.presentation.bind (fun d => integrate d (fun _ => some 1))
  exact b.observeJoint_bridge _

end PrimitivePointBind

/-- Splitting a density observation requires both branch observations to be
defined; otherwise cancellation inside a row could erase nonintegrability. -/
theorem DensityProgram.observe_add (p : DensityProgram) (u v : ℝ → Option ℝ)
    (hu : Value.Defined (p.observe u)) (hv : Value.Defined (p.observe v)) :
    p.observe (fun x => Value.add (u x) (v x)) =
      Value.add (p.observe u) (p.observe v) := by
  simp only [DensityProgram.observe, Model.densityMassValue_eq, Option.some_bind] at hu hv ⊢
  have hdistrib : (fun x => Value.mul (p.density x) (Value.add (u x) (v x))) =
      fun x => Value.add (Value.mul (p.density x) (u x))
        (Value.mul (p.density x) (v x)) := by
    funext x
    cases p.density x <;> cases u x <;> cases v x <;>
      simp [Value.mul, Value.add, mul_add]
  rw [hdistrib]
  exact partialIntegral_add_defined volume _ _ hu hv

/-- A density source followed by a fixed finite weighted-Dirac continuation. -/
structure DensityPointBind (α : Type) where
  source : DensityProgram
  continuation : PointContinuation ℝ α

namespace DensityPointBind
variable {α : Type}

/-- Direct recursive semantics. Composite continuations reuse the strict rooted
scaling and addition operations; no presentation interpretation is involved. -/
def semanticAux (source : DensityProgram) : PointContinuation ℝ α →
    RootedPartialTrace ℝ volume α
  | .weighted k => (DensityBind.mk source k).rootedSemantic
  | .scale r c => RootedPartialHom.scale r (semanticAux source c)
  | .add c d => RootedPartialHom.add (semanticAux source c) (semanticAux source d)

def rootedSemantic (b : DensityPointBind α) : RootedPartialTrace ℝ volume α :=
  semanticAux b.source b.continuation

def observeJoint (b : DensityPointBind α) (f : α → Option ℝ) : Option ℝ :=
  b.rootedSemantic.observeJoint PUnit.unit (fun _ a => f a)

def semanticMass (b : DensityPointBind α) : Option ℝ := b.rootedSemantic.mass

def presentation (b : DensityPointBind α) : Option (D α) :=
  bindValue b.source.presentation (some fun x => b.continuation.presentation x)

/-- Scaling a strict test preserves definedness of a defined direct observation. -/
theorem observeJoint_scale_test_defined (source : DensityProgram)
    (c : PointContinuation ℝ α) (f : α → Option ℝ) (r : ℝ)
    (h : Value.Defined (observeJoint ⟨source, c⟩ f)) :
    Value.Defined (observeJoint ⟨source, c⟩
      (fun a => Value.mul (some r) (f a))) := by
  have heq := RootedPartialHom.observeJoint_scale_defined
    (semanticAux source c) r PUnit.unit (fun _ a => f a) h
  rw [RootedPartialHom.observeJoint_scale] at heq
  change Value.Defined (RootedPartialHom.observeJoint (semanticAux source c)
    PUnit.unit (fun _ a => Value.mul (some r) (f a)))
  rw [heq]
  exact (Value.defined_mul _ _).2 ⟨⟨r, rfl⟩, h⟩

/-- Only continuation addition needs a domain capability: both direct branch
observations must be defined before the shared continuous source can split. -/
def CompatibleAux (source : DensityProgram) (c : PointContinuation ℝ α)
    (f : α → Option ℝ) : Prop :=
  match c with
  | .weighted _ => True
  | .scale _ c => CompatibleAux source c f
  | .add c d => CompatibleAux source c f ∧ CompatibleAux source d f ∧
      Value.Defined (observeJoint ⟨source, c⟩ f) ∧
      Value.Defined (observeJoint ⟨source, d⟩ f)

/-- The addition capabilities remain available after scaling the strict test. -/
theorem compatibleAux_scale_test (source : DensityProgram)
    (c : PointContinuation ℝ α) (f : α → Option ℝ) (r : ℝ)
    (h : CompatibleAux source c f) :
    CompatibleAux source c (fun a => Value.mul (some r) (f a)) := by
  induction c generalizing f with
  | weighted k => trivial
  | scale s c ih => exact ih f h
  | add c d ihc ihd =>
      rcases h with ⟨hc, hd, hcdef, hddef⟩
      exact ⟨ihc f hc, ihd f hd,
        observeJoint_scale_test_defined source c f r hcdef,
        observeJoint_scale_test_defined source d f r hddef⟩

def ObservationCompatible (b : DensityPointBind α) (f : α → Option ℝ) : Prop :=
  CompatibleAux b.source b.continuation f

/-- Direct observation is ordered source integration under the explicit
continuation-addition capabilities. Weighted and scaled nodes need no guard. -/
theorem observeJoint_aux (source : DensityProgram) (c : PointContinuation ℝ α)
    (f : α → Option ℝ) (h : CompatibleAux source c f) :
    observeJoint ⟨source, c⟩ f = source.observe (fun x => c.eval x f) := by
  induction c generalizing source f with
  | weighted k => exact DensityBind.observeJoint_eq ⟨source, k⟩ f
  | scale r c ih =>
      change (RootedPartialHom.scale r (semanticAux source c)).observeJoint
        PUnit.unit (fun _ a => f a) = _
      rw [RootedPartialHom.observeJoint_scale]
      change observeJoint ⟨source, c⟩ (fun a => Value.mul (some r) (f a)) = _
      have h' := compatibleAux_scale_test source c f r h
      rw [ih source _ h']
      congr 1
      funext x
      exact PointContinuation.eval_scale_test c x f r
  | add c d ihc ihd =>
      rcases h with ⟨hc, hd, hcdef, hddef⟩
      change (RootedPartialHom.add (semanticAux source c) (semanticAux source d)).observeJoint
        PUnit.unit (fun _ a => f a) = _
      rw [RootedPartialHom.observeJoint_add]
      change Value.add (observeJoint ⟨source, c⟩ f) (observeJoint ⟨source, d⟩ f) = _
      have hc' : Value.Defined (source.observe fun x => c.eval x f) := by
        rw [← ihc source f hc]
        exact hcdef
      have hd' : Value.Defined (source.observe fun x => d.eval x f) := by
        rw [← ihd source f hd]
        exact hddef
      rw [ihc source f hc, ihd source f hd]
      exact (source.observe_add _ _ hc' hd').symm

theorem observeJoint_eq (b : DensityPointBind α) (f : α → Option ℝ)
    (h : b.ObservationCompatible f) :
    b.observeJoint f = b.source.observe (fun x => b.continuation.eval x f) :=
  observeJoint_aux b.source b.continuation f h

/-- Exact compatibility with the ordered presentation observer. -/
theorem observeJoint_bridge (b : DensityPointBind α) (f : α → Option ℝ)
    (h : b.ObservationCompatible f) :
    b.observeJoint f = b.presentation.bind (fun d => integrate d f) := by
  rw [presentation, DensityProgram.bind_observe_bridge, observeJoint_eq b f h]
  congr 1
  funext x
  exact PointContinuation.eval_bridge b.continuation x f

theorem semanticMass_eq (b : DensityPointBind α) :
    b.semanticMass = b.observeJoint (fun _ => some 1) := rfl

theorem semanticMass_bridge (b : DensityPointBind α)
    (h : b.ObservationCompatible (fun _ => some 1)) :
    b.semanticMass = massValue b.presentation := by
  change b.observeJoint (fun _ => some 1) =
    b.presentation.bind (fun d => integrate d (fun _ => some 1))
  exact b.observeJoint_bridge _ h

end DensityPointBind

/-- A defined source observation can be scaled in the strict test. -/
theorem DensityProgram.observe_scale_test_defined (p : DensityProgram) (r : ℝ)
    (f : ℝ → Option ℝ) (h : Value.Defined (p.observe f)) :
    p.observe (fun x => Value.mul (some r) (f x)) =
      Value.mul (some r) (p.observe f) := by
  simp only [DensityProgram.observe, Model.densityMassValue_eq, Option.some_bind] at h ⊢
  have hrow : (fun x => Value.mul (p.density x) (Value.mul (some r) (f x))) =
      fun x => Value.mul (some r) (Value.mul (p.density x) (f x)) := by
    funext x
    cases p.density x <;> cases f x <;>
      simp [Value.mul, mul_assoc, mul_left_comm]
  rw [hrow]
  exact partialIntegral_scale_defined volume r _ h

namespace ContinuousDensityBind

/-- Scaling a strict test preserves defined continuation rows. -/
theorem rowDefined_scale_test (b : ContinuousDensityBind) (f : ℝ → Option ℝ) (r : ℝ)
    (h : b.RowDefined f) : b.RowDefined (fun y => Value.mul (some r) (f y)) := by
  intro x
  rw [DensityProgram.observe_scale_test_defined _ r f (h x)]
  exact (Value.defined_mul _ _).2 ⟨⟨r, rfl⟩, h x⟩

/-- Scaling a strict test also preserves joint integrability. -/
theorem jointL1_scale_test (b : ContinuousDensityBind) (f : ℝ → Option ℝ) (r : ℝ)
    (h : b.JointL1 f) : b.JointL1 (fun y => Value.mul (some r) (f y)) := by
  unfold JointL1 at h ⊢
  have hrow : (fun p : ℝ × ℝ =>
      (b.rowIntegrand p.1 (fun y => Value.mul (some r) (f y)) p.2).getD 0) =
      fun p => r * (b.rowIntegrand p.1 f p.2).getD 0 := by
    funext p
    rcases p with ⟨x, y⟩
    cases hs : b.source.density x <;> cases hc : (b.continuation x).density y <;>
      cases hf : f y <;>
      simp [rowIntegrand, hs, hc, hf, Value.mul, mul_assoc, mul_left_comm]
  rw [hrow]
  exact h.const_mul r

end ContinuousDensityBind

/-- A finite continuation tree with both weighted-Dirac and continuous-density
leaves. Continuous leaves return real values; weighted leaves remain polymorphic. -/
inductive DensityContinuation : Type → Type 1 where
  | weighted {α : Type} (run : ℝ → Option (ℝ × α)) : DensityContinuation α
  | continuous (run : ℝ → DensityProgram) : DensityContinuation ℝ
  | scale {α : Type} (r : ℝ) (rest : DensityContinuation α) : DensityContinuation α
  | add {α : Type} (left right : DensityContinuation α) : DensityContinuation α

namespace DensityContinuation
variable {α : Type}

/-- Ordered strict observation before integration over the shared source. -/
def eval (c : DensityContinuation α) (x : ℝ) (f : α → Option ℝ) : Option ℝ :=
  DensityContinuation.rec
    (motive := fun {α} _ => ℝ → (α → Option ℝ) → Option ℝ)
    (fun k x f => (k x).bind fun wx => Value.mul (some wx.1) (f wx.2))
    (fun k x f => (k x).observe f)
    (fun r _ ih x f => Value.mul (some r) (ih x f))
    (fun _ _ ihc ihd x f => Value.add (ihc x f) (ihd x f))
    c x f

/-- Legacy continuation syntax is reconstructed only for compatibility. -/
def presentation (c : DensityContinuation α) (x : ℝ) : Option (D α) :=
  DensityContinuation.rec
    (motive := fun {α} _ => ℝ → Option (D α))
    (fun k x => (k x).map fun wx => .scale wx.1 (.dirac wx.2))
    (fun k x => (k x).presentation)
    (fun r _ ih x => scaleValue (some r) (ih x))
    (fun _ _ ihc ihd x => addValue (ihc x) (ihd x))
    c x

private theorem integrate_scaleValue (r : ℝ) (d : Option (D α))
    (f : α → Option ℝ) :
    (scaleValue (some r) d).bind (fun a => integrate a f) =
      Value.mul (some r) (d.bind (fun a => integrate a f)) := by
  cases d <;> rfl

private theorem integrate_addValue (a b : Option (D α)) (f : α → Option ℝ) :
    (addValue a b).bind (fun d => integrate d f) =
      Value.add (a.bind (fun d => integrate d f)) (b.bind (fun d => integrate d f)) := by
  cases a <;> cases b <;> simp [addValue, integrate, Value.add]

/-- Ordered row observation agrees with the legacy observer for every leaf. -/
theorem eval_bridge (c : DensityContinuation α) (x : ℝ) (f : α → Option ℝ) :
    c.eval x f = (c.presentation x).bind (fun d => integrate d f) := by
  induction c generalizing x with
  | weighted k =>
      cases hk : k x <;> simp [eval, presentation, hk, integrate, Value.mul]
  | continuous k => exact DensityProgram.observe_bridge (k x) f
  | scale r c ih =>
      change Value.mul (some r) (c.eval x f) =
        (scaleValue (some r) (c.presentation x)).bind (fun d => integrate d f)
      rw [integrate_scaleValue, ← ih]
  | add c d ihc ihd =>
      change Value.add (c.eval x f) (d.eval x f) =
        (addValue (c.presentation x) (d.presentation x)).bind (fun d => integrate d f)
      rw [integrate_addValue, ← ihc, ← ihd]

end DensityContinuation

/-- A density source followed by a finite mixed continuation tree. -/
structure DensityContinuationBind (α : Type) where
  source : DensityProgram
  continuation : DensityContinuation α

namespace DensityContinuationBind
variable {α : Type}

/-- Direct recursive semantics; no compatibility observer is used here. -/
def semanticAux (source : DensityProgram) (c : DensityContinuation α) :
    RootedPartialTrace ℝ volume α :=
  DensityContinuation.rec
    (motive := fun {α} _ => RootedPartialTrace ℝ volume α)
    (fun k => (DensityBind.mk source k).rootedSemantic)
    (fun k => (ContinuousDensityBind.mk source k).rootedSemantic)
    (fun r _ ih => RootedPartialHom.scale r ih)
    (fun _ _ ihc ihd => RootedPartialHom.add ihc ihd)
    c

def rootedSemantic (b : DensityContinuationBind α) : RootedPartialTrace ℝ volume α :=
  semanticAux b.source b.continuation

def observeJoint (b : DensityContinuationBind α) (f : α → Option ℝ) : Option ℝ :=
  b.rootedSemantic.observeJoint PUnit.unit (fun _ a => f a)

def semanticMass (b : DensityContinuationBind α) : Option ℝ := b.rootedSemantic.mass

def presentation (b : DensityContinuationBind α) : Option (D α) :=
  bindValue b.source.presentation (some fun x => b.continuation.presentation x)

/-- Scaling a strict test preserves a defined direct mixed observation. -/
theorem observeJoint_scale_test_defined (source : DensityProgram)
    (c : DensityContinuation α) (f : α → Option ℝ) (r : ℝ)
    (h : Value.Defined (observeJoint ⟨source, c⟩ f)) :
    Value.Defined (observeJoint ⟨source, c⟩
      (fun a => Value.mul (some r) (f a))) := by
  have heq := RootedPartialHom.observeJoint_scale_defined
    (semanticAux source c) r PUnit.unit (fun _ a => f a) h
  rw [RootedPartialHom.observeJoint_scale] at heq
  change Value.Defined (RootedPartialHom.observeJoint (semanticAux source c)
    PUnit.unit (fun _ a => Value.mul (some r) (f a)))
  rw [heq]
  exact (Value.defined_mul _ _).2 ⟨⟨r, rfl⟩, h⟩

/-- Continuous leaves retain their row and joint capabilities. Addition adds
exactly the two direct branch-definedness capabilities needed to split the source. -/
def CompatibleAux (source : DensityProgram) (c : DensityContinuation α)
    (f : α → Option ℝ) : Prop :=
  DensityContinuation.rec
    (motive := fun {α} _ => (α → Option ℝ) → Prop)
    (fun _ _ => True)
    (fun k f => (ContinuousDensityBind.mk source k).RowDefined f ∧
      (ContinuousDensityBind.mk source k).JointL1 f)
    (fun _ _ ih f => ih f)
    (fun c d ihc ihd f => ihc f ∧ ihd f ∧
      Value.Defined (observeJoint ⟨source, c⟩ f) ∧
      Value.Defined (observeJoint ⟨source, d⟩ f))
    c f

/-- All leaf and addition capabilities survive scaling of the strict test. -/
theorem compatibleAux_scale_test (source : DensityProgram)
    (c : DensityContinuation α) (f : α → Option ℝ) (r : ℝ)
    (h : CompatibleAux source c f) :
    CompatibleAux source c (fun a => Value.mul (some r) (f a)) := by
  induction c with
  | weighted k => trivial
  | continuous k =>
      exact ⟨(ContinuousDensityBind.mk source k).rowDefined_scale_test f r h.1,
        (ContinuousDensityBind.mk source k).jointL1_scale_test f r h.2⟩
  | scale s c ih => exact ih f h
  | add c d ihc ihd =>
      rcases h with ⟨hc, hd, hcdef, hddef⟩
      exact ⟨ihc f hc, ihd f hd,
        observeJoint_scale_test_defined source c f r hcdef,
        observeJoint_scale_test_defined source d f r hddef⟩

/-- Under the row capabilities, scaling commutes with ordered continuation
observation. The weighted and finite-addition cases need no integrability guard. -/
theorem eval_scale_test (source : DensityProgram) (c : DensityContinuation α)
    (x : ℝ) (f : α → Option ℝ) (r : ℝ) (h : CompatibleAux source c f) :
    c.eval x (fun a => Value.mul (some r) (f a)) =
      Value.mul (some r) (c.eval x f) := by
  induction c generalizing x with
  | weighted k =>
      cases hk : k x with
      | none => simp [DensityContinuation.eval, hk, Value.mul]
      | some wx =>
          cases hf : f wx.2 <;>
            simp [DensityContinuation.eval, hk, hf, Value.mul, mul_assoc, mul_left_comm]
  | continuous k =>
      exact DensityProgram.observe_scale_test_defined (k x) r f (h.1 x)
  | scale s c ih =>
      change Value.mul (some s)
        (c.eval x (fun a => Value.mul (some r) (f a))) =
        Value.mul (some r) (Value.mul (some s) (c.eval x f))
      rw [ih x f h]
      cases hc : c.eval x f <;>
        simp [hc, Value.mul, mul_assoc, mul_left_comm]
  | add c d ihc ihd =>
      change Value.add (c.eval x (fun a => Value.mul (some r) (f a)))
        (d.eval x (fun a => Value.mul (some r) (f a))) =
        Value.mul (some r) (Value.add (c.eval x f) (d.eval x f))
      rw [ihc x f h.1, ihd x f h.2.1]
      cases c.eval x f <;> cases d.eval x f <;>
        simp [Value.mul, Value.add, mul_add]

def ObservationCompatible (b : DensityContinuationBind α) (f : α → Option ℝ) : Prop :=
  CompatibleAux b.source b.continuation f

/-- Direct mixed observation is ordered source integration under the explicit
leaf and continuation-addition capabilities. -/
theorem observeJoint_aux (source : DensityProgram) (c : DensityContinuation α)
    (f : α → Option ℝ) (h : CompatibleAux source c f) :
    observeJoint ⟨source, c⟩ f = source.observe (fun x => c.eval x f) := by
  induction c generalizing source with
  | weighted k => exact DensityBind.observeJoint_eq ⟨source, k⟩ f
  | continuous k => exact ContinuousDensityBind.observeJoint_source ⟨source, k⟩ f h.1 h.2
  | scale r c ih =>
      change (RootedPartialHom.scale r (semanticAux source c)).observeJoint
        PUnit.unit (fun _ a => f a) = _
      rw [RootedPartialHom.observeJoint_scale]
      change observeJoint ⟨source, c⟩ (fun a => Value.mul (some r) (f a)) = _
      have h' := compatibleAux_scale_test source c f r h
      rw [ih source _ h']
      congr 1
      funext x
      exact eval_scale_test source c x f r h
  | add c d ihc ihd =>
      rcases h with ⟨hc, hd, hcdef, hddef⟩
      change (RootedPartialHom.add (semanticAux source c) (semanticAux source d)).observeJoint
        PUnit.unit (fun _ a => f a) = _
      rw [RootedPartialHom.observeJoint_add]
      change Value.add (observeJoint ⟨source, c⟩ f) (observeJoint ⟨source, d⟩ f) = _
      have hc' : Value.Defined (source.observe fun x => c.eval x f) := by
        rw [← ihc source f hc]
        exact hcdef
      have hd' : Value.Defined (source.observe fun x => d.eval x f) := by
        rw [← ihd source f hd]
        exact hddef
      rw [ihc source f hc, ihd source f hd]
      exact (source.observe_add _ _ hc' hd').symm

theorem observeJoint_eq (b : DensityContinuationBind α) (f : α → Option ℝ)
    (h : b.ObservationCompatible f) :
    b.observeJoint f = b.source.observe (fun x => b.continuation.eval x f) :=
  observeJoint_aux b.source b.continuation f h

/-- Exact compatibility with the ordered legacy observer. -/
theorem observeJoint_bridge (b : DensityContinuationBind α) (f : α → Option ℝ)
    (h : b.ObservationCompatible f) :
    b.observeJoint f = b.presentation.bind (fun d => integrate d f) := by
  rw [presentation, DensityProgram.bind_observe_bridge, observeJoint_eq b f h]
  congr 1
  funext x
  exact DensityContinuation.eval_bridge b.continuation x f

theorem semanticMass_eq (b : DensityContinuationBind α) :
    b.semanticMass = b.observeJoint (fun _ => some 1) := rfl

theorem semanticMass_bridge (b : DensityContinuationBind α)
    (h : b.ObservationCompatible (fun _ => some 1)) :
    b.semanticMass = massValue b.presentation := by
  change b.observeJoint (fun _ => some 1) =
    b.presentation.bind (fun d => integrate d (fun _ => some 1))
  exact b.observeJoint_bridge _ h

end DensityContinuationBind

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
  | primitiveBind {α : Type} (b : PrimitivePointBind α) : CoveredProgram .point α
  | density (p : DensityProgram) : CoveredProgram .real ℝ
  | bind {α : Type} (b : DensityBind α) : CoveredProgram .real α
  | pointBind {α : Type} (b : DensityPointBind α) : CoveredProgram .real α
  | continuationBind {α : Type} (b : DensityContinuationBind α) : CoveredProgram .real α
  | zeroBind {α : Type} (b : DensityZeroBind α) : CoveredProgram .real α
  | continuousBind (b : ContinuousDensityBind) : CoveredProgram .real ℝ
  | integral (p : ContinuousDensityIntegral) : CoveredProgram .real ℝ
  | scale {root : CoveredRoot} {α : Type} (r : ℝ)
      (p : CoveredProgram root α) : CoveredProgram root α
  | add {root : CoveredRoot} {α : Type}
      (p q : CoveredProgram root α) : CoveredProgram root α

namespace CoveredProgram
variable {root : CoveredRoot} {α : Type}

/-- One recursive direct semantics; each nonempty base case keeps its previous
rooted trace under a defined source guard, while zero binds supply their own
source-first guard. -/
def semantic (p : CoveredProgram root α) :
    GuardedRootedPartialTrace root.Carrier root.measure α :=
  CoveredProgram.rec
    (motive := fun {r} {a} _ => GuardedRootedPartialTrace r.Carrier r.measure a)
    (fun p => GuardedRootedPartialTrace.ofTrace p.rootedSemantic)
    (fun b => GuardedRootedPartialTrace.ofTrace b.rootedSemantic)
    (fun p => GuardedRootedPartialTrace.ofTrace p.rootedSemantic)
    (fun b => GuardedRootedPartialTrace.ofTrace b.rootedSemantic)
    (fun b => GuardedRootedPartialTrace.ofTrace b.rootedSemantic)
    (fun b => GuardedRootedPartialTrace.ofTrace b.rootedSemantic)
    (fun b => b.rootedSemantic)
    (fun b => GuardedRootedPartialTrace.ofTrace b.rootedSemantic)
    (fun p => GuardedRootedPartialTrace.ofTrace p.rootedSemantic)
    (fun r _ ih => GuardedRootedPartialTrace.scale r ih)
    (fun _ _ ihp ihq => GuardedRootedPartialTrace.add ihp ihq)
    p

/-- Legacy syntax is reconstructed only at the compatibility boundary. -/
def presentation (p : CoveredProgram root α) : Option (D α) :=
  CoveredProgram.rec
    (motive := fun {_} {a} _ => Option (D a))
    (fun p => p.presentation)
    (fun b => b.presentation)
    (fun p => p.presentation)
    (fun b => b.presentation)
    (fun b => b.presentation)
    (fun b => b.presentation)
    (fun b => b.presentation)
    (fun b => b.presentation)
    (fun p => p.presentation)
    (fun r _ ih => scaleValue (some r) ih)
    (fun _ _ ihp ihq => addValue ihp ihq)
    p

/-- Arbitrary strict observation of the one direct semantic object. -/
def observe (p : CoveredProgram root α) (f : α → Option ℝ) : Option ℝ :=
  p.semantic.observeJoint (fun _ a => f a)

def semanticMass (p : CoveredProgram root α) : Option ℝ := p.semantic.mass

/-- Capabilities needed by the existing ordered-observer compatibility proofs.
Addition adds no definedness requirement; scaling retains its source guard. -/
def ObservationCompatible (p : CoveredProgram root α) : (α → Option ℝ) → Prop :=
  CoveredProgram.rec
    (motive := fun {_} {a} _ => (a → Option ℝ) → Prop)
    (fun _ _ => True)
    (fun _ _ => True)
    (fun _ _ => True)
    (fun _ _ => True)
    (fun b f => b.ObservationCompatible f)
    (fun b f => b.ObservationCompatible f)
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
  | primitiveBind b => exact b.observeJoint_bridge f
  | density p => exact (p.observeJoint_eq f).trans (p.observe_bridge f)
  | bind b => exact b.observeJoint_bridge f
  | pointBind b => exact b.observeJoint_bridge f h
  | continuationBind b => exact b.observeJoint_bridge f h
  | zeroBind b => exact b.observeJoint_bridge f
  | continuousBind b => exact b.observeJoint_bridge f h.1 h.2
  | integral p => exact p.observeJoint_bridge f h.1 h.2
  | scale r p ih =>
      exact GuardedScale.observeJoint_bridge p.semantic r p.presentation f
        (ih f h.1) h.2
  | add p q ihp ihq =>
      exact GuardedAdd.observeJoint_bridge p.semantic q.semantic
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
