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

/-- Rooted mass is the source density observed against continuation mass.
No Fubini or integrability assumption is needed: both sides are the same strict
integral after removing the two Dirac latent coordinates. -/
theorem semanticMass_eq (b : DensityBind α) :
    b.semanticMass = b.source.observe (fun x => (b.continuation x).map Prod.fst) := by
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
  cases hk : b.continuation x <;>
    cases hd : b.source.density x <;>
      simp [tower, next, DensityProgram.semanticFamily, densityFamily,
        PartialTower.flatten, PartialFamily.depComp, hk, hd, Value.mul]

/-- Exact compatibility with the old ordered presentation observer. -/
theorem semanticMass_bridge (b : DensityBind α) :
    b.semanticMass = massValue b.presentation := by
  rw [presentation, DensityProgram.bind_mass_bridge, semanticMass_eq]
  congr 1
  funext x
  exact (b.mass_continuationPresentation x).symm

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

private theorem observe_one (p : DensityProgram) : p.observe (fun _ => some 1) = p.mass := by
  rw [DensityProgram.observe, DensityProgram.mass, Model.densityMassValue_eq,
    Model.densityMassValue_eq]
  simp only [Option.some_bind, Value.mul_one_right]

/-- Under explicit row and joint capabilities, intrinsic joint mass agrees with
the old ordered source-then-continuation observer. -/
theorem semanticMass_eq (b : ContinuousDensityBind)
    (hr : b.RowDefined (fun _ => some 1)) (hi : b.JointL1 (fun _ => some 1)) :
    b.semanticMass = b.source.observe (fun x => (b.continuation x).mass) := by
  change b.observeJoint (fun _ => some 1) = _
  rw [observeJoint_iterated b _ (b.rows_of_rowDefined _ hr) hi]
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  simp only [Option.some_bind]
  congr 1
  funext x
  rw [rowIntegral_eq b x _ (hr x), observe_one]

/-- Exact compatibility with the old presentation mass observer, guarded by
the same domain capabilities. -/
theorem semanticMass_bridge (b : ContinuousDensityBind)
    (hr : b.RowDefined (fun _ => some 1)) (hi : b.JointL1 (fun _ => some 1)) :
    b.semanticMass = massValue b.presentation := by
  rw [presentation, DensityProgram.bind_mass_bridge, semanticMass_eq b hr hi]
  congr 1
  funext x
  rw [DensityProgram.mass_bridge]

end ContinuousDensityBind
end QSym.Distribution
