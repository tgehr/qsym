import QSym.DistributionPartialModel
import QSym.DistributionSequentialModel
import QSym.WeightedFibrePartialDependent

/-! Direct partial-fibre semantics for density binds with weighted Dirac
continuations.

A continuation may fail and returns both a real weight and an arbitrary output
value. Its source and continuation fibres remain available in `tower`; only
`semantic` and `rootedSemantic` flatten them. Compatibility with the old
presentation interpreter is a proved observer equation, not the semantic route.
Continuous continuations still require their own references and integration
capabilities.
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
end QSym.Distribution
