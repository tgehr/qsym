import QSym.DistributionDensityModel
import QSym.WeightedFibreRooted

/-! Direct interpretation of density programs by partial weighted fibres.

The retained coordinate is the returned real value, and the partial density is
stored in the body. The latent reference is a Dirac point. Density and mass are
therefore observations of the same semantic object; `Presentation` is used only
in compatibility theorems for the existing frontend.
-/
noncomputable section
namespace QSym.Distribution
open MeasureTheory
open scoped ProbabilityTheory
open WeightedParameter.Fibre

/-- A real density as a partial family retaining its sample coordinate. -/
def densityFamily (w : ℝ → Option ℝ) : PartialFamily ℝ PUnit.{1} ℝ where
  space := Space.point
  body := fun x =>
    { weight := fun _ _ => w x
      value := fun _ _ => some x }

namespace DensityProgram

/-- The direct partial-fibre representative of a density program. -/
def semanticFamily (p : DensityProgram) : PartialFamily ℝ PUnit.{1} ℝ :=
  densityFamily p.density

/-- The direct partial-fibre semantics, quotiented by reference isomorphism. -/
def semantic (p : DensityProgram) : PartialHom ℝ PUnit.{1} ℝ :=
  PartialHom.ofFamily p.semanticFamily

/-- The direct partial-fibre semantics with its intrinsic Lebesgue root. -/
def rootedSemantic (p : DensityProgram) : RootedPartialTrace ℝ volume ℝ :=
  RootedPartialHom.ofPartialHom p.semantic

/-- Pointwise density is observation of the fibre at the retained coordinate. -/
def semanticDensityAt (p : DensityProgram) (x : ℝ) : Option ℝ :=
  p.rootedSemantic.observe x (PUnit.unit : PUnit.{1}) (fun _ => some 1)

/-- Mass is joint observation at the intrinsic Lebesgue root. -/
def semanticMass (p : DensityProgram) : Option ℝ := p.rootedSemantic.mass

/-- A source weight is semantic reweighting of the retained returned value. -/
theorem semantic_weight (f : ℝ → Option ℝ) (p : DensityProgram) :
    semantic (.weight f p) =
      PartialHom.reweight (fun _ _ x => f x) p.semantic := rfl

/-- Forgetting the intrinsic root recovers the original direct semantics. -/
theorem eraseRoot_rootedSemantic (p : DensityProgram) :
    p.rootedSemantic.eraseRoot = p.semantic := rfl

/-- Source weighting preserves the Lebesgue root. -/
theorem rootedSemantic_weight (f : ℝ → Option ℝ) (p : DensityProgram) :
    rootedSemantic (.weight f p) =
      RootedPartialHom.reweight (fun _ _ x => f x) p.rootedSemantic := rfl

/-- The rooted observer is the previous explicitly based mass observer. -/
theorem semanticMass_rooted (p : DensityProgram) :
    p.semanticMass = p.rootedSemantic.mass := rfl

@[simp] theorem semanticDensityAt_eq (p : DensityProgram) (x : ℝ) :
    p.semanticDensityAt x = p.density x := by
  change partialIntegral (Measure.dirac (PUnit.unit : PUnit.{1}))
    (fun _ : PUnit.{1} => Value.mul (p.density x) (some 1)) = _
  rw [partialIntegral_point, Value.mul_one_right]

theorem semanticMass_eq (p : DensityProgram) : p.semanticMass = p.mass := by
  rw [DensityProgram.mass, Model.densityMassValue_eq]
  change partialIntegral
      (volume ⊗ₘ ProbabilityTheory.Kernel.const ℝ (Measure.dirac (PUnit.unit : PUnit.{1})))
      (fun z : ℝ × PUnit.{1} => Value.mul (p.density z.1) (some 1)) =
    partialIntegral volume p.density
  simp only [Value.mul_one_right, Measure.compProd_const]
  exact partialIntegral_comp MeasurableEquiv.prodPUnit
    (WeightedParameter.measurePreserving_prodPUnit volume) p.density

/-- Compatibility with the old presentation observer, not the semantic route. -/
theorem semanticDensityAt_bridge (p : DensityProgram) (x : ℝ) :
    p.semanticDensityAt x = densityAtValue p.presentation (some x) := by
  rw [semanticDensityAt_eq, p.observeAt_bridge, p.observeAt_eq]

/-- Compatibility with the old presentation mass observer. -/
theorem semanticMass_bridge (p : DensityProgram) :
    p.semanticMass = massValue p.presentation := by
  rw [semanticMass_eq, p.mass_bridge]

end DensityProgram
end QSym.Distribution
