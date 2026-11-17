import QSym.DistributionDensityModel
import QSym.WeightedFibreRooted

/-! Direct interpretation of primitive and density programs by partial fibres.

Density programs retain their real sample as the returned value and store the
partial density in the body. Primitive programs use point or empty latent fibres.
Observation and mass therefore share one semantic object; `Presentation` is used
only in compatibility theorems for the existing frontend.
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

/-- The three non-recursive primitive presentation constructors. -/
inductive PrimitiveProgram (α : Type) where
  | invalid
  | zero
  | dirac (value : α)

namespace PrimitiveProgram
variable {α : Type}

/-- Invalidity is retained at a latent point rather than identified with zero. -/
def invalidFamily (α : Type) : PartialFamily PUnit.{1} PUnit.{1} α where
  space := Space.point
  body := fun _ =>
    { weight := fun _ _ => none
      value := fun _ _ => none }

/-- The zero program has an empty latent fibre. A zero weight on a point with an
undefined value would instead be invalid under strict pointwise observation. -/
def zeroFamily (α : Type) : PartialFamily PUnit.{1} PUnit.{1} α where
  space := Space.ofMeasure Empty 0
  body := fun _ =>
    { weight := fun _ ω => nomatch ω
      value := fun _ ω => nomatch ω }

/-- A point mass uses the deterministic partial introduction. -/
def diracFamily (a : α) : PartialFamily PUnit.{1} PUnit.{1} α :=
  PartialFamily.pure (fun _ _ => some a)

/-- The direct primitive representative; its latent space may be empty. -/
def semanticFamily (p : PrimitiveProgram α) : PartialFamily PUnit.{1} PUnit.{1} α :=
  match p with
  | .invalid => invalidFamily α
  | .zero => zeroFamily α
  | .dirac a => diracFamily a

def semantic (p : PrimitiveProgram α) : PartialHom PUnit.{1} PUnit.{1} α :=
  PartialHom.ofFamily p.semanticFamily

/-- Primitive programs have an intrinsic Dirac root at the unit point. -/
def rootedSemantic (p : PrimitiveProgram α) :
    RootedPartialTrace PUnit.{1} (Measure.dirac (PUnit.unit : PUnit.{1})) α :=
  RootedPartialHom.ofFamily p.semanticFamily

/-- Joint observation at the intrinsic root for an arbitrary strict test. -/
def observe (p : PrimitiveProgram α) (f : α → Option ℝ) : Option ℝ :=
  p.rootedSemantic.observeJoint PUnit.unit (fun _ a => f a)

def semanticMass (p : PrimitiveProgram α) : Option ℝ := p.rootedSemantic.mass

/-- The old primitive presentation is used only at the compatibility boundary. -/
def presentation (p : PrimitiveProgram α) : Option (D α) :=
  some <| match p with
    | .invalid => .invalid
    | .zero => .zero
    | .dirac a => .dirac a

@[simp] theorem eraseRoot_rootedSemantic (p : PrimitiveProgram α) :
    p.rootedSemantic.eraseRoot = p.semantic := rfl

@[simp] theorem observe_invalid (f : α → Option ℝ) :
    observe (invalid : PrimitiveProgram α) f = none := by
  unfold observe rootedSemantic RootedPartialHom.observeJoint PartialHom.observeJoint
    RootedPartialHom.ofFamily RootedPartialHom.ofPartialHom PartialHom.ofFamily
  rw [Quotient.liftOn_mk]
  unfold semanticFamily invalidFamily PartialFamily.observeJoint
  apply if_neg
  intro h
  have hd := h.1 (PUnit.unit, PUnit.unit)
  simp [Value.Defined, Value.mul] at hd

@[simp] theorem observe_zero (f : α → Option ℝ) :
    observe (zero : PrimitiveProgram α) f = some 0 := by
  unfold observe rootedSemantic RootedPartialHom.observeJoint PartialHom.observeJoint
    RootedPartialHom.ofFamily RootedPartialHom.ofPartialHom PartialHom.ofFamily
  rw [Quotient.liftOn_mk]
  unfold PartialFamily.observeJoint
  change partialIntegral ((Measure.dirac (PUnit.unit : PUnit.{1})) ⊗ₘ
    ProbabilityTheory.Kernel.const PUnit.{1} (0 : Measure Empty)) _ = some 0
  rw [partialIntegral_valid _ _ (fun z => isEmptyElim z.2) Integrable.of_isEmpty,
    integral_of_isEmpty]

@[simp] theorem observe_dirac (a : α) (f : α → Option ℝ) :
    observe (dirac a) f = f a := by
  unfold observe rootedSemantic RootedPartialHom.observeJoint PartialHom.observeJoint
    RootedPartialHom.ofFamily RootedPartialHom.ofPartialHom PartialHom.ofFamily
  rw [Quotient.liftOn_mk]
  unfold semanticFamily diracFamily PartialFamily.observeJoint PartialFamily.pure
    PartialKernel.pure Space.point
  simp only [ProbabilityTheory.Kernel.const_apply, Measure.compProd_const,
    Option.some_bind, Value.mul_one_left]
  exact (partialIntegral_comp MeasurableEquiv.punitProd
    (WeightedParameter.measurePreserving_punitProd
      (Measure.dirac (PUnit.unit : PUnit.{1}))) (fun _ => f a)).trans
    (partialIntegral_point (f a))

/-- Primitive observation computes exactly by constructor. -/
theorem observe_eq (p : PrimitiveProgram α) (f : α → Option ℝ) :
    p.observe f = match p with
      | .invalid => none
      | .zero => some 0
      | .dirac a => f a := by
  cases p with
  | invalid => exact observe_invalid f
  | zero => exact observe_zero f
  | dirac a => exact observe_dirac a f

/-- Exact compatibility with the old primitive presentation observer. -/
theorem observe_bridge (p : PrimitiveProgram α) (f : α → Option ℝ) :
    p.observe f = p.presentation.bind (fun d => integrate d f) := by
  cases p with
  | invalid => exact observe_invalid f
  | zero => exact observe_zero f
  | dirac a => exact observe_dirac a f

/-- Intrinsic rooted mass is the unit-test special case of observation. -/
theorem semanticMass_eq (p : PrimitiveProgram α) :
    p.semanticMass = p.observe (fun _ => some 1) := rfl

/-- Exact compatibility with the old primitive presentation mass observer. -/
theorem semanticMass_bridge (p : PrimitiveProgram α) :
    p.semanticMass = massValue p.presentation := by
  change p.observe (fun _ => some 1) =
    p.presentation.bind (fun d => integrate d (fun _ => some 1))
  exact observe_bridge p _

end PrimitiveProgram

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

/-! Compatibility boundary for constant scaling of any rooted direct trace.
The source bridge and its definedness are explicit capabilities; neither the
semantic operation nor its direct observer is routed through `Presentation`. -/
namespace RootedScale
variable {X α : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem observeJoint_bridge (p : RootedPartialTrace X μ α) (r : ℝ)
    (d : Option (D α)) (f : α → Option ℝ)
    (hs : p.observeJoint PUnit.unit (fun _ a => f a) =
      d.bind (fun a => integrate a f))
    (hd : Value.Defined (p.observeJoint PUnit.unit (fun _ a => f a))) :
    (RootedPartialHom.scale r p).observeJoint PUnit.unit (fun _ a => f a) =
      (scaleValue (some r) d).bind (fun a => integrate a f) := by
  rw [RootedPartialHom.observeJoint_scale_defined p r PUnit.unit _ hd, hs]
  cases d <;> rfl

theorem mass_bridge (p : RootedPartialTrace X μ α) (r : ℝ) (d : Option (D α))
    (hs : p.mass = massValue d) (hd : Value.Defined p.mass) :
    (RootedPartialHom.scale r p).mass = massValue (scaleValue (some r) d) := by
  rw [RootedPartialHom.mass_scale_defined p r hd, hs, mass_scaleValue]

end RootedScale
end QSym.Distribution
