import QSym.WeightedFibreReference
import Mathlib.Probability.Kernel.Composition.Prod

/-! Transport of chosen fibre references, including exceptional base points.

A coordinate change acts on the reference kernel as well as on the weight.
Joint measurability is explicit; no continuity in the retained coordinate is
required. Pointwise reference preservation implies joint measure preservation,
but the converse is false (`WeightedFibreObstruction`).
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory
open scoped ProbabilityTheory

/-- A jointly measurable family of measurable bijections of latent coordinates. -/
structure Coordinates (X Y Z : Type*) [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] where
  coord : X → Y ≃ᵐ Z
  forward : Measurable (fun p : X × Y => coord p.1 p.2)
  backward : Measurable (fun p : X × Z => (coord p.1).symm p.2)

namespace Coordinates
variable {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace W]

def joint (e : Coordinates X Y Z) : (X × Y) ≃ᵐ (X × Z) where
  toEquiv :=
    { toFun := fun p => (p.1, e.coord p.1 p.2)
      invFun := fun p => (p.1, (e.coord p.1).symm p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  measurable_toFun := measurable_fst.prodMk e.forward
  measurable_invFun := measurable_fst.prodMk e.backward

def const (e : Y ≃ᵐ Z) : Coordinates X Y Z where
  coord := fun _ => e
  forward := e.measurable.comp measurable_snd
  backward := e.symm.measurable.comp measurable_snd

def refl : Coordinates X Y Y := const (MeasurableEquiv.refl Y)

def symm (e : Coordinates X Y Z) : Coordinates X Z Y where
  coord := fun x => (e.coord x).symm
  forward := e.backward
  backward := e.forward

def trans (e : Coordinates X Y Z) (f : Coordinates X Z W) : Coordinates X Y W where
  coord := fun x => (e.coord x).trans (f.coord x)
  forward := f.forward.comp e.joint.measurable
  backward := e.backward.comp f.joint.symm.measurable

def prod {Y' Z' : Type*} [MeasurableSpace Y'] [MeasurableSpace Z']
    (e : Coordinates X Y Z) (f : Coordinates X Y' Z') :
    Coordinates X (Y × Y') (Z × Z') where
  coord := fun x => (e.coord x).prodCongr (f.coord x)
  forward := (e.forward.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
    (f.forward.comp (measurable_fst.prodMk measurable_snd.snd))
  backward := (e.backward.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
    (f.backward.comp (measurable_fst.prodMk measurable_snd.snd))

/-- Push each reference forward, at every retained coordinate. The explicit
measurability certificate prevents Mathlib's nonmeasurable-map fallback. -/
def transport (e : Coordinates X Y Z) (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] :
    ProbabilityTheory.Kernel X Z :=
  (ProbabilityTheory.Kernel.id ×ₖ κ).map (fun p => e.coord p.1 p.2)

instance transport_sfinite (e : Coordinates X Y Z) (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] :
    ProbabilityTheory.IsSFiniteKernel (e.transport κ) := by
  unfold transport
  infer_instance

theorem transport_apply (e : Coordinates X Y Z) (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] (x : X) :
    e.transport κ x = (κ x).map (e.coord x) := by
  ext s hs
  rw [transport, ProbabilityTheory.Kernel.map_apply' _ e.forward _ hs,
    ProbabilityTheory.Kernel.id_prod_apply' _ _ (e.forward hs),
    Measure.map_apply (e.coord x).measurable hs]
  rfl

theorem preserving_transport (e : Coordinates X Y Z) (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] (x : X) :
    MeasurePreserving (e.coord x) (κ x) (e.transport κ x) :=
  ⟨(e.coord x).measurable, (e.transport_apply κ x).symm⟩

/-- A genuine fibre isomorphism preserves the joint reference for every outer
base measure. Equality merely almost everywhere in `x` would not suffice for
the pointwise observations, even though it suffices for this theorem alone. -/
theorem preserving_joint (e : Coordinates X Y Z)
    {κ : ProbabilityTheory.Kernel X Y} {η : ProbabilityTheory.Kernel X Z}
    [ProbabilityTheory.IsSFiniteKernel κ] [ProbabilityTheory.IsSFiniteKernel η]
    (h : ∀ x, MeasurePreserving (e.coord x) (κ x) (η x))
    (μ : Measure X) [SFinite μ] :
    MeasurePreserving e.joint (μ ⊗ₘ κ) (μ ⊗ₘ η) where
  measurable := e.joint.measurable
  map_eq := by
    ext s hs
    rw [Measure.map_apply e.joint.measurable hs,
      Measure.compProd_apply (e.joint.measurable hs), Measure.compProd_apply hs]
    apply lintegral_congr
    intro x
    have hx := congrArg (fun m : Measure Z => m (Prod.mk x ⁻¹' s)) (h x).map_eq
    dsimp only at hx
    rw [Measure.map_apply (e.coord x).measurable (measurable_prodMk_left hs)] at hx
    exact hx

end Coordinates
end QSym.WeightedParameter.Fibre
