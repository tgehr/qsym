import QSym.WeightedMarginal
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Chosen pointwise fibre references for a coordinate projection.

Unlike a joint measure, a Mathlib kernel retains its value at every base point.
This is a building block for replacing the old global-measure-only quotient,
not a claim that the replacement quotient or full disintegration is complete.
The reference kernels are unnormalized measures; weights may still be signed.
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory
open scoped ProbabilityTheory

structure Reference (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  base : Measure X
  fibres : ProbabilityTheory.Kernel X Y
  [base_sfinite : SFinite base]
  [fibres_sfinite : ProbabilityTheory.IsSFiniteKernel fibres]

attribute [instance] Reference.base_sfinite Reference.fibres_sfinite

namespace Reference

def joint {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (R : Reference X Y) :
    Measure (X × Y) := R.base ⊗ₘ R.fibres

def product {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] : Reference X Y where
  base := μ
  fibres := ProbabilityTheory.Kernel.const X ν

@[simp] theorem joint_product {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] :
    (product μ ν).joint = μ.prod ν := Measure.compProd_const

def mean {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (R : Reference X Y) (w : X → Y → ℝ) (x : X) : ℝ := ∫ y, w x y ∂(R.fibres x)

def variation {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (R : Reference X Y) (w : X → Y → ℝ) (x : X) : ℝ := ∫ y, |w x y| ∂(R.fibres x)

structure IntegrableRows {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (R : Reference X Y) (w : X → Y → ℝ) : Prop where
  integrable : ∀ x, Integrable (w x) (R.fibres x)

theorem finiteIntegral_row {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {R : Reference X Y} {w : X → Y → ℝ} (h : IntegrableRows R w) (x : X) :
    finiteIntegral (R.fibres x) (w x) = some (R.mean w x) := by
  simp [finiteIntegral, h.integrable x, mean]

theorem integrable_weighted_iff {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {R : Reference X Y} {w : X → Y → ℝ} (hr : IntegrableRows R w) (f : X → ℝ)
    (hm : AEStronglyMeasurable (fun z : X × Y => w z.1 z.2 * f z.1) R.joint) :
    Integrable (fun z : X × Y => w z.1 z.2 * f z.1) R.joint ↔
      Integrable (fun x => R.variation w x * |f x|) R.base := by
  dsimp only [joint] at hm ⊢
  rw [Measure.integrable_compProd_iff hm]
  have hr' : ∀ᵐ x ∂R.base, Integrable (fun y => w x y * f x) (R.fibres x) :=
    Filter.Eventually.of_forall (fun x => (hr.integrable x).mul_const (f x))
  simp only [hr', true_and]
  simp_rw [norm_mul, Real.norm_eq_abs, integral_mul_const, variation]

/-- Sufficient pointwise preservation law for a change of latent coordinates.
The stronger condition is essential: preserving only `R.joint` is insufficient.
No assumption about numerical continuity in the retained coordinate is needed
for these pointwise conclusions. -/
structure FibreIso {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (R : Reference X Y) (S : Reference X Z) where
  base_eq : R.base = S.base
  coord : X → Y ≃ᵐ Z
  preserving : ∀ x, MeasurePreserving (coord x) (R.fibres x) (S.fibres x)

namespace FibreIso

def refl {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (R : Reference X Y) : FibreIso R R where
  base_eq := rfl
  coord := fun _ => MeasurableEquiv.refl Y
  preserving := fun x => MeasurePreserving.id (R.fibres x)

def symm {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {R : Reference X Y} {S : Reference X Z} (h : FibreIso R S) : FibreIso S R where
  base_eq := h.base_eq.symm
  coord := fun x => (h.coord x).symm
  preserving := fun x => MeasurePreserving.symm (h.coord x) (h.preserving x)

def trans {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W]
    {R : Reference X Y} {S : Reference X Z} {T : Reference X W}
    (h : FibreIso R S) (k : FibreIso S T) : FibreIso R T where
  base_eq := h.base_eq.trans k.base_eq
  coord := fun x => (h.coord x).trans (k.coord x)
  preserving := fun x => (k.preserving x).comp (h.preserving x)

end FibreIso

theorem mean_reparam {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {R : Reference X Y} {S : Reference X Z} (h : FibreIso R S) (w : X → Z → ℝ) :
    R.mean (fun x y => w x (h.coord x y)) = S.mean w := by
  funext x
  exact (h.preserving x).integral_comp' (w x)

theorem variation_reparam {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {R : Reference X Y} {S : Reference X Z} (h : FibreIso R S) (w : X → Z → ℝ) :
    R.variation (fun x y => w x (h.coord x y)) = S.variation w :=
  mean_reparam h (fun x y => |w x y|)

theorem rows_reparam_iff {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {R : Reference X Y} {S : Reference X Z} (h : FibreIso R S) (w : X → Z → ℝ) :
    IntegrableRows R (fun x y => w x (h.coord x y)) ↔ IntegrableRows S w := by
  constructor
  · intro hr
    exact ⟨fun x => ((h.preserving x).integrable_comp_emb (h.coord x).measurableEmbedding).mp
      (hr.integrable x)⟩
  · intro hr
    exact ⟨fun x => ((h.preserving x).integrable_comp_emb (h.coord x).measurableEmbedding).mpr
      (hr.integrable x)⟩

end Reference
end QSym.WeightedParameter.Fibre
