import QSym.WeightedParameterSpace

/-! Certified coordinate marginalization on *chosen product presentations*.

These operations deliberately do not define a density observer on `Hom`:
global measure preservation alone does not preserve individual fibre integrals.
See `WeightedFibreObstruction` for a counterexample in the current quotient.
Signed marginalization retains an absolute-weight profile to track domains.
-/
noncomputable section
namespace QSym.WeightedParameter
open MeasureTheory

namespace Fibre

def mean {X Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (w : X → Y → ℝ) (x : X) : ℝ :=
  ∫ y, w x y ∂ν

def variation {X Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (w : X → Y → ℝ) (x : X) : ℝ :=
  ∫ y, |w x y| ∂ν

/-- Pointwise fibre integrability, including exceptional values of the retained
coordinate. An almost-everywhere statement does not certify pointwise density. -/
structure IntegrableRows {X Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (w : X → Y → ℝ) : Prop where
  integrable : ∀ x, Integrable (w x) ν

/-- A single density query only needs integrability of that particular fibre.
The stronger `IntegrableRows` capability is for forming a total marginal. -/
theorem finiteIntegral_row_of_integrable {X Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {w : X → Y → ℝ} {x : X} (h : Integrable (w x) ν) :
    finiteIntegral ν (w x) = some (mean ν w x) := by
  simp [finiteIntegral, h, mean]

theorem finiteIntegral_row {X Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {w : X → Y → ℝ} (h : IntegrableRows ν w) (x : X) :
    finiteIntegral ν (w x) = some (mean ν w x) := by
  exact finiteIntegral_row_of_integrable (h.integrable x)

theorem rows_reweight {X Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {w : X → Y → ℝ} (h : IntegrableRows ν w) (f : X → ℝ) :
    IntegrableRows ν (fun x y => w x y * f x) :=
  ⟨fun x => (h.integrable x).mul_const (f x)⟩

theorem rows_add {X Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {w v : X → Y → ℝ} (hw : IntegrableRows ν w) (hv : IntegrableRows ν v) :
    IntegrableRows ν (fun x y => w x y + v x y) :=
  ⟨fun x => (hw.integrable x).add (hv.integrable x)⟩

theorem mean_add {X Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {w v : X → Y → ℝ} (hw : IntegrableRows ν w) (hv : IntegrableRows ν v) :
    mean ν (fun x y => w x y + v x y) = fun x => mean ν w x + mean ν v x := by
  funext x
  exact integral_add (hw.integrable x) (hv.integrable x)

theorem mean_reweight {X Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (w : X → Y → ℝ) (f : X → ℝ) :
    mean ν (fun x y => w x y * f x) = fun x => mean ν w x * f x := by
  funext x
  exact integral_mul_const (f x) (w x)

theorem variation_reweight {X Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (w : X → Y → ℝ) (f : X → ℝ) :
    variation ν (fun x y => w x y * f x) = fun x => variation ν w x * |f x| := by
  funext x
  simp only [variation, abs_mul, integral_mul_const]

theorem rows_separable {X Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} (f : X → ℝ) {g : Y → ℝ} (hg : Integrable g ν) :
    IntegrableRows ν (fun x y => f x * g y) :=
  ⟨fun x => hg.const_mul (f x)⟩

theorem mean_separable {X Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (f : X → ℝ) (g : Y → ℝ) :
    mean ν (fun x y => f x * g y) = fun x => f x * ∫ y, g y ∂ν := by
  funext x
  exact integral_const_mul (f x) g

theorem mean_congr {X Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {w v : X → Y → ℝ} (h : ∀ x, w x =ᵐ[ν] v x) :
    mean ν w = mean ν v := by
  funext x
  exact integral_congr_ae (h x)

/-- Reparameterization must preserve the latent reference measure on *every*
fibre. It may depend on the retained coordinate; joint measurability is not
needed for this pointwise statement. -/
theorem mean_reparam {X Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {ν : Measure Y} {τ : Measure Z} (w : X → Z → ℝ)
    (e : X → Y ≃ᵐ Z) (he : ∀ x, MeasurePreserving (e x) ν τ) :
    mean ν (fun x y => w x (e x y)) = mean τ w := by
  funext x
  exact (he x).integral_comp' (w x)

theorem variation_reparam {X Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {ν : Measure Y} {τ : Measure Z} (w : X → Z → ℝ)
    (e : X → Y ≃ᵐ Z) (he : ∀ x, MeasurePreserving (e x) ν τ) :
    variation ν (fun x y => w x (e x y)) = variation τ w :=
  mean_reparam (fun x y => |w x y|) e he

theorem rows_reparam_iff {X Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {ν : Measure Y} {τ : Measure Z} (w : X → Z → ℝ)
    (e : X → Y ≃ᵐ Z) (he : ∀ x, MeasurePreserving (e x) ν τ) :
    IntegrableRows ν (fun x y => w x (e x y)) ↔ IntegrableRows τ w := by
  constructor
  · intro h
    exact ⟨fun x => ((he x).integrable_comp_emb (e x).measurableEmbedding).mp (h.integrable x)⟩
  · intro h
    exact ⟨fun x => ((he x).integrable_comp_emb (e x).measurableEmbedding).mpr (h.integrable x)⟩

theorem variation_nonneg {X Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (w : X → Y → ℝ) (x : X) : 0 ≤ variation ν w x :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem abs_mean_le_variation {X Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (w : X → Y → ℝ) (x : X) : |mean ν w x| ≤ variation ν w x := by
  simpa [mean, variation, Real.norm_eq_abs] using norm_integral_le_integral_norm (w x)

theorem variation_eq_mean_of_nonneg {X Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {w : X → Y → ℝ} (hw : ∀ x y, 0 ≤ w x y) :
    variation ν w = mean ν w := by
  funext x
  simp [variation, mean, abs_of_nonneg (hw x _)]

/-- Exact joint-integrability criterion for a retained-coordinate test. The
absolute-weight profile, rather than the absolute value of the marginal mean,
is essential for signed weights. -/
theorem integrable_weighted_iff {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν] {w : X → Y → ℝ}
    (hr : IntegrableRows ν w) (f : X → ℝ)
    (hm : AEStronglyMeasurable (fun z : X × Y => w z.1 z.2 * f z.1) (μ.prod ν)) :
    Integrable (fun z : X × Y => w z.1 z.2 * f z.1) (μ.prod ν) ↔
      Integrable (fun x => variation ν w x * |f x|) μ := by
  rw [integrable_prod_iff hm]
  have hr' : ∀ᵐ x ∂μ, Integrable (fun y => w x y * f x) ν :=
    Filter.Eventually.of_forall (fun x => (hr.integrable x).mul_const (f x))
  simp only [hr', true_and]
  simp_rw [norm_mul, Real.norm_eq_abs, integral_mul_const, variation]

theorem mean_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] {w : X → Y → ℝ}
    (hw : StronglyMeasurable (Function.uncurry w)) : StronglyMeasurable (mean ν w) :=
  hw.integral_prod_right'

/-- A scalar reduction with an explicit joint integrability certificate. This
does not claim that dropping latent cancellation preserves definedness without
that certificate. -/
theorem finiteIntegral_project {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] (w : X → Y → ℝ) (f : X → ℝ)
    (hi : Integrable (fun z : X × Y => w z.1 z.2 * f z.1) (μ.prod ν)) :
    finiteIntegral (μ.prod ν) (fun z : X × Y => w z.1 z.2 * f z.1) =
      finiteIntegral μ (fun x => mean ν w x * f x) := by
  have houter : Integrable (fun x => mean ν w x * f x) μ := by
    simpa only [mean, integral_mul_const] using hi.integral_prod_left
  simp only [finiteIntegral, if_pos hi, if_pos houter]
  congr 1
  rw [integral_prod _ hi]
  simp only [mean, integral_mul_const]

/-- Evaluate a certified marginal while retaining the source's absolute-weight
profile. This preserves the joint observer's domain even when signed weights
cancel on a fibre. Joint measurability and pointwise row existence are explicit
capabilities, not run-time failures replaced with zero. -/
def observe {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (w : X → Y → ℝ)
    (_rows : IntegrableRows ν w) (f : X → ℝ)
    (_measurable : AEStronglyMeasurable (fun z : X × Y => w z.1 z.2 * f z.1) (μ.prod ν)) :
    Option ℝ := by
  classical
  exact if Integrable (fun x => variation ν w x * |f x|) μ
    then some (∫ x, mean ν w x * f x ∂μ) else none

theorem observe_eq_joint {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (w : X → Y → ℝ)
    (rows : IntegrableRows ν w) (f : X → ℝ)
    (hm : AEStronglyMeasurable (fun z : X × Y => w z.1 z.2 * f z.1) (μ.prod ν)) :
    observe μ ν w rows f hm =
      finiteIntegral (μ.prod ν) (fun z : X × Y => w z.1 z.2 * f z.1) := by
  classical
  have hiff := integrable_weighted_iff rows f hm
  by_cases hi : Integrable (fun z : X × Y => w z.1 z.2 * f z.1) (μ.prod ν)
  · have houter : Integrable (fun x => mean ν w x * f x) μ := by
      simpa only [mean, integral_mul_const] using hi.integral_prod_left
    rw [observe, if_pos (hiff.mp hi)]
    rw [finiteIntegral_project w f hi]
    simp [finiteIntegral, houter]
  · have hv : ¬ Integrable (fun x => variation ν w x * |f x|) μ :=
      fun h => hi (hiff.mpr h)
    simp [observe, finiteIntegral, hi, hv]

end Fibre

namespace Kernel

/-- A chosen product presentation whose return value ignores the latent
coordinate. No equality in `Hom` is claimed by this constructor. -/
def projected {A B X Y : Type*} (w : A → X → Y → ℝ) (v : A → X → B) : Kernel (X × Y) A B :=
  ⟨fun a z => w a z.1 z.2, fun a z => v a z.1⟩

/-- Collapse a certified product presentation. The row certificate prevents
Mathlib's nonintegrable-zero convention from becoming a pointwise density. -/
def marginal {A B X Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (w : A → X → Y → ℝ) (v : A → X → B)
    (_rows : ∀ a, Fibre.IntegrableRows ν (w a)) : Kernel X A B :=
  ⟨fun a x => Fibre.mean ν (w a) x, v⟩

theorem marginal_weight {A B X Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (w : A → X → Y → ℝ) (v : A → X → B) (rows : ∀ a, Fibre.IntegrableRows ν (w a))
    (a : A) (x : X) :
    finiteIntegral ν (w a x) = some ((marginal ν w v rows).weight a x) :=
  Fibre.finiteIntegral_row (rows a) x

theorem integrate_marginal {A B X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (w : A → X → Y → ℝ) (v : A → X → B) (rows : ∀ a, Fibre.IntegrableRows ν (w a))
    (a : A) (f : B → ℝ)
    (hi : Integrable (fun z : X × Y => w a z.1 z.2 * f (v a z.1)) (μ.prod ν)) :
    integrate (μ.prod ν) (projected w v) a f = integrate μ (marginal ν w v rows) a f :=
  Fibre.finiteIntegral_project (w a) (fun x => f (v a x)) hi

end Kernel
end QSym.WeightedParameter
