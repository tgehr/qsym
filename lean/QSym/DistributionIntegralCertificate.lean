import QSym.DependentIntegrationLaws
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Source-checkable finite-exception certificates. These separate pointwise
 totality from almost-everywhere integration facts. They justify scalar
 observations, never replacement of a pointwise density by an AE-equal one.
-/
noncomputable section
namespace QSym.Distribution
open MeasureTheory Set
open scoped ProbabilityTheory

theorem ae_away (points : List ℝ) :
    ∀ᵐ x : ℝ ∂volume, ∀ p ∈ points, x ≠ p := by
  induction points with
  | nil => simp
  | cons p ps ih =>
    filter_upwards [ih, show ∀ᵐ x : ℝ ∂volume, x ≠ p by
      rw [ae_iff]; simp] with x hx hp
    simpa using And.intro hp hx

theorem partialIntegral_congr_away (f g : ℝ → Option ℝ) (points : List ℝ)
    (hf : ∀ x, Value.Defined (f x)) (hg : ∀ x, Value.Defined (g x))
    (he : ∀ x, (∀ p ∈ points, x ≠ p) → f x = g x) :
    partialIntegral volume f = partialIntegral volume g := by
  have he' : (fun x => (f x).getD 0) =ᵐ[volume] (fun x => (g x).getD 0) := by
    filter_upwards [ae_away points] with x hx
    rw [he x hx]
  have hi := integrable_congr he'
  by_cases h : Integrable (fun x => (g x).getD 0) volume
  · rw [partialIntegral_valid volume f hf (hi.mpr h), partialIntegral_valid volume g hg h,
      integral_congr_ae he']
  · rw [partialIntegral_invalid volume g h,
      partialIntegral_invalid volume f (fun h' => h (hi.mp h'))]

theorem partialIntegral_interval (f : ℝ → Option ℝ) (a b c : ℝ) (points : List ℝ)
    (hab : a ≤ b) (hf : ∀ x, Value.Defined (f x))
    (he : ∀ x, (∀ p ∈ points, x ≠ p) →
      f x = some (if a ≤ x ∧ x ≤ b then c else 0)) :
    partialIntegral volume f = some (c * (b - a)) := by
  let g : ℝ → ℝ := (Icc a b).indicator (fun _ => c)
  have hi : Integrable g volume := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const.mpr (Or.inr (by simp [Real.volume_Icc]))
  have he' : (fun x => (f x).getD 0) =ᵐ[volume] g := by
    filter_upwards [ae_away points] with x hx
    simp [he x hx, g, Set.indicator, Set.mem_Icc]
  rw [partialIntegral_valid volume f hf ((integrable_congr he').mpr hi)]
  rw [integral_congr_ae he']
  simp [g, integral_indicator_const, Real.volume_real_Icc_of_le hab, mul_comm]

/-- Facts checked from the source expression and the proposed bounds. -/
structure IntervalCertificate (f : ℝ → Option ℝ) (a b c : ℝ) (points : List ℝ) : Prop where
  ordered : a ≤ b
  total : ∀ x, Value.Defined (f x)
  away : ∀ x, (∀ p ∈ points, x ≠ p) → f x = some (if a ≤ x ∧ x ≤ b then c else 0)

/-- A null-point edit is licensed only for the scalar observer. -/
structure NullEditCertificate (f g : ℝ → Option ℝ) (points : List ℝ) : Prop where
  source_total : ∀ x, Value.Defined (f x)
  target_total : ∀ x, Value.Defined (g x)
  away : ∀ x, (∀ p ∈ points, x ≠ p) → f x = g x

namespace IntervalCertificate
variable {f : ℝ → Option ℝ} {a b c : ℝ} {points : List ℝ}

theorem integrate (h : IntervalCertificate f a b c points) :
    partialIntegral volume f = some (c * (b - a)) :=
  partialIntegral_interval f a b c points h.ordered h.total h.away

theorem integrable (h : IntervalCertificate f a b c points) :
    Integrable (fun x => (f x).getD 0) volume :=
  ((partialIntegral_defined_iff volume f).mp ⟨_, h.integrate⟩).2

theorem integral_value (h : IntervalCertificate f a b c points) :
    (∫ x, (f x).getD 0) = c * (b - a) :=
  Option.some.inj ((partialIntegral_valid volume f h.total h.integrable).symm.trans h.integrate)

def absolute (h : IntervalCertificate f a b c points) :
    IntervalCertificate (fun x => (f x).map (fun r : ℝ => |r|)) a b |c| points where
  ordered := h.ordered
  total := by
    intro x
    obtain ⟨r, hr⟩ := h.total x
    exact ⟨|r|, by simp [hr]⟩
  away := by
    intro x hx
    rw [h.away x hx]
    split_ifs <;> simp

theorem variation (h : IntervalCertificate f a b c points) :
    (∫ x, |(f x).getD 0|) = |c| * (b - a) := by
  have hget (x : ℝ) : ((f x).map (fun r : ℝ => |r|)).getD 0 = |(f x).getD 0| := by
    cases f x <;> simp
  simpa only [hget] using h.absolute.integral_value

/-- Row certificates may have parameter-dependent bounds and coefficients.
No continuity in the retained parameter is required. -/
theorem rows {X : Type} [MeasurableSpace X] {f : X × ℝ → Option ℝ}
    {a b c : X → ℝ} {points : X → List ℝ}
    (h : ∀ x, IntervalCertificate (fun y => f (x, y)) (a x) (b x) (c x) (points x)) :
    IntegrableEveryRow (ProbabilityTheory.Kernel.const X volume) f :=
  fun x => (h x).integrable

/-- The outer capability is absolute mass, so signed cancellation cannot
silently justify flattening a dependent integral. -/
theorem joint_integrable {X : Type} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {f : X × ℝ → Option ℝ} {a b c : X → ℝ} {points : X → List ℝ}
    (h : ∀ x, IntervalCertificate (fun y => f (x, y)) (a x) (b x) (c x) (points x))
    (hm : AEStronglyMeasurable (fun p => (f p).getD 0)
      (μ ⊗ₘ ProbabilityTheory.Kernel.const X volume))
    (hp : Integrable (fun x => |c x| * (b x - a x)) μ) :
    Integrable (fun p => (f p).getD 0) (μ ⊗ₘ ProbabilityTheory.Kernel.const X volume) := by
  apply (integrable_compProd_iff_variation μ _ f (rows h) hm).mpr
  simpa only [ProbabilityTheory.Kernel.const_apply, fun x => (h x).variation] using hp

end IntervalCertificate

end QSym.Distribution
