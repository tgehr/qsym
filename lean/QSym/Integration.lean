import QSym.Value
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace QSym
open MeasureTheory

/-! Strict finite Bochner integration, including ℂ. A positive extended integral
is a different operation. Mathlib totalizes nonintegrable integrals to zero;
this wrapper deliberately does not expose that as a valid result. The prototype
uses pointwise-defined integrands, even on null sets. -/
noncomputable def partialIntegral {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (f : α → Option E) : Option E := by
  classical
  exact if (∀ x, Value.Defined (f x)) ∧ Integrable (fun x => (f x).getD 0) μ
    then some (∫ x, (f x).getD 0 ∂μ) else none

theorem partialIntegral_valid {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (f : α → Option E)
    (hd : ∀ x, Value.Defined (f x))
    (hi : Integrable (fun x => (f x).getD 0) μ) :
    partialIntegral μ f = some (∫ x, (f x).getD 0 ∂μ) := by
  simp [partialIntegral, hd, hi]

theorem partialIntegral_invalid {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (f : α → Option E)
    (hi : ¬ Integrable (fun x => (f x).getD 0) μ) :
    partialIntegral μ f = none := by
  simp [partialIntegral, hi]

theorem partialIntegral_defined_iff {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) (f : α → Option E) :
    Value.Defined (partialIntegral μ f) ↔
      (∀ x, Value.Defined (f x)) ∧ Integrable (fun x => (f x).getD 0) μ := by
  classical
  simp only [partialIntegral]
  split <;> simp_all [Value.Defined]
end QSym
