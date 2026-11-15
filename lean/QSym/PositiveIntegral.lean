import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.OmegaCompletePartialOrder

namespace QSym.PositiveIntegral
open MeasureTheory OmegaCompletePartialOrder
open scoped ENNReal

/-- An undefined contribution is zero. This observer is deliberately separate
from strict finite integration and from the pointwise density representation. -/
noncomputable def zeroExtend (p : Part ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ h : p.Dom, p.get h

@[simp] theorem zeroExtend_none : zeroExtend Part.none = 0 := by simp [zeroExtend]
@[simp] theorem zeroExtend_some (r : ℝ≥0∞) : zeroExtend (Part.some r) = r := by
  simp [zeroExtend]

theorem zeroExtend_mono : Monotone zeroExtend := by
  intro p q hpq
  induction p using Part.induction_on with
  | hnone => simp
  | hsome r =>
    have hr : r ∈ q := hpq r (Part.mem_some r)
    rw [← Part.eq_some_iff] at hr
    simp [hr]

theorem zeroExtend_sup (c : Chain (Part ℝ≥0∞)) :
    zeroExtend (ωSup c) = ⨆ n, zeroExtend (c n) := by
  apply le_antisymm
  · induction h : ωSup c using Part.induction_on with
    | hnone => simp
    | hsome r =>
      have hr : r ∈ ωSup c := by rw [h]; exact Part.mem_some r
      obtain ⟨n, hn⟩ := (Part.mem_ωSup r c).mp hr
      simp only [zeroExtend_some]
      calc
        r = zeroExtend (c n) := by rw [← hn]; simp
        _ ≤ ⨆ n, zeroExtend (c n) := le_iSup (fun i => zeroExtend (c i)) n
  · exact iSup_le (fun n => zeroExtend_mono (le_ωSup c n))

/-- Zero extension is continuous from partial information to ordered mass. -/
noncomputable def zeroExtendHom : Part ℝ≥0∞ →𝒄 ℝ≥0∞ where
  toFun := zeroExtend
  monotone' := zeroExtend_mono
  map_ωSup' := zeroExtend_sup

/-- A proof-bearing continuity capability. Measurability is required only
almost everywhere, independently at each approximation parameter. -/
noncomputable def integralHom {P α : Type*} [OmegaCompletePartialOrder P]
    [MeasurableSpace α] (μ : Measure α) (f : α → P →𝒄 ℝ≥0∞)
    (hf : ∀ p, AEMeasurable (fun x => f x p) μ) : P →𝒄 ℝ≥0∞ where
  toFun p := ∫⁻ x, f x p ∂μ
  monotone' := fun p q hpq => lintegral_mono (fun x => (f x).monotone hpq)
  map_ωSup' c := by
    change (∫⁻ x, f x (ωSup c) ∂μ) = ⨆ n, ∫⁻ x, f x (c n) ∂μ
    have he : (fun x => f x (ωSup c)) = (fun x => ⨆ n, f x (c n)) := by
      funext x
      exact (f x).map_ωSup' c
    rw [he]
    exact lintegral_iSup' (fun n => hf (c n))
      (Filter.Eventually.of_forall (fun x i j hij => (f x).monotone (c.monotone hij)))

/-- A continuous partial integrand can contribute zero until it is defined.
Invalid arithmetic must be represented separately if it should propagate errors. -/
noncomputable def partialIntegralHom {P α : Type*} [OmegaCompletePartialOrder P]
    [MeasurableSpace α] (μ : Measure α) (f : α → P →𝒄 Part ℝ≥0∞)
    (hf : ∀ p, AEMeasurable (fun x => zeroExtend (f x p)) μ) : P →𝒄 ℝ≥0∞ :=
  integralHom μ (fun x => zeroExtendHom.comp (f x)) hf

end QSym.PositiveIntegral
