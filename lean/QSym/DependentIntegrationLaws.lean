import QSym.IntegrationLaws
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Strict finite integration along a chosen dependent reference.

Joint L1 does not imply L1 on every row. Iterated strict integration observes
every row, even rows of zero outer measure. Conversely, integrable signed row
means need not imply joint L1. The two domain obligations are separate.
-/
noncomputable section
namespace QSym
open MeasureTheory
open scoped ProbabilityTheory
variable {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
  (μ : Measure Y) (κ : ProbabilityTheory.Kernel Y Z)

/-- A source-checkable capability can prove this predicate compositionally.
It concerns integrability, not continuity, and does not assert totality. -/
def IntegrableEveryRow (f : Y × Z → Option ℝ) : Prop :=
  ∀ y, Integrable (fun z => (f (y, z)).getD 0) (κ y)

/-- Scaling is a compositional way to construct a row capability. Undefined
values remain undefined; `getD` is used only in the integrability predicate. -/
theorem IntegrableEveryRow.scale {f : Y × Z → Option ℝ}
    (hr : IntegrableEveryRow κ f) (c : ℝ) :
    IntegrableEveryRow κ (fun p => Value.mul (some c) (f p)) := by
  intro y
  have hget (z : Z) : (Value.mul (some c) (f (y, z))).getD 0 = c * (f (y, z)).getD 0 := by
    cases f (y, z) <;> simp [Value.mul]
  simpa only [hget] using (hr y).const_mul c

/-- Zero scaling supplies the L1 capability even when the unscaled rows
diverge. It supplies no pointwise-definedness capability. -/
theorem IntegrableEveryRow.zero_scale (f : Y × Z → Option ℝ) :
    IntegrableEveryRow κ (fun p => Value.mul (some 0) (f p)) := by
  intro y
  have hget (z : Z) : (Value.mul (some (0 : ℝ)) (f (y, z))).getD 0 = 0 := by
    cases f (y, z) <;> simp [Value.mul]
  simp only [hget, integrable_zero]

variable [SFinite μ] [ProbabilityTheory.IsSFiniteKernel κ]

theorem partialIntegral_compProd_of_integrable (f : Y × Z → Option ℝ)
    (hr : IntegrableEveryRow κ f)
    (hi : Integrable (fun p => (f p).getD 0) (μ ⊗ₘ κ)) :
    partialIntegral (μ ⊗ₘ κ) f =
      partialIntegral μ (fun y => partialIntegral (κ y) (fun z => f (y, z))) := by
  classical
  by_cases hd : ∀ p, Value.Defined (f p)
  · have rows (y : Y) : partialIntegral (κ y) (fun z => f (y, z)) =
        some (∫ z, (f (y, z)).getD 0 ∂κ y) :=
      partialIntegral_valid _ _ (fun z => hd (y, z)) (hr y)
    have hm : Integrable (fun y => ∫ z, (f (y, z)).getD 0 ∂κ y) μ := by
      simpa only [Measure.compProd, ProbabilityTheory.Kernel.prodMkLeft_apply,
        ProbabilityTheory.Kernel.const_apply] using hi.integral_compProd
    rw [partialIntegral_valid _ _ hd hi]
    simp_rw [rows]
    rw [partialIntegral_valid _ _ (fun _ => ⟨_, rfl⟩) hm]
    congr 1
    exact Measure.integral_compProd hi
  · have hn : ¬ Value.Defined
        (partialIntegral μ (fun y => partialIntegral (κ y) (fun z => f (y, z)))) := by
      intro h
      have hrows := ((partialIntegral_defined_iff _ _).mp h).1
      apply hd
      intro p
      exact ((partialIntegral_defined_iff _ _).mp (hrows p.1)).1 p.2
    have hn' : partialIntegral μ (fun y => partialIntegral (κ y) (fun z => f (y, z))) = none := by
      cases h : partialIntegral μ (fun y => partialIntegral (κ y) (fun z => f (y, z))) with
      | none => rfl
      | some r => exact (hn ⟨r, h⟩).elim
    rw [hn']
    exact if_neg (fun h => hd h.1)

/-- Forward Fubini refinement needs only the every-row obligation. Joint L1
and totality follow when the source observation actually produces a value. -/
theorem partialIntegral_compProd_refines (f : Y × Z → Option ℝ)
    (hr : IntegrableEveryRow κ f) :
    Value.Refines (partialIntegral (μ ⊗ₘ κ) f)
      (partialIntegral μ (fun y => partialIntegral (κ y) (fun z => f (y, z)))) := by
  intro r h
  have hi := ((partialIntegral_defined_iff _ _).mp ⟨r, h⟩).2
  rw [← partialIntegral_compProd_of_integrable μ κ f hr hi]
  exact h

/-- An exact absolute-profile test for joint L1, given measurable totalization
and integrable rows. Signed cancellation in the row means is insufficient. -/
theorem integrable_compProd_iff_variation (f : Y × Z → Option ℝ)
    (hr : IntegrableEveryRow κ f)
    (hm : AEStronglyMeasurable (fun p => (f p).getD 0) (μ ⊗ₘ κ)) :
    Integrable (fun p => (f p).getD 0) (μ ⊗ₘ κ) ↔
      Integrable (fun y => ∫ z, |(f (y, z)).getD 0| ∂κ y) μ := by
  rw [Measure.integrable_compProd_iff hm]
  simp only [Real.norm_eq_abs, Filter.Eventually.of_forall hr, true_and]

/-- Backend-independent dependent-integration contract. Capabilities are
predicates supplied and verified by the model, not global axioms. -/
structure DependentIntegralTheory (Y Z : Type) where
  outer : (Y → Option ℝ) → Option ℝ
  row : Y → (Z → Option ℝ) → Option ℝ
  joint : (Y × Z → Option ℝ) → Option ℝ
  Rows : (Y × Z → Option ℝ) → Prop
  JointL1 : (Y × Z → Option ℝ) → Prop
  fubini : ∀ f, Rows f → JointL1 f → joint f = outer (fun y => row y (fun z => f (y, z)))
  fubini_refines : ∀ f, Rows f →
    Value.Refines (joint f) (outer (fun y => row y (fun z => f (y, z))))

def dependentIntegralTheory : DependentIntegralTheory Y Z where
  outer := partialIntegral μ
  row := fun y => partialIntegral (κ y)
  joint := partialIntegral (μ ⊗ₘ κ)
  Rows := IntegrableEveryRow κ
  JointL1 := fun f => Integrable (fun p => (f p).getD 0) (μ ⊗ₘ κ)
  fubini := partialIntegral_compProd_of_integrable μ κ
  fubini_refines := partialIntegral_compProd_refines μ κ

end QSym
