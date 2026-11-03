import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! Partial values. `none` means invalid mathematics, never loop divergence.
Multiplication is strict; Iverson masking has its own non-strict operation. -/
namespace QSym
open scoped NNReal ENNReal
namespace Value

def add {α : Type} [Add α] : Option α → Option α → Option α
  | some x, some y => some (x + y)
  | _, _ => none

def mul {α : Type} [Mul α] : Option α → Option α → Option α
  | some x, some y => some (x * y)
  | _, _ => none

noncomputable def inv {α : Type} [Zero α] [Inv α] (x : Option α) : Option α := by
  classical
  exact x.bind (fun v => if v = 0 then none else some v⁻¹)

noncomputable def nonzero {α : Type} [Zero α] (x : Option α) : Option Bool := by
  classical
  exact x.map (fun v => decide (v ≠ 0))

def mask {α : Type} [Zero α] : Option Bool → Option α → Option α
  | some false, _ => some 0
  | some true, x => x
  | none, _ => none

noncomputable def conj (x : Option ℂ) : Option ℂ := x.map star

def Defined {α : Type} (x : Option α) : Prop := ∃ v, x = some v

theorem add_zero_right {α : Type} [AddZeroClass α] (x : Option α) :
    add x (some 0) = x := by cases x <;> simp [add]

theorem add_zero_left {α : Type} [AddZeroClass α] (x : Option α) :
    add (some 0) x = x := by cases x <;> simp [add]

theorem mul_one_right {α : Type} [MulOneClass α] (x : Option α) :
    mul x (some 1) = x := by cases x <;> simp [mul]

theorem mul_one_left {α : Type} [MulOneClass α] (x : Option α) :
    mul (some 1) x = x := by cases x <;> simp [mul]

theorem mask_true {α : Type} [Zero α] (x : Option α) :
    mask (some true) x = x := rfl

theorem mask_false {α : Type} [Zero α] (x : Option α) :
    mask (some false) x = some 0 := rfl

theorem conj_conj (x : Option ℂ) : conj (conj x) = x := by
  cases x <;> simp [conj]

theorem defined_add {α : Type} [Add α] (x y : Option α) :
    Defined (add x y) ↔ Defined x ∧ Defined y := by
  cases x <;> cases y <;> simp [add, Defined]

theorem defined_mul {α : Type} [Mul α] (x y : Option α) :
    Defined (mul x y) ↔ Defined x ∧ Defined y := by
  cases x <;> cases y <;> simp [mul, Defined]

theorem defined_inv {α : Type} [Zero α] [Inv α] (x : Option α) :
    Defined (inv x) ↔ ∃ v, x = some v ∧ v ≠ 0 := by
  classical
  cases x with
  | none => simp [inv, Defined]
  | some v => by_cases h : v = 0 <;> simp [inv, Defined, h]

theorem defined_nonzero {α : Type} [Zero α] (x : Option α) :
    Defined (nonzero x) ↔ Defined x := by
  classical
  cases x with
  | none => simp [nonzero, Defined]
  | some v => by_cases h : v = 0 <;> simp [nonzero, Defined, h]

theorem defined_mask {α : Type} [Zero α] (p : Option Bool) (x : Option α) :
    Defined (mask p x) ↔ p = some false ∨ (p = some true ∧ Defined x) := by
  cases p with
  | none => simp [mask, Defined]
  | some b => cases b <;> simp [mask, Defined]

theorem defined_conj (x : Option ℂ) : Defined (conj x) ↔ Defined x := by
  cases x <;> simp [conj, Defined]

theorem defined_guarded_inv {α : Type} [Zero α] [Inv α] (x : Option α) :
    Defined (mask (nonzero x) (inv x)) ↔ Defined x := by
  classical
  cases x with
  | none => simp [nonzero, mask, Defined]
  | some v => by_cases h : v = 0 <;> simp [nonzero, inv, mask, Defined, h]

-- These are regression theorems, including the deliberately forbidden 0*x rule.
theorem inverse_zero : inv (some (0 : ℝ)) = none := by simp [inv]
theorem strict_zero_undefined : mul (some (0 : ℝ)) none = none := rfl
theorem masked_undefined : mask (some false) (none : Option ℝ) = some 0 := rfl

end Value

/-! A representative retains its point values. The prototype fixes its reference
measure to real Lebesgue measure and its weights to finite nonnegative reals.
The full design generalizes the reference measure and exposes measurability. -/
abbrev Density := ℝ → ℝ≥0

namespace Density
noncomputable def lebesgue : Density := fun _ => 1
noncomputable def puncture (f : Density) : Density := fun x => if x = 0 then 0 else f x
noncomputable def forget (f : Density) : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.withDensity (fun x => (f x : ℝ≥0∞))

theorem measurable_puncture (f : Density) (hf : Measurable f) : Measurable (puncture f) := by
  exact Measurable.ite (measurableSet_singleton 0) measurable_const hf

theorem forget_puncture (f : Density) : forget (puncture f) = forget f := by
  apply MeasureTheory.withDensity_congr_ae
  have h : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [h] with x hx
  simp [puncture, hx]

theorem puncture_differs : puncture lebesgue ≠ lebesgue := by
  intro h
  have h0 := congrFun h 0
  norm_num [puncture, lebesgue] at h0

theorem representative_at_zero : puncture lebesgue 0 = 0 := by simp [puncture]
theorem lebesgue_at_zero : lebesgue 0 = 1 := rfl
end Density

namespace Value
def densityAt (d : Option Density) (x : Option ℝ) : Option ℝ := do
  let f ← d
  let v ← x
  pure (f v : ℝ)

theorem defined_map {α β : Type} (f : α → β) (x : Option α) :
    Defined (x.map f) ↔ Defined x := by
  cases x <;> simp [Defined]

theorem defined_densityAt (d : Option Density) (x : Option ℝ) :
    Defined (densityAt d x) ↔ Defined d ∧ Defined x := by
  cases d <;> cases x <;> simp [densityAt, Defined]
end Value
end QSym
