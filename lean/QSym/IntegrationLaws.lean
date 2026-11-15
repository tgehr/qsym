import QSym.Integration
import QSym.RefinementBase

/-! Domain-aware laws for strict finite integration. These are proved facts,
not axioms about Mathlib's totalized integral. In particular, pulling out a
zero factor or splitting a signed sum is not an unconditional forward rule.
-/
noncomputable section
namespace QSym
open MeasureTheory

theorem partialIntegral_comp {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y)
    (he : MeasurePreserving e μ ν) (f : Y → Option ℝ) :
    partialIntegral μ (fun x => f (e x)) = partialIntegral ν f := by
  classical
  have hd : (∀ x, Value.Defined (f (e x))) ↔ ∀ y, Value.Defined (f y) :=
    (e.surjective.forall (p := fun y => Value.Defined (f y))).symm
  have hi := he.integrable_comp_emb e.measurableEmbedding (g := fun y => (f y).getD 0)
  simp only [Function.comp_def] at hi
  simp only [partialIntegral]
  rw [hd, hi, he.integral_comp' (fun y => (f y).getD 0)]

theorem partialIntegral_zero {X : Type} [MeasurableSpace X] (μ : Measure X) :
    partialIntegral μ (fun _ => some (0 : ℝ)) = some 0 := by
  simp [partialIntegral, Value.Defined]

theorem partialIntegral_point (v : Option ℝ) :
    partialIntegral (Measure.dirac PUnit.unit) (fun _ : PUnit => v) = v := by
  cases v <;> simp [partialIntegral, Value.Defined]

private theorem mul_getD (c : ℝ) (v : Option ℝ) :
    (Value.mul (some c) v).getD 0 = c * v.getD 0 := by
  cases v <;> simp [Value.mul]

private theorem mul_defined (c : ℝ) (v : Option ℝ) :
    Value.Defined (Value.mul (some c) v) ↔ Value.Defined v := by
  cases v <;> simp [Value.mul, Value.Defined]

/-- The zero-factor case needs only pointwise definedness, not integrability
of the original integrand. This is strictly weaker than `scale_defined`. -/
theorem partialIntegral_scale_zero_total {X : Type} [MeasurableSpace X]
    (μ : Measure X) (f : X → Option ℝ) (hf : ∀ x, Value.Defined (f x)) :
    partialIntegral μ (fun x => Value.mul (some 0) (f x)) = some 0 := by
  have h : (fun x => Value.mul (some (0 : ℝ)) (f x)) = fun _ => some 0 := by
    funext x
    obtain ⟨v, hv⟩ := hf x
    simp [hv, Value.mul]
  rw [h, partialIntegral_zero]

theorem partialIntegral_scale_zero_defined_iff {X : Type} [MeasurableSpace X]
    (μ : Measure X) (f : X → Option ℝ) :
    Value.Defined (partialIntegral μ (fun x => Value.mul (some 0) (f x))) ↔
      ∀ x, Value.Defined (f x) := by
  rw [partialIntegral_defined_iff]
  simp only [mul_defined, mul_getD, zero_mul, integrable_zero, and_true]

theorem partialIntegral_scale_nonzero {X : Type} [MeasurableSpace X]
    (μ : Measure X) (c : ℝ) (hc : c ≠ 0) (f : X → Option ℝ) :
    partialIntegral μ (fun x => Value.mul (some c) (f x)) =
      Value.mul (some c) (partialIntegral μ f) := by
  classical
  simp only [partialIntegral, mul_defined, mul_getD,
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc), integral_const_mul]
  split <;> rfl

theorem partialIntegral_scale_defined {X : Type} [MeasurableSpace X]
    (μ : Measure X) (c : ℝ) (f : X → Option ℝ)
    (hf : Value.Defined (partialIntegral μ f)) :
    partialIntegral μ (fun x => Value.mul (some c) (f x)) =
      Value.mul (some c) (partialIntegral μ f) := by
  obtain ⟨hd, hi⟩ := (partialIntegral_defined_iff μ f).mp hf
  have hd' : ∀ x, Value.Defined (Value.mul (some c) (f x)) :=
    fun x => (mul_defined c (f x)).mpr (hd x)
  have hi' : Integrable (fun x => (Value.mul (some c) (f x)).getD 0) μ := by
    simpa only [mul_getD] using hi.const_mul c
  rw [partialIntegral_valid _ _ hd' hi', partialIntegral_valid _ _ hd hi]
  simp only [mul_getD, integral_const_mul]
  rfl

theorem partialIntegral_add_defined {X : Type} [MeasurableSpace X]
    (μ : Measure X) (f g : X → Option ℝ)
    (hf : Value.Defined (partialIntegral μ f)) (hg : Value.Defined (partialIntegral μ g)) :
    partialIntegral μ (fun x => Value.add (f x) (g x)) =
      Value.add (partialIntegral μ f) (partialIntegral μ g) := by
  obtain ⟨hfd, hfi⟩ := (partialIntegral_defined_iff μ f).mp hf
  obtain ⟨hgd, hgi⟩ := (partialIntegral_defined_iff μ g).mp hg
  have hget (x : X) : (Value.add (f x) (g x)).getD 0 = (f x).getD 0 + (g x).getD 0 := by
    obtain ⟨a, ha⟩ := hfd x
    obtain ⟨b, hb⟩ := hgd x
    simp [ha, hb, Value.add]
  have hd : ∀ x, Value.Defined (Value.add (f x) (g x)) := by
    intro x
    obtain ⟨a, ha⟩ := hfd x
    obtain ⟨b, hb⟩ := hgd x
    exact ⟨a + b, by simp [ha, hb, Value.add]⟩
  have hi : Integrable (fun x => (Value.add (f x) (g x)).getD 0) μ := by
    simpa only [hget] using hfi.add hgi
  rw [partialIntegral_valid _ _ hd hi, partialIntegral_valid _ _ hfd hfi,
    partialIntegral_valid _ _ hgd hgi]
  simp only [hget, integral_add hfi hgi]
  rfl

/-- These contraction directions may enlarge the domain, exactly as ordinary
qsym refinement rules allow. Reversing them needs the stated capabilities. -/
theorem partialIntegral_scale_refines {X : Type} [MeasurableSpace X]
    (μ : Measure X) (c : ℝ) (f : X → Option ℝ) :
    Value.Refines (Value.mul (some c) (partialIntegral μ f))
      (partialIntegral μ (fun x => Value.mul (some c) (f x))) := by
  intro v hv
  cases h : partialIntegral μ f with
  | none => simp [h, Value.mul] at hv
  | some r =>
    rw [partialIntegral_scale_defined μ c f ⟨r, h⟩]
    simpa only [h] using hv

theorem partialIntegral_add_refines {X : Type} [MeasurableSpace X]
    (μ : Measure X) (f g : X → Option ℝ) :
    Value.Refines (Value.add (partialIntegral μ f) (partialIntegral μ g))
      (partialIntegral μ (fun x => Value.add (f x) (g x))) := by
  intro v hv
  cases hf : partialIntegral μ f with
  | none => simp [hf, Value.add] at hv
  | some a =>
    cases hg : partialIntegral μ g with
    | none => simp [hf, hg, Value.add] at hv
    | some b =>
      rw [partialIntegral_add_defined μ f g ⟨a, hf⟩ ⟨b, hg⟩]
      simpa only [hf, hg] using hv

/-- A small backend-independent rule contract. A field is an obligation for
an implementation, never a new global axiom. Definedness certificates are
expressed in source-value vocabulary rather than measure-specific syntax. -/
structure FiniteIntegralTheory (X : Type) where
  integrate : (X → Option ℝ) → Option ℝ
  zero : integrate (fun _ => some 0) = some 0
  scale_zero_total : ∀ f : X → Option ℝ, (∀ x, Value.Defined (f x)) →
    integrate (fun x => Value.mul (some 0) (f x)) = some 0
  scale_nonzero : ∀ c : ℝ, c ≠ 0 → ∀ f : X → Option ℝ,
    integrate (fun x => Value.mul (some c) (f x)) = Value.mul (some c) (integrate f)
  scale_defined : ∀ c f, Value.Defined (integrate f) →
    integrate (fun x => Value.mul (some c) (f x)) = Value.mul (some c) (integrate f)
  add_defined : ∀ f g, Value.Defined (integrate f) → Value.Defined (integrate g) →
    integrate (fun x => Value.add (f x) (g x)) = Value.add (integrate f) (integrate g)
  scale_refines : ∀ c f, Value.Refines (Value.mul (some c) (integrate f))
    (integrate (fun x => Value.mul (some c) (f x)))
  add_refines : ∀ f g, Value.Refines (Value.add (integrate f) (integrate g))
    (integrate (fun x => Value.add (f x) (g x)))

def finiteIntegralTheory {X : Type} [MeasurableSpace X] (μ : Measure X) :
    FiniteIntegralTheory X where
  integrate := partialIntegral μ
  zero := partialIntegral_zero μ
  scale_zero_total := partialIntegral_scale_zero_total μ
  scale_nonzero := partialIntegral_scale_nonzero μ
  scale_defined := partialIntegral_scale_defined μ
  add_defined := partialIntegral_add_defined μ
  scale_refines := partialIntegral_scale_refines μ
  add_refines := partialIntegral_add_refines μ

end QSym
