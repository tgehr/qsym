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

/-- Strict integration over a disjoint sum is the strict sum of its branches.
In particular, failure or nonintegrability in either branch is retained. -/
theorem partialIntegral_sum {Ω Ψ : Type} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) (f : Ω → Option ℝ) (g : Ψ → Option ℝ) :
    partialIntegral (μ.map Sum.inl + ν.map Sum.inr) (Sum.elim f g) =
      Value.add (partialIntegral μ f) (partialIntegral ν g) := by
  have hinl : MeasurableEmbedding (@Sum.inl Ω Ψ) :=
    { injective := Sum.inl_injective
      measurable := measurable_inl
      measurableSet_image' := by
        intro s hs
        exact MeasurableSet.inl_image hs }
  have hinr : MeasurableEmbedding (@Sum.inr Ω Ψ) :=
    { injective := Sum.inr_injective
      measurable := measurable_inr
      measurableSet_image' := by
        intro s hs
        exact MeasurableSet.inr_image hs }
  have hd : (∀ z, Value.Defined (Sum.elim f g z)) ↔
      (∀ x, Value.Defined (f x)) ∧ (∀ y, Value.Defined (g y)) := by
    constructor
    · intro h
      exact ⟨fun x => h (Sum.inl x), fun y => h (Sum.inr y)⟩
    · rintro ⟨hf, hg⟩ (x | y)
      · exact hf x
      · exact hg y
  have hi : Integrable (fun z => (Sum.elim f g z).getD 0)
      (μ.map Sum.inl + ν.map Sum.inr) ↔
      Integrable (fun x => (f x).getD 0) μ ∧ Integrable (fun y => (g y).getD 0) ν := by
    rw [integrable_add_measure, hinl.integrable_map_iff, hinr.integrable_map_iff]
    rfl
  have hdefined : Value.Defined
      (partialIntegral (μ.map Sum.inl + ν.map Sum.inr) (Sum.elim f g)) ↔
      Value.Defined (partialIntegral μ f) ∧ Value.Defined (partialIntegral ν g) := by
    rw [partialIntegral_defined_iff, partialIntegral_defined_iff, partialIntegral_defined_iff]
    constructor
    · intro h
      exact ⟨⟨(hd.mp h.1).1, (hi.mp h.2).1⟩, ⟨(hd.mp h.1).2, (hi.mp h.2).2⟩⟩
    · rintro ⟨⟨hfd, hfi⟩, ⟨hgd, hgi⟩⟩
      exact ⟨hd.mpr ⟨hfd, hgd⟩, hi.mpr ⟨hfi, hgi⟩⟩
  cases hf : partialIntegral μ f with
  | none =>
    have hs : partialIntegral (μ.map Sum.inl + ν.map Sum.inr) (Sum.elim f g) = none := by
      cases hs : partialIntegral (μ.map Sum.inl + ν.map Sum.inr) (Sum.elim f g) with
      | none => rfl
      | some c =>
        have hfd := (hdefined.mp ⟨c, hs⟩).1
        rw [hf] at hfd
        simp [Value.Defined] at hfd
    rw [hs]
    cases partialIntegral ν g <;> rfl
  | some a =>
    cases hg : partialIntegral ν g with
    | none =>
      have hs : partialIntegral (μ.map Sum.inl + ν.map Sum.inr) (Sum.elim f g) = none := by
        cases hs : partialIntegral (μ.map Sum.inl + ν.map Sum.inr) (Sum.elim f g) with
        | none => rfl
        | some c =>
          have hgd := (hdefined.mp ⟨c, hs⟩).2
          rw [hg] at hgd
          simp [Value.Defined] at hgd
      rw [hs]
      rfl
    | some b =>
      obtain ⟨hfd, hfi⟩ := (partialIntegral_defined_iff μ f).mp ⟨a, hf⟩
      obtain ⟨hgd, hgi⟩ := (partialIntegral_defined_iff ν g).mp ⟨b, hg⟩
      have hfi' : Integrable (fun z => (Sum.elim f g z).getD 0) (μ.map Sum.inl) :=
        hinl.integrable_map_iff.mpr hfi
      have hgi' : Integrable (fun z => (Sum.elim f g z).getD 0) (ν.map Sum.inr) :=
        hinr.integrable_map_iff.mpr hgi
      rw [partialIntegral_valid _ _ (hd.mpr ⟨hfd, hgd⟩) (hi.mpr ⟨hfi, hgi⟩)]
      simp only [Value.add]
      congr 1
      rw [integral_add_measure hfi' hgi', hinl.integral_map, hinr.integral_map]
      have ha : (∫ x, (f x).getD 0 ∂μ) = a := by
        have h := partialIntegral_valid μ f hfd hfi
        rw [hf] at h
        exact (Option.some.inj h).symm
      have hb : (∫ y, (g y).getD 0 ∂ν) = b := by
        have h := partialIntegral_valid ν g hgd hgi
        rw [hg] at h
        exact (Option.some.inj h).symm
      change (∫ x, (f x).getD 0 ∂μ) + (∫ y, (g y).getD 0 ∂ν) = a + b
      rw [ha, hb]

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
