import QSym.Summation

noncomputable section
namespace QSym.Summation
private theorem summable_parities {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (f : ℕ → E) :
    Summable f ↔ (Summable fun k => f (2*k)) ∧ Summable (fun k => f (2*k+1)) := by
  constructor
  · intro h
    exact ⟨h.comp_injective (i := fun n : ℕ => 2*n) (by intro a b h; dsimp only at h; omega),
      h.comp_injective (i := fun n : ℕ => 2*n+1) (by intro a b h; dsimp only at h; omega)⟩
  · exact fun ⟨a,b⟩ => (a.hasSum.even_add_odd b.hasSum).summable

/-- Absolute summation over naturals can group the even and odd indices.
Presence at every index is preserved, including at zero summands. -/
theorem even_odd {E : Type} [NormedAddCommGroup E] [CompleteSpace E] (t : ℕ → Option E) :
    value norm (some t) = Value.add (value norm (some fun k => t (2*k)))
      (value norm (some fun k => t (2*k+1))) := by
  classical
  let even (n : ℕ) := t (2*n)
  let odd (n : ℕ) := t (2*n+1)
  let good (f : ℕ → Option E) := (∀ i, (f i).isSome = true) ∧
    Summable (fun i => ‖(f i).getD 0‖) ∧ Summable (fun i => (f i).getD 0)
  have dom : (∀ i, (t i).isSome = true) ↔ (∀ i, (even i).isSome = true) ∧ ∀ i, (odd i).isSome = true := by
    refine ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, ?_⟩
    rintro ⟨he, ho⟩ i
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · exact he k
    · exact ho k
  have split : good t ↔ good even ∧ good odd := by
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _) ∧ (_ ∧ _ ∧ _)
    rw [dom, summable_parities (fun i => ‖(t i).getD 0‖), summable_parities (fun i => (t i).getD 0)]
    dsimp only [even, odd]; tauto
  change (if good t then some _ else none) = Value.add (if good even then some _ else none) (if good odd then some _ else none)
  by_cases he : good even
  · by_cases ho : good odd
    · rw [if_pos he, if_pos ho, if_pos (split.mpr ⟨he, ho⟩)]
      exact congrArg some (tsum_even_add_odd (f := fun i => (t i).getD 0) he.2.2 ho.2.2).symm
    · rw [if_pos he, if_neg ho, if_neg (fun h => ho (split.mp h).2)]
      rfl
  · rw [if_neg he, if_neg (fun h => he (split.mp h).1)]
    rfl
end QSym.Summation
