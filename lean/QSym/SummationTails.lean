import QSym.SummationAlgebra
import QSym.SummationNaturalTails

noncomputable section
namespace QSym.SummationTails
open Summation
variable {ι κ α : Type} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]

theorem reindex (weight : α → ℝ) (hw : weight 0 = 0) (e : ι ↪ κ)
    (f : κ → Option α) (hz : ∀ x ∉ Set.range e, f x = some 0) :
    value weight (some f) = value weight (some (fun i => f (e i))) := by
  classical
  have ht : (∀ x, (f x).isSome) ↔ ∀ i, (f (e i)).isSome := by
    constructor
    · intro h i; exact h (e i)
    · intro h x; by_cases hx : x ∈ Set.range e
      · obtain ⟨i,rfl⟩ := hx; exact h i
      · simp [hz x hx]
  have hn : (Summable (fun i => weight ((f (e i)).getD 0))) ↔ Summable (fun x => weight ((f x).getD 0)) :=
    e.injective.summable_iff (f := fun x => weight ((f x).getD 0)) (by intro x hx; dsimp; rw [hz x hx]; exact hw)
  have hs : (Summable (fun i => (f (e i)).getD 0)) ↔ Summable (fun x => (f x).getD 0) :=
    e.injective.summable_iff (f := fun x => (f x).getD 0) (by intro x hx; dsimp; rw [hz x hx]; rfl)
  have he : (∑' i, (f (e i)).getD 0) = ∑' x, (f x).getD 0 :=
    e.injective.tsum_eq (f := fun x => (f x).getD 0) (by
      intro x hx
      by_contra hnot
      exact hx (by change (f x).getD 0 = 0; rw [hz x hnot]; rfl))
  simp only [value,Option.bind,ht,hn,hs,he]

theorem lowerN (weight : α → ℝ) (hw : weight 0 = 0)
    (f : Option ℕ → Option α) (k : Option ℕ) :
    value weight (some (fun i : ℕ => Value.mask (Functions.leN.apply k (some i)) (f (some i)))) =
      k.bind (fun _ => value weight (some (fun j : ℕ => f (Functions.addN.apply (some j) k)))) := by
  classical
  cases k with
  | none => exact undefined_term weight _ 0 (by simp [Function2.apply,Functions.leN,Value.mask])
  | some k =>
    let e : ℕ ↪ ℕ := ⟨fun j => j+k, fun _ _ h => Nat.add_right_cancel h⟩
    rw [reindex weight hw e _ (by
      intro i hi
      have h : ¬ k ≤ i := by intro h; exact hi ⟨i-k, by simp [e,Nat.sub_add_cancel h]⟩
      simp [Function2.apply,Functions.leN,Value.mask,h])]
    simp [e,Function2.apply,Functions.leN,Functions.addN,Value.mask]

theorem lowerZ (weight : α → ℝ) (hw : weight 0 = 0)
    (f : Option ℤ → Option α) (k : Option ℤ) :
    value weight (some (fun i : ℤ => Value.mask (Functions.leZ.apply k (some i)) (f (some i)))) =
      k.bind (fun _ => value weight (some (fun j : ℕ => f
        (Functions.addZ.apply (Functions.castNZ.apply (some j)) k)))) := by
  classical
  cases k with
  | none => exact undefined_term weight _ 0 (by simp [Function2.apply,Functions.leZ,Value.mask])
  | some k =>
    let e : ℕ ↪ ℤ := ⟨fun j => (j:ℤ)+k, fun _ _ h => Nat.cast_injective (add_right_cancel h)⟩
    rw [reindex weight hw e _ (by
      intro i hi
      have h : ¬ k ≤ i := by
        intro h; apply hi; refine ⟨(i-k).toNat, ?_⟩; dsimp [e]; omega
      simp [Function2.apply,Functions.leZ,Value.mask,h])]
    have h (j : ℕ) : k ≤ (j:ℤ)+k := by omega
    simp [e,Function1.apply,Function2.apply,Functions.leZ,Functions.castNZ,Functions.addZ,Value.mask,h]

theorem upperZ (weight : α → ℝ) (hw : weight 0 = 0)
    (f : Option ℤ → Option α) (k : Option ℤ) :
    value weight (some (fun i : ℤ => Value.mask (Functions.ltZ.apply (some i) k) (f (some i)))) =
      k.bind (fun _ => value weight (some (fun j : ℕ => f
        (Functions.addZ.apply (Functions.addZ.apply k (some (-1)))
          (Functions.mulZ.apply (some (-1)) (Functions.castNZ.apply (some j))))))) := by
  classical
  cases k with
  | none => exact undefined_term weight _ 0 (by simp [Function2.apply,Functions.ltZ,Value.mask])
  | some k =>
    let e : ℕ ↪ ℤ := ⟨fun j => k-1-(j:ℤ), by
      intro a b h
      change k-1-(a:ℤ)=k-1-(b:ℤ) at h
      exact_mod_cast (sub_right_inj.mp h)⟩
    rw [reindex weight hw e _ (by
      intro i hi
      have h : ¬ i < k := by
        intro h; apply hi; refine ⟨(k-1-i).toNat, ?_⟩; dsimp [e]; omega
      simp [Function2.apply,Functions.ltZ,Value.mask,h])]
    have h (j : ℕ) : k-1-(j:ℤ)<k := by omega
    simp [e,Function1.apply,Function2.apply,Functions.ltZ,Functions.castNZ,Functions.addZ,Functions.mulZ,Value.mask,h,sub_eq_add_neg,show ∀ j : ℕ, (-1:ℤ)<j by intro j; omega]

end QSym.SummationTails
