import QSym.SummationMasks

noncomputable section
namespace QSym.SummationPrefix
open Summation
open scoped BigOperators
variable {α : Type} [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α] [T2Space α]

/-- Removing a finite prefix preserves both convergence requirements. -/
theorem split_prefix (weight : α → ℝ) (f : ℕ → Option α) (k : ℕ) :
    value weight (some f) = Value.add (finite (Finset.range k) f)
      (value weight (some (fun i => f (i+k)))) := by
  classical
  have ht : (∀ i, (f i).isSome) ↔
      (∀ i ∈ Finset.range k, (f i).isSome) ∧ (∀ i, (f (i+k)).isSome) := by
    constructor
    · intro h; exact ⟨fun i _ => h i, fun i => h (i+k)⟩
    · rintro ⟨hf,ht⟩ i
      by_cases hi : i < k
      · exact hf i (Finset.mem_range.mpr hi)
      · simpa [Nat.sub_add_cancel (Nat.le_of_not_gt hi)] using ht (i-k)
  have ha := summable_nat_add_iff (f := fun i => weight ((f i).getD 0)) k
  have hs := summable_nat_add_iff (f := fun i => (f i).getD 0) k
  by_cases hf : ∀ i ∈ Finset.range k, (f i).isSome
  · have hf' : ∀ i < k, (f i).isSome := by simpa using hf
    by_cases htt : ∀ i, (f (i+k)).isSome
    · by_cases hn : Summable (fun i => weight ((f i).getD 0))
      · by_cases h : Summable (fun i => (f i).getD 0)
        · have hall := ht.mpr ⟨hf,htt⟩
          have hn' := ha.mpr hn
          have h' := hs.mpr h
          simp only [value,Option.bind,finite,if_pos hf,hall,htt,hn,h,hn',h',true_and,and_true,implies_true,forall_const,ite_true,Value.add]
          exact congrArg some (h.sum_add_tsum_nat_add k).symm
        · simp [value,finite,hf,ht,htt,hn,h,ha,hs,Value.add]
      · simp [value,finite,hf,ht,htt,hn,ha,hs,Value.add]
    · simp [value,finite,hf,ht,htt,Value.add]
  · have hf' : ¬ ∀ i < k, (f i).isSome := by simpa using hf
    simp [value,finite,hf,hf',ht,Value.add]

/-- The excluded term need not be defined; it is never evaluated. -/
theorem exclude (weight : α → ℝ) (f : ℕ → Option α) (k : ℕ) :
    value weight (some (fun i => if i = k then some 0 else f i)) =
      Value.add (finite (Finset.range k) f)
        (value weight (some (fun i => f (i+(k+1))))) := by
  classical
  rw [split_prefix weight _ (k+1)]
  have hf : finite (Finset.range (k+1)) (fun i => if i=k then some 0 else f i) = finite (Finset.range k) f := by
    rw [range_succ]
    have he : finite (Finset.range k) (fun i => if i=k then some 0 else f i) = finite (Finset.range k) f := by
      unfold finite
      have h (i : ℕ) (hi : i ∈ Finset.range k) : i ≠ k := Nat.ne_of_lt (Finset.mem_range.mp hi)
      simp only [show (∀ i ∈ Finset.range k, ((if i=k then some 0 else f i) : Option α).isSome) ↔
        ∀ i ∈ Finset.range k, (f i).isSome by
          apply forall_congr'; intro i; apply forall_congr'; intro hi; simp [h i hi]]
      congr 2
      apply Finset.sum_congr rfl; intro i hi; simp [h i hi]
    rw [he]; simp
  rw [hf]
  congr 2
  apply congrArg some
  funext i; simp [show i+(k+1) ≠ k by omega]

open SummationAlgebra

theorem exclude_offset (weight : α → ℝ)
    (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b)))
    (f : Option ℕ → Option α) (c : Option ℤ) :
    value weight (some (fun i => Value.mask (offsetNonzero (some i) c) (f (some i)))) =
      op (rangeValue (some (fun i => f (some i))) (offsetBound c))
        (value weight (some (fun i => f (Functions.addN.apply (some i) (offsetNext c))))) := by
  classical
  have he : op = Value.add := by funext a b; rw [hop,Summation.add]
  rw [he]
  cases c with
  | none =>
    rw [undefined_term weight _ 0 (by simp [offsetNonzero,Function1.apply,Function2.apply,Value.mask])]
    rfl
  | some c =>
    rw [offsetBound_some,offsetNext_some]
    by_cases hc : c ≤ 0
    · have hc' : (-c+1).toNat = (-c).toNat+1 := by omega
      have hp (i : ℕ) : Value.mask (offsetNonzero (some i) (some c)) (f (some i)) =
          if i = (-c).toNat then some 0 else f (some i) := by
        have h : (i : ℤ)+c = 0 ↔ i = (-c).toNat := by omega
        by_cases hi : i = (-c).toNat
        · have hz := h.mpr hi
          simp only [offsetNonzero,Function1.apply,Function2.apply,Functions.castNZ,Functions.addZ,Functions.nonzeroZ,Option.bind,if_pos trivial,hz,ne_eq,not_true_eq_false,decide_false,Value.mask,if_pos hi]
        · have hz : (i:ℤ)+c ≠ 0 := by simpa [h] using hi
          simp [offsetNonzero,Function1.apply,Function2.apply,Functions.castNZ,Functions.addZ,Functions.nonzeroZ,Value.mask,hz,hi]
      simp only [hp,hc']
      simpa [rangeValue,Function2.apply,Functions.addN] using exclude weight (fun i => f (some i)) (-c).toNat
    · have hb : (-c).toNat=0 := by omega
      have hn : (-c+1).toNat=0 := by omega
      have hp (i : ℕ) : Value.mask (offsetNonzero (some i) (some c)) (f (some i)) = f (some i) := by
        have h : (i:ℤ)+c ≠ 0 := by omega
        simp [offsetNonzero,Function1.apply,Function2.apply,Functions.castNZ,Functions.addZ,Functions.nonzeroZ,Value.mask,h]
      simp only [hp,hb,hn]
      simp only [rangeValue,Option.bind,finite,Finset.range_zero,Finset.not_mem_empty,IsEmpty.forall_iff,implies_true,if_pos,Finset.sum_empty,Function2.apply,Functions.addN,if_pos trivial,Nat.add_zero]
      cases value weight (some (fun i => f (some i))) <;> simp [Value.add]

end QSym.SummationPrefix
