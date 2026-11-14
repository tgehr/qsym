import QSym.SummationBounds

noncomputable section
namespace QSym.SummationAlgebra
set_option linter.unusedSectionVars false
open scoped BigOperators
open Summation
variable {ι α : Type} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]

theorem mask_and (p q : Option Bool) (x : Option α) :
    Value.mask (Value.and p q) x = Value.mask p (Value.mask q x) := by
  cases p with
  | none => rfl
  | some p => cases p <;> rfl

theorem finite_add (s : Finset ι) (f g : ι → Option α) :
    finite s (fun i => Value.add (f i) (g i)) = Value.add (finite s f) (finite s g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finite,Value.add]
  | @insert i s hi ih =>
    rw [finite_insert _ _ _ hi, finite_insert _ _ _ hi, finite_insert _ _ _ hi, ih]
    cases finite s f <;> cases finite s g <;> cases f i <;> cases g i <;>
      simp [Value.add, _root_.add_assoc, _root_.add_left_comm, _root_.add_comm]

theorem range_add (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b)))
    (f g : ℕ → Option α) (n : Option ℕ) :
    rangeValue (some (fun i => op (f i) (g i))) n = op (rangeValue (some f) n) (rangeValue (some g) n) := by
  have he : op = Value.add := by funext a b; rw [hop, Summation.add]
  rw [he]
  cases n with
  | none => rfl
  | some n => exact finite_add (Finset.range n) f g

theorem finite_filter (s : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → Option α) :
    finite s (fun i => if p i then f i else some 0) = finite (s.filter p) f := by
  classical
  have ht : (∀ i ∈ s, (if p i then f i else some 0).isSome) ↔ ∀ i ∈ s.filter p, (f i).isSome := by
    simp only [Finset.mem_filter]
    constructor
    · intro h i hi; simpa [hi.2] using h i hi.1
    · intro h i hi; by_cases hp : p i
      · simpa [hp] using h i ⟨hi,hp⟩
      · simp [hp]
  simp only [finite,ht]
  split_ifs <;> try rfl
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _; split_ifs <;> rfl

theorem finite_ge (f : ℕ → Option α) (n k : ℕ) :
    finite (Finset.range n) (fun i => if k ≤ i then f i else some 0) =
      finite (Finset.range (n-k)) (fun i => f (i+k)) := by
  classical
  rw [finite_filter]
  have he : (Finset.range n).filter (fun i => k ≤ i) =
      (Finset.range (n-k)).map ⟨fun i => i+k, fun _ _ h => Nat.add_right_cancel h⟩ := by
    ext i; simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_map,Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨i-k,by omega,by omega⟩
    · rintro ⟨j,hj,rfl⟩; omega
  rw [he,finite_reindex]; rfl

def nonzeroN (n : Option ℕ) := Functions.nonzeroZ.apply (Functions.castNZ.apply n)
def minCount (n k : Option ℕ) := Functions.floorN.apply
  (Functions.minR.apply (SummationBounds.realN n) (SummationBounds.realN k))
def tailCount (n k : Option ℕ) := Summation.intervalLength (Functions.castNZ.apply k) (Functions.castNZ.apply n)

@[simp] theorem nonzeroN_succ (n : ℕ) : nonzeroN (some (n+1)) = some true := by
  have h : (n : ℤ)+1 ≠ 0 := by omega
  simp [nonzeroN,Function1.apply,Functions.castNZ,Functions.nonzeroZ,h]
@[simp] theorem finite_none_succ (n : ℕ) : finite (Finset.range (n+1)) (fun _ => (none : Option α)) = none := by
  have h : ¬ ∀ i ∈ Finset.range (n+1), (none : Option α).isSome := by intro h; simpa using h 0 (by simp)
  exact if_neg h

@[simp] theorem minCount_some (n k : ℕ) : minCount (some n) (some k) = some (min n k) := by
  simp [minCount,Function1.apply,Function2.apply,Functions.minR,Functions.floorN,← Nat.cast_min]
@[simp] theorem tailCount_some (n k : ℕ) : tailCount (some n) (some k) = some (n-k) := by
  have h : ((n : ℤ) - (k : ℤ)).toNat = n-k := by omega
  simpa [tailCount,Function1.apply,Functions.castNZ,h] using intervalLength_some (k : ℤ) (n : ℤ)

theorem range_mask_lt (f : ℕ → Option α) (n k : Option ℕ) :
    rangeValue (some (fun i => Value.mask (Functions.ltN.apply (some i) k) (f i))) n =
    Value.mask (nonzeroN n) (rangeValue (some f) (minCount n k)) := by
  classical
  cases n with
  | none => simp [rangeValue,nonzeroN,Function1.apply,Functions.castNZ,Functions.nonzeroZ,Value.mask]
  | some n =>
    cases n with
    | zero => simp [rangeValue,finite,nonzeroN,Function1.apply,Functions.castNZ,Functions.nonzeroZ,Value.mask]
    | succ n =>
      cases k with
      | none =>
        have hn : ¬ ∀ i ∈ Finset.range (n+1), (none : Option α).isSome := by intro h; simpa using h 0 (by simp)
        simp [rangeValue,finite_none_succ,nonzeroN_succ,minCount,SummationBounds.realN,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltN,Functions.nonzeroZ,Functions.minR,Functions.floorN,Value.mask]
      | some k =>
        have hp (i : ℕ) : Value.mask (Functions.ltN.apply (some i) (some k)) (f i) = if i<k then f i else some 0 := by
          by_cases h : i<k <;> simp [Function2.apply,Functions.ltN,Value.mask,h]
        simp only [rangeValue,Option.bind,hp,minCount_some]
        rw [finite_filter]
        have he : (Finset.range (n+1)).filter (fun i => i<k) = Finset.range (min (n+1) k) := by ext i; simp [lt_min_iff]
        rw [he]
        simp only [nonzeroN_succ,Value.mask]

theorem range_mask_ge (f : Option ℕ → Option α) (n k : Option ℕ) :
    rangeValue (some (fun i => Value.mask (Functions.leN.apply k (some i)) (f (some i)))) n =
    Value.mask (nonzeroN n) (rangeValue (some (fun j => f (Functions.addN.apply (some j) k))) (tailCount n k)) := by
  classical
  cases n with
  | none => simp [rangeValue,nonzeroN,Function1.apply,Functions.castNZ,Functions.nonzeroZ,Value.mask]
  | some n =>
    cases n with
    | zero => simp [rangeValue,finite,nonzeroN,Function1.apply,Functions.castNZ,Functions.nonzeroZ,Value.mask]
    | succ n =>
      cases k with
      | none =>
        have hn : ¬ ∀ i ∈ Finset.range (n+1), (none : Option α).isSome := by intro h; simpa using h 0 (by simp)
        simp [rangeValue,finite_none_succ,nonzeroN_succ,tailCount,intervalLength,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leN,Functions.nonzeroZ,Functions.floorN,Functions.addZ,Functions.mulZ,Value.mask]
      | some k =>
        have hp (i : ℕ) : Value.mask (Functions.leN.apply (some k) (some i)) (f (some i)) = if k ≤ i then f (some i) else some 0 := by
          by_cases h : k ≤ i <;> simp [Function2.apply,Functions.leN,Value.mask,h]
        simp only [rangeValue,Option.bind,hp,tailCount_some]
        rw [finite_ge]
        simp [nonzeroN_succ,Function2.apply,Functions.addN,Value.mask]


def offsetBound (c : Option ℤ) := Functions.floorN.apply
  (SummationBounds.realZ (Functions.mulZ.apply (some (-1)) c))
def offsetNext (c : Option ℤ) := Functions.floorN.apply
  (SummationBounds.realZ (Functions.addZ.apply (Functions.mulZ.apply (some (-1)) c) (some 1)))
def offsetNonzero (i : Option ℕ) (c : Option ℤ) := Functions.nonzeroZ.apply
  (Functions.addZ.apply (Functions.castNZ.apply i) c)

private theorem floor_integer (z : ℤ) : Functions.floorN.apply (some (z : ℝ)) = some z.toNat := by
  simp only [Function1.apply,Functions.floorN,Option.bind,if_pos trivial]
  rw [← Int.floor_toNat,Int.floor_intCast]
@[simp] theorem offsetBound_some (c : ℤ) : offsetBound (some c) = some (-c).toNat := by
  have h : SummationBounds.realZ (Functions.mulZ.apply (some (-1)) (some c)) = some ((-c : ℤ) : ℝ) := by
    simp [SummationBounds.realZ,Function1.apply,Function2.apply,Functions.castZQ,Functions.castQR,Functions.mulZ]
  rw [offsetBound,h,floor_integer]
@[simp] theorem offsetNext_some (c : ℤ) : offsetNext (some c) = some (-c+1).toNat := by
  have h : SummationBounds.realZ (Functions.addZ.apply (Functions.mulZ.apply (some (-1)) (some c)) (some 1)) = some ((-c+1 : ℤ) : ℝ) := by
    simp [SummationBounds.realZ,Function1.apply,Function2.apply,Functions.castZQ,Functions.castQR,Functions.mulZ,Functions.addZ]
  rw [offsetNext,h,floor_integer]

theorem mask_ne_offset (i : Option ℕ) (c : Option ℤ) (x : Option α) :
    Value.mask (offsetNonzero i c) x = Value.add
      (Value.mask (Functions.ltN.apply i (offsetBound c)) x)
      (Value.mask (Functions.leN.apply (offsetNext c) i) x) := by
  cases i with
  | none => simp [offsetNonzero,Function1.apply,Function2.apply,Functions.castNZ,Functions.addZ,Functions.nonzeroZ,Functions.ltN,Functions.leN,Value.mask,Value.add]
  | some i =>
    cases c with
    | none => simp [offsetNonzero,offsetBound,offsetNext,SummationBounds.realZ,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.floorN,Functions.mulZ,Functions.addZ,Functions.nonzeroZ,Functions.ltN,Functions.leN,Value.mask,Value.add]
    | some c =>
      have hlo : i < (-c).toNat ↔ (i:ℤ)+c < 0 := by omega
      have hhi : (-c+1).toNat ≤ i ↔ 0 < (i:ℤ)+c := by omega
      simp only [offsetBound_some,offsetNext_some,offsetNonzero,Function1.apply,Function2.apply,
        Functions.castNZ,Functions.addZ,Functions.nonzeroZ,Functions.ltN,Functions.leN,
        Option.bind,if_pos trivial,hlo,hhi]
      rcases lt_trichotomy ((i:ℤ)+c) 0 with h | h | h <;>
        cases x <;> simp [Value.mask,Value.add,h,ne_of_lt,ne_of_gt,not_lt_of_ge,le_of_lt]

theorem mask_eq_offset (i : Option ℕ) (c : Option ℤ) (x : Option α) :
    Value.mask (Value.not (offsetNonzero i c)) x = Value.mask
      (Value.and (Functions.leN.apply (offsetBound c) i)
        (Functions.ltN.apply i (offsetNext c))) x := by
  cases i with
  | none => simp [offsetNonzero,Function1.apply,Function2.apply,Functions.castNZ,Functions.addZ,Functions.nonzeroZ,Functions.ltN,Functions.leN,Value.not,Value.and,Value.mask]
  | some i =>
    cases c with
    | none => simp [offsetNonzero,offsetBound,offsetNext,SummationBounds.realZ,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.floorN,Functions.mulZ,Functions.addZ,Functions.nonzeroZ,Functions.ltN,Functions.leN,Value.not,Value.and,Value.mask]
    | some c =>
      have h : ((-c).toNat ≤ i ∧ i < (-c+1).toNat) ↔ (i:ℤ)+c=0 := by omega
      simp only [offsetBound_some,offsetNext_some,offsetNonzero,Function1.apply,Function2.apply,
        Functions.castNZ,Functions.addZ,Functions.nonzeroZ,Functions.ltN,Functions.leN,
        Option.bind,if_pos trivial]
      by_cases hlo : (-c).toNat ≤ i <;> by_cases hhi : i < (-c+1).toNat <;>
        simp only [hlo,hhi,decide_true,decide_false,Value.not,Value.and,Value.mask] <;> simp_all [Option.map]

theorem mask_ne_offset_op (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b)))
    (i : Option ℕ) (c : Option ℤ) (x : Option α) :
    Value.mask (offsetNonzero i c) x = op
      (Value.mask (Functions.ltN.apply i (offsetBound c)) x)
      (Value.mask (Functions.leN.apply (offsetNext c) i) x) := by
  rw [hop,← Summation.add]
  exact mask_ne_offset i c x

end QSym.SummationAlgebra
