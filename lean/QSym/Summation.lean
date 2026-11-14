import QSym.Binding
import QSym.RepeatedSpectra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Int

/-! Partial, absolutely convergent sums. All summands must be defined. The
absolute-convergence predicate is independent of the ordered-partial-sum limit.
In particular `tsum`'s conventional value for a divergent series is never exposed. -/
set_option linter.unusedSectionVars false
namespace QSym.Summation
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {ι α : Type} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]

noncomputable def value (weight : α → ℝ) (f : Option (ι → Option α)) : Option α := by
  classical
  exact f.bind fun g => if (∀ i, (g i).isSome) ∧
      Summable (fun i => weight ((g i).getD 0)) ∧ Summable (fun i => (g i).getD 0)
    then some (∑' i, (g i).getD 0) else none

theorem of_hasSum (weight : α → ℝ) (f : ι → Option α) (g : ι → α) (a : α)
    (h : ∀ i, f i = some (g i)) (ha : Summable (fun i => weight (g i)))
    (hs : HasSum g a) : value weight (some f) = some a := by
  classical
  have hf : f = fun i => some (g i) := funext h
  rw [hf]
  simpa [value, ha, hs.summable] using hs.tsum_eq

theorem undefined_term (weight : α → ℝ) (f : ι → Option α) (i : ι)
    (h : f i = none) : value weight (some f) = none := by
  classical
  have hn : ¬ ∀ j, (f j).isSome := by intro ht; simpa [h] using ht i
  simp [value, hn]

theorem zero (weight : α → ℝ) (hw : weight 0 = 0) :
    value weight (some (fun _ : ι => some 0)) = some 0 := by
  apply of_hasSum weight _ (fun _ => 0) 0 (fun _ => rfl)
  · simpa [hw] using (summable_zero : Summable (fun _ : ι => (0 : ℝ)))
  · exact hasSum_zero

theorem zero_literal (weight : α → ℝ) (hw : weight 0 = 0) (z : Option α) (hz : z = some 0) :
    value weight (some (fun _ : ι => z)) = z := by rw [hz]; exact zero weight hw

noncomputable def finite (s : Finset ι) (f : ι → Option α) : Option α := by
  classical
  exact if ∀ i ∈ s, (f i).isSome then some (∑ i ∈ s, (f i).getD 0) else none

theorem finite_support (weight : α → ℝ) (hw : weight 0 = 0)
    (s : Finset ι) (f : ι → Option α) (h : ∀ i ∉ s, f i = some 0) :
    value weight (some f) = finite s f := by
  classical
  by_cases ht : ∀ i ∈ s, (f i).isSome
  · have hall : ∀ i, (f i).isSome := by
      intro i; by_cases hi : i ∈ s
      · exact ht i hi
      · simp [h i hi]
    have hz : ∀ i ∉ s, (f i).getD 0 = 0 := by intros; simp_all
    have hn : Summable (fun i => weight ((f i).getD 0)) :=
      summable_of_ne_finset_zero (s := s) (by intros; simp_all)
    simp [value, finite, ht, hall, hn, summable_of_ne_finset_zero hz, tsum_eq_sum hz]
  · have hn : ¬ ∀ i, (f i).isSome := by intro hall; exact ht (fun i _ => hall i)
    simp [value, finite, ht, hn]

theorem finite_empty (f : ι → Option α) : finite ∅ f = some 0 := by simp [finite]

theorem finite_insert [DecidableEq ι] (s : Finset ι) (i : ι) (f : ι → Option α)
    (hi : i ∉ s) : finite (insert i s) f =
      (finite s f).bind (fun a => (f i).map (fun b => a + b)) := by
  classical
  by_cases ht : ∀ j ∈ s, (f j).isSome
  · cases he : f i with
    | none => simp [finite, hi, ht, he]
    | some x =>
      simp only [finite, Finset.mem_insert, forall_eq_or_imp, he, Option.isSome_some, Bool.true_eq, true_and, ht, ↓reduceIte, Option.bind_some, Option.map_some, Finset.sum_insert hi, Option.getD_some]
      rw [add_comm, if_pos ht, if_pos ht]
      rfl
  · have hn : ¬ ∀ j ∈ insert i s, (f j).isSome := by
      intro hh; exact ht (fun j hj => hh j (Finset.mem_insert_of_mem hj))
    simp [finite, ht, hn]

theorem range_succ (f : ℕ → Option α) (n : ℕ) :
    finite (Finset.range (n+1)) f =
      (finite (Finset.range n) f).bind (fun a => (f n).map (fun b => a + b)) := by
  rw [Finset.range_add_one, finite_insert _ _ _ (Finset.not_mem_range_self)]

theorem range_mask (weight : α → ℝ) (hw : weight 0 = 0) (f : ℕ → Option α) (n : ℕ) :
    value weight (some (fun i => if i < n then f i else some 0)) = finite (Finset.range n) f := by
  classical
  rw [finite_support weight hw (Finset.range n) _ (by intros; simp_all)]
  simp only [finite, Finset.mem_range]
  congr 1
  · apply forall_congr
    intro i
    apply propext
    constructor <;> intro h hi <;> simpa [hi] using h hi
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi; simp [Finset.mem_range.mp hi]

theorem delta [DecidableEq ι] (weight : α → ℝ) (hw : weight 0 = 0)
    (k : ι) (x : Option α) :
    value weight (some (fun i => if i = k then x else some 0)) = x := by
  cases x with
  | none => exact undefined_term weight _ k (if_pos rfl)
  | some x =>
    apply of_hasSum weight _ (fun i => if i = k then x else 0) x
    · intro i; split_ifs <;> rfl
    · exact summable_of_ne_finset_zero (s := {k}) (by intros; simp_all)
    · exact hasSum_ite_eq k x

noncomputable def rangeValue (f : Option (ℕ → Option α)) (n : Option ℕ) : Option α :=
  f.bind (fun f => n.bind (fun n => finite (Finset.range n) f))

theorem delta_select [DecidableEq ι] (weight : α → ℝ) (hw : weight 0 = 0)
    (k : ι) (f : ι → Option α) :
    value weight (some (fun i => if i = k then f i else some 0)) = f k := by
  have h : (fun i => if i = k then f i else some 0) = (fun i => if i = k then f k else some 0) := by
    funext i; split_ifs with hi <;> simp_all
  rw [h, delta weight hw]

theorem deltaN (weight : α → ℝ) (hw : weight 0 = 0) (f : ℕ → Option α) (k : Option ℕ) :
    value weight (some (fun i => Value.mask (Value.not (Functions.nonzeroZ.apply
      (Functions.addZ.apply (Functions.castNZ.apply (some i))
        (Functions.mulZ.apply (some (-1)) (Functions.castNZ.apply k))))) (f i))) = k.bind f := by
  cases k with
  | none => exact undefined_term weight _ 0 (by simp [Function1.apply, Function2.apply, Functions.castNZ, Functions.addZ, Functions.mulZ, Functions.nonzeroZ, Value.not, Value.mask])
  | some k =>
    have hp : (fun i => Value.mask (Value.not (Functions.nonzeroZ.apply
      (Functions.addZ.apply (Functions.castNZ.apply (some i))
        (Functions.mulZ.apply (some (-1)) (Functions.castNZ.apply (some k)))))) (f i)) =
        (fun i => if i = k then f i else some 0) := by
      funext i; by_cases hi : i = k <;>
        simp [Value.mask, Value.not, Function1.apply, Function2.apply, Functions.nonzeroZ,
          Functions.castNZ, Functions.addZ, Functions.mulZ, hi, ← sub_eq_add_neg, sub_eq_zero]
    rw [hp]; exact delta_select weight hw k f

theorem deltaZ (weight : α → ℝ) (hw : weight 0 = 0) (f : ℤ → Option α) (k : Option ℤ) :
    value weight (some (fun i => Value.mask (Value.not (Functions.nonzeroZ.apply
      (Functions.addZ.apply (some i) (Functions.mulZ.apply (some (-1)) k)))) (f i))) = k.bind f := by
  cases k with
  | none => exact undefined_term weight _ 0 rfl
  | some k =>
    have hp : (fun i => Value.mask (Value.not (Functions.nonzeroZ.apply
      (Functions.addZ.apply (some i) (Functions.mulZ.apply (some (-1)) (some k))))) (f i)) =
        (fun i => if i = k then f i else some 0) := by
      funext i; by_cases hi : i = k <;>
        simp [Value.mask, Value.not, Function1.apply, Function2.apply, Functions.nonzeroZ,
          Functions.addZ, Functions.mulZ, hi, ← sub_eq_add_neg, sub_eq_zero]
    rw [hp]; exact delta_select weight hw k f

theorem deltaZ_offset (weight : α → ℝ) (hw : weight 0 = 0) (f : ℤ → Option α) (c : Option ℤ) :
    value weight (some (fun i => Value.mask (Value.not (Functions.nonzeroZ.apply
      (Functions.addZ.apply (some i) c))) (f i))) =
      (Functions.mulZ.apply (some (-1)) c).bind f := by
  cases c with
  | none =>
    rw [undefined_term weight _ 0 (by simp [Value.mask,Value.not,Function1.apply,Function2.apply,Functions.nonzeroZ,Functions.addZ])]
    simp [Function2.apply,Functions.mulZ]
  | some c =>
    have hp : (fun i => Value.mask (Value.not (Functions.nonzeroZ.apply
      (Functions.addZ.apply (some i) (some c)))) (f i)) =
        (fun i => if i = -c then f i else some 0) := by
      funext i; by_cases hi : i = -c <;>
        simp [Value.mask,Value.not,Function1.apply,Function2.apply,Functions.nonzeroZ,Functions.addZ,hi,add_eq_zero_iff_eq_neg]
    rw [hp,delta_select weight hw]
    simp [Function2.apply,Functions.mulZ]

theorem range_convert_le (weight : α → ℝ) (hw : weight 0 = 0) (f : ℕ → Option α) (n : Option ℕ) :
    value weight (some (fun i => Value.mask (Functions.leN.apply (some i) n) (f i))) =
      rangeValue (some f) (Functions.addN.apply n (some 1)) := by
  cases n with
  | none => exact undefined_term weight _ 0 rfl
  | some n =>
    have h : (fun i => Value.mask (Functions.leN.apply (some i) (some n)) (f i)) =
        (fun i => if i < n+1 then f i else some 0) := by
      funext i; by_cases hi : i ≤ n <;> simp [Function2.apply, Functions.leN, Value.mask, Nat.lt_succ_iff, hi]
    rw [h]
    simpa [Function2.apply, Functions.addN] using range_mask weight hw f (n+1)

theorem finite_congr (s : Finset ι) {f g : ι → Option α} (h : ∀ i ∈ s, f i = g i) :
    finite s f = finite s g := by
  classical
  unfold finite
  congr 1
  · apply propext
    constructor <;> intro hh i hi
    · rw [← h i hi]; exact hh i hi
    · rw [h i hi]; exact hh i hi
  · congr 1
    exact Finset.sum_congr rfl (fun i hi => congrArg (fun x => x.getD 0) (h i hi))

theorem finite_reindex {κ : Type} (s : Finset ι) (e : ι ↪ κ) (f : κ → Option α) :
    finite (s.map e) f = finite s (fun i => f (e i)) := by
  classical
  simp [finite, Finset.sum_map]

theorem interval_nat (weight : α → ℝ) (hw : weight 0 = 0) (f : ℕ → Option α) (l u : ℕ) :
    value weight (some (fun i => if l ≤ i ∧ i < u then f i else some 0)) =
      finite (Finset.range (u-l)) (fun i => f (i+l)) := by
  classical
  rw [finite_support weight hw (Finset.Ico l u) _ (by intros; simp_all)]
  rw [finite_congr (f := fun i => if l ≤ i ∧ i < u then f i else some 0)
      (g := f) _ (by intro i hi; simp_all)]
  let e : ℕ ↪ ℕ := ⟨fun i => i+l, fun _ _ h => Nat.add_right_cancel h⟩
  have he : Finset.Ico l u = (Finset.range (u-l)).map e := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, e, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨i-l, by omega, by omega⟩
    · rintro ⟨j,hj,rfl⟩; omega
  rw [he, finite_reindex]; rfl

theorem interval_int (weight : α → ℝ) (hw : weight 0 = 0) (f : ℤ → Option α) (l u : ℤ) :
    value weight (some (fun i => if l ≤ i ∧ i < u then f i else some 0)) =
      finite (Finset.range (u-l).toNat) (fun i => f ((i:ℤ)+l)) := by
  classical
  rw [finite_support weight hw (Finset.Ico l u) _ (by intros; simp_all)]
  rw [finite_congr (f := fun i => if l ≤ i ∧ i < u then f i else some 0)
      (g := f) _ (by intro i hi; simp_all)]
  let e : ℕ ↪ ℤ := ⟨fun i => (i:ℤ)+l, fun _ _ h => Nat.cast_injective (add_right_cancel h)⟩
  have he : Finset.Ico l u = (Finset.range (u-l).toNat).map e := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, e, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨(i-l).toNat, by omega, by omega⟩
    · rintro ⟨j,hj,rfl⟩; omega
  rw [he, finite_reindex]; rfl

theorem boundsN (weight : α → ℝ) (f : ℕ → Option α) (l u : Option ℕ) (strict inclusive : Bool) :
    value weight (some (fun i => Value.mask (Value.and
      ((if strict then Functions.ltN.apply else Functions.leN.apply) l (some i))
      ((if inclusive then Functions.leN.apply else Functions.ltN.apply) (some i) u)) (f i))) =
    value weight (some (fun i => Value.mask (Value.and
      (Functions.leN.apply (if strict then Functions.addN.apply l (some 1) else l) (some i))
      (Functions.ltN.apply (some i) (if inclusive then Functions.addN.apply u (some 1) else u))) (f i))) := by
  apply congrArg (value weight)
  apply congrArg some
  funext i
  have hl : (if strict then Functions.ltN.apply else Functions.leN.apply) l (some i) =
      Functions.leN.apply (if strict then Functions.addN.apply l (some 1) else l) (some i) := by
    cases strict <;> cases l <;> simp [Function2.apply,Functions.ltN,Functions.leN,Functions.addN,Nat.succ_le_iff]
  have hu : (if inclusive then Functions.leN.apply else Functions.ltN.apply) (some i) u =
      Functions.ltN.apply (some i) (if inclusive then Functions.addN.apply u (some 1) else u) := by
    cases inclusive <;> cases u <;> simp [Function2.apply,Functions.ltN,Functions.leN,Functions.addN,Nat.lt_succ_iff]
  rw [hl,hu]

theorem boundsZ (weight : α → ℝ) (f : ℤ → Option α) (l u : Option ℤ) (strict inclusive : Bool) :
    value weight (some (fun i => Value.mask (Value.and
      ((if strict then Functions.ltZ.apply else Functions.leZ.apply) l (some i))
      ((if inclusive then Functions.leZ.apply else Functions.ltZ.apply) (some i) u)) (f i))) =
    value weight (some (fun i => Value.mask (Value.and
      (Functions.leZ.apply (if strict then Functions.addZ.apply l (some 1) else l) (some i))
      (Functions.ltZ.apply (some i) (if inclusive then Functions.addZ.apply u (some 1) else u))) (f i))) := by
  apply congrArg (value weight)
  apply congrArg some
  funext i
  have hl : (if strict then Functions.ltZ.apply else Functions.leZ.apply) l (some i) =
      Functions.leZ.apply (if strict then Functions.addZ.apply l (some 1) else l) (some i) := by
    cases strict <;> cases l <;> simp [Function2.apply,Functions.ltZ,Functions.leZ,Functions.addZ,Int.add_one_le_iff]
  have hu : (if inclusive then Functions.leZ.apply else Functions.ltZ.apply) (some i) u =
      Functions.ltZ.apply (some i) (if inclusive then Functions.addZ.apply u (some 1) else u) := by
    cases inclusive <;> cases u <;> simp [Function2.apply,Functions.ltZ,Functions.leZ,Functions.addZ,Int.lt_add_one_iff]
  rw [hl,hu]

noncomputable def intervalLength (l u : Option ℤ) : Option ℕ :=
  Functions.floorN.apply (Functions.castQR.apply (Functions.castZQ.apply
    (Functions.addZ.apply u (Functions.mulZ.apply (some (-1)) l))))

theorem intervalLength_some (l u : ℤ) : intervalLength (some l) (some u) = some (u-l).toNat := by
  simp [intervalLength, Function1.apply, Function2.apply, Functions.floorN, Functions.castQR,
    Functions.castZQ, Functions.addZ, Functions.mulZ, ← sub_eq_add_neg, ← Int.floor_toNat]

theorem interval_convertZ (weight : α → ℝ) (hw : weight 0 = 0)
    (f : Option ℤ → Option α) (l u : Option ℤ) :
    value weight (some (fun i : ℤ => Value.mask
      (Value.and (Functions.leZ.apply l (some i)) (Functions.ltZ.apply (some i) u)) (f (some i)))) =
    rangeValue (some (fun j : ℕ => f (Functions.addZ.apply (Functions.castNZ.apply (some j)) l)))
      (intervalLength l u) := by
  cases l with
  | none =>
    rw [undefined_term weight _ 0 (by simp [Value.and, Value.mask, Function2.apply, Functions.leZ])]
    simp [rangeValue,intervalLength, Function1.apply, Function2.apply, Functions.floorN, Functions.castQR, Functions.castZQ, Functions.addZ, Functions.mulZ]
  | some l =>
    cases u with
    | none =>
      rw [undefined_term weight _ l (by simp [Value.and, Value.mask, Function2.apply, Functions.leZ, Functions.ltZ])]
      simp [rangeValue,intervalLength, Function1.apply, Function2.apply, Functions.floorN, Functions.castQR, Functions.castZQ, Functions.addZ, Functions.mulZ]
    | some u =>
      rw [intervalLength_some]
      have hp : (fun i : ℤ => Value.mask
        (Value.and (Functions.leZ.apply (some l) (some i)) (Functions.ltZ.apply (some i) (some u))) (f (some i))) =
          (fun i => if l ≤ i ∧ i < u then f (some i) else some 0) := by
        funext i; by_cases hl : l ≤ i <;> by_cases hu : i < u <;>
          simp [Value.mask,Value.and,Function2.apply,Functions.leZ,Functions.ltZ,hl,hu]
      rw [hp,interval_int weight hw]
      simp [rangeValue,Function1.apply,Function2.apply,Functions.castNZ,Functions.addZ]

theorem interval_convertN (weight : α → ℝ) (hw : weight 0 = 0)
    (f : Option ℕ → Option α) (l u : Option ℕ) :
    value weight (some (fun i : ℕ => Value.mask
      (Value.and (Functions.leN.apply l (some i)) (Functions.ltN.apply (some i) u)) (f (some i)))) =
    rangeValue (some (fun j : ℕ => f (Functions.addN.apply (some j) l)))
      (intervalLength (Functions.castNZ.apply l) (Functions.castNZ.apply u)) := by
  cases l with
  | none =>
    rw [undefined_term weight _ 0 (by simp [Value.and, Value.mask, Function2.apply, Functions.leN])]
    simp [rangeValue,intervalLength, Function1.apply, Function2.apply, Functions.floorN, Functions.castNZ, Functions.castQR, Functions.castZQ, Functions.addZ, Functions.mulZ]
  | some l =>
    cases u with
    | none =>
      rw [undefined_term weight _ l (by simp [Value.and, Value.mask, Function2.apply, Functions.leN, Functions.ltN])]
      simp [rangeValue,intervalLength, Function1.apply, Function2.apply, Functions.floorN, Functions.castNZ, Functions.castQR, Functions.castZQ, Functions.addZ, Functions.mulZ]
    | some u =>
      have hc (n : ℕ) : Functions.castNZ.apply (some n) = some (n : ℤ) := by simp [Function1.apply,Functions.castNZ]
      rw [hc,hc,intervalLength_some]
      have he : ((u:ℤ)-(l:ℤ)).toNat = u-l := by omega
      rw [he]
      have hp : (fun i : ℕ => Value.mask
        (Value.and (Functions.leN.apply (some l) (some i)) (Functions.ltN.apply (some i) (some u))) (f (some i))) =
          (fun i => if l ≤ i ∧ i < u then f (some i) else some 0) := by
        funext i; by_cases hl : l ≤ i <;> by_cases hu : i < u <;>
          simp [Value.mask,Value.and,Function2.apply,Functions.leN,Functions.ltN,hl,hu]
      rw [hp,interval_nat weight hw]
      simp [rangeValue,Function2.apply,Functions.addN]

theorem range_convert (weight : α → ℝ) (hw : weight 0 = 0) (f : ℕ → Option α) (n : Option ℕ) :
    value weight (some (fun i => Value.mask (Functions.ltN.apply (some i) n) (f i))) =
      rangeValue (some f) n := by
  cases n with
  | none => exact undefined_term weight _ 0 rfl
  | some n =>
    have h : (fun i => Value.mask (Functions.ltN.apply (some i) (some n)) (f i)) = (fun i => if i < n then f i else some 0) := by
      funext i; by_cases hi : i < n <;> simp [Function2.apply, Functions.ltN, hi, Value.mask]
    rw [h]; exact range_mask weight hw f n

theorem range_zero (f : Option (ℕ → Option α)) (hf : f.isSome) :
    rangeValue f (some 0) = some 0 := by
  cases f with
  | none => simp at hf
  | some f => exact finite_empty f

theorem range_zero_literal (f : Option (ℕ → Option α)) (hf : f.isSome)
    (z : Option α) (hz : z = some 0) : rangeValue f (some 0) = z := by
  rw [hz]; exact range_zero f hf

theorem range_step (f : ℕ → Option α) (n : ℕ)
    (add : Option α → Option α → Option α)
    (ha : ∀ a b, add a b = a.bind (fun a => b.map (fun b => a+b))) :
    rangeValue (some f) (some (n+1)) = add (rangeValue (some f) (some n)) (f n) := by
  exact (range_succ f n).trans (ha _ _).symm

theorem range_solution (f g : ℕ → Option α) (add : Option α → Option α → Option α)
    (ha : ∀ a b, add a b = a.bind (fun a => b.map (fun b => a+b)))
    (hz : g 0 = some 0) (hs : ∀ n, g (n+1) = add (g n) (f n)) (n : Option ℕ) :
    rangeValue (some f) n = n.bind g := by
  cases n with
  | none => rfl
  | some n =>
    change finite (Finset.range n) f = g n
    induction n with
    | zero => exact (finite_empty f).trans hz.symm
    | succ n ih => rw [range_succ, ih, hs, ha]

theorem range_solution_partial (f : ℕ → Option α) (g : Option ℕ → Option α)
    (add : Option α → Option α → Option α)
    (ha : ∀ a b, add a b = a.bind (fun a => b.map (fun b => a+b)))
    (hz : g (some 0) = some 0)
    (hs : ∀ n, g (Functions.addN.apply (some n) (some 1)) = add (g (some n)) (f n))
    (n : Option ℕ) : rangeValue (some f) n = n.bind (fun n => g (some n)) := by
  apply range_solution f (fun n => g (some n)) add ha hz
  intro n
  simpa only [Function2.apply, Functions.addN, Option.bind_some, ite_true] using hs n

theorem finite_map {β : Type} [AddCommMonoid β] (s : Finset ι) (f : ι → Option α)
    (cast : α →+ β) : finite s (fun i => (f i).map cast) = (finite s f).map cast := by
  classical
  have hm : ∀ i, ((f i).map cast).isSome = (f i).isSome := by intro i; cases f i <;> rfl
  unfold finite
  simp_rw [hm]
  split_ifs with h
  · congr 1
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    cases he : f i with
    | none => have := h i hi; simp [he] at this
    | some x => rfl
  · rfl

theorem range_nat_cast (f : Option (ℕ → Option ℕ)) (n : Option ℕ) :
    rangeValue f n = (rangeValue (f.map (fun f i => (f i).map (fun x : ℕ => (x : ℝ)))) n).map Nat.floor := by
  cases f with
  | none => rfl
  | some f =>
    cases n with
    | none => rfl
    | some n =>
      change finite (Finset.range n) f = (finite (Finset.range n) (fun i => (f i).map (Nat.cast : ℕ → ℝ))).map Nat.floor
      have hh := finite_map (Finset.range n) f (Nat.castAddMonoidHom ℝ)
      change finite (Finset.range n) (fun i => (f i).map (fun x : ℕ => (x : ℝ))) = _ at hh
      rw [hh]
      cases finite (Finset.range n) f <;> simp

theorem range_int_cast (f : Option (ℕ → Option ℤ)) (n : Option ℕ) :
    rangeValue f n = (rangeValue (f.map (fun f i => (f i).map (fun x : ℤ => (x : ℝ)))) n).map Int.floor := by
  cases f with
  | none => rfl
  | some f =>
    cases n with
    | none => rfl
    | some n =>
      change finite (Finset.range n) f = (finite (Finset.range n) (fun i => (f i).map (Int.cast : ℤ → ℝ))).map Int.floor
      have hh := finite_map (Finset.range n) f (Int.castAddHom ℝ)
      change finite (Finset.range n) (fun i => (f i).map (fun x : ℤ => (x : ℝ))) = _ at hh
      rw [hh]
      cases finite (Finset.range n) f <;> simp

theorem add (a b : Option α) : Value.add a b = a.bind (fun a => b.map (fun b => a+b)) := by
  cases a <;> cases b <;> rfl
 theorem addN (a b : Option ℕ) : Functions.addN.apply a b = a.bind (fun a => b.map (fun b => a+b)) := by
  cases a <;> cases b <;> simp [Function2.apply, Functions.addN]
 theorem addZ (a b : Option ℤ) : Functions.addZ.apply a b = a.bind (fun a => b.map (fun b => a+b)) := by
  cases a <;> cases b <;> simp [Function2.apply, Functions.addZ]
 theorem addQ (a b : Option ℚ) : Functions.addQ.apply a b = a.bind (fun a => b.map (fun b => a+b)) := by
  cases a <;> cases b <;> simp [Function2.apply, Functions.addQ]

theorem castNat (x : Option ℕ) :
    Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply x)) = x.map (fun n : ℕ => (n : ℝ)) := by
  cases x <;> simp [Function1.apply, Functions.castQR, Functions.castZQ, Functions.castNZ]
theorem castInt (x : Option ℤ) :
    Functions.castQR.apply (Functions.castZQ.apply x) = x.map (fun n : ℤ => (n : ℝ)) := by
  cases x <;> simp [Function1.apply, Functions.castQR, Functions.castZQ]
theorem floorNat (x : Option ℝ) : Functions.floorN.apply x = x.map Nat.floor := by
  cases x <;> simp [Function1.apply, Functions.floorN]
theorem floorInt (x : Option ℝ) : Functions.floorR.apply x = x.map Int.floor := by
  cases x <;> simp [Function1.apply, Functions.floorR]
theorem range_nat_lift (f : Option (ℕ → Option ℕ)) (n : Option ℕ) :
    rangeValue f n = Functions.floorN.apply (rangeValue
      (f.map (fun f i => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply (f i))))) n) := by
  simpa only [castNat, floorNat] using range_nat_cast f n
theorem range_int_lift (f : Option (ℕ → Option ℤ)) (n : Option ℕ) :
    rangeValue f n = Functions.floorR.apply (rangeValue
      (f.map (fun f i => Functions.castQR.apply (Functions.castZQ.apply (f i)))) n) := by
  simpa only [castInt, floorInt] using range_int_cast f n

section Normed
variable {K : Type} [NormedField K]

theorem geometric (q : K) :
    value norm (some (fun n : ℕ => some (q ^ n))) =
      if ‖q‖ < 1 then some ((1-q)⁻¹) else none := by
  classical
  by_cases h : ‖q‖ < 1
  · rw [if_pos h]
    apply of_hasSum _ _ _ _ (fun _ => rfl)
    · simpa only [norm_pow] using summable_geometric_of_norm_lt_one (by simpa using h : ‖‖q‖‖ < 1)
    · exact hasSum_geometric_of_norm_lt_one h
  · have hn : ¬ Summable (fun n : ℕ => q ^ n) := by simpa [summable_geometric_iff_norm_lt_one] using h
    simp [value, h, hn]

end Normed
theorem geometric_partial {K : Type} [NormedField K] (q : Option K) :
    value norm (some (fun n : ℕ => q.map (fun q => q^n))) =
      Binding.guardValue (Value.lt (q.map norm) (some 1))
        (Value.inv (Value.add (some 1) (Value.mul (some (-1)) q))) := by
  classical
  cases q with
  | none => exact undefined_term _ _ 0 rfl
  | some q =>
    change value norm (some (fun n : ℕ => some (q^n))) = Binding.guardValue (Value.lt (some ‖q‖) (some 1)) (Value.inv (Value.add (some 1) (Value.mul (some (-1)) (some q))))
    rw [geometric]
    by_cases h : ‖q‖ < 1
    · have hq : q ≠ 1 := by intro he; simp [he] at h
      simp [Binding.guardValue, Value.lt, Value.inv, Value.add, Value.mul, h, ← sub_eq_add_neg, sub_ne_zero.mpr (Ne.symm hq)]
    · simp [Binding.guardValue, Value.lt, h]

theorem geometricR (q : Option ℝ) :
    value norm (some (fun n : ℕ => Functions.powRN.apply q (some n))) =
      Binding.guardValue (Value.lt (Value.abs q) (some 1))
        (Value.inv (Value.add (some 1) (Value.mul (some (-1)) q))) := by
  simpa [Function2.apply, Functions.powRN, Value.abs, Real.norm_eq_abs, Option.map_eq_bind] using geometric_partial q

theorem geometricC (q : Option ℂ) :
    value norm (some (fun n : ℕ => Functions.powCN.apply q (some n))) =
      Binding.guardValue (Value.lt (Functions.absC.apply q) (some 1))
        (Value.inv (Value.add (some 1) (Value.mul (some (-1)) q))) := by
  simpa [Function2.apply, Function1.apply, Functions.powCN, Functions.absC, Option.map_eq_bind] using geometric_partial q

theorem geometricQ (q : Option ℚ) :
    value norm (some (fun n : ℕ => Functions.powQN.apply q (some n))) =
      Binding.guardValue (Value.lt (Value.abs (Functions.castQR.apply q)) (some 1))
        (Functions.invQ.apply (Functions.addQ.apply (some 1) (Functions.mulQ.apply (some (-1)) q))) := by
  have hn : Value.abs (Functions.castQR.apply q) = q.map norm := by
    cases q <;> simp [Value.abs, Function1.apply, Functions.castQR, ← Real.norm_eq_abs, Rat.norm_cast_real]
  rw [hn]
  have h := geometric_partial q
  cases q with
  | none => exact h
  | some q =>
    by_cases hz : 1 + -q = 0 <;> simpa [hz, Function2.apply, Function1.apply, Functions.powQN, Functions.invQ, Functions.addQ, Functions.mulQ,
    Value.inv, Value.add, Value.mul, Option.map_eq_bind] using h

theorem geometricR_literals (q one minus : Option ℝ) (ho : one = some 1) (hm : minus = some (-1)) :
    value norm (some (fun n : ℕ => Functions.powRN.apply q (some n))) =
      Binding.guardValue (Value.lt (Value.abs q) one)
        (Value.inv (Value.add one (Value.mul minus q))) := by
  rw [ho, hm]; exact geometricR q

theorem geometricC_literals (q one minus : Option ℂ) (rOne : Option ℝ)
    (ho : one = some 1) (hm : minus = some (-1)) (hr : rOne = some 1) :
    value norm (some (fun n : ℕ => Functions.powCN.apply q (some n))) =
      Binding.guardValue (Value.lt (Functions.absC.apply q) rOne)
        (Value.inv (Value.add one (Value.mul minus q))) := by
  rw [ho, hm, hr]; exact geometricC q

theorem geometricQ_literals (q one minus : Option ℚ) (rOne : Option ℝ)
    (ho : one = some 1) (hm : minus = some (-1)) (hr : rOne = some 1) :
    value norm (some (fun n : ℕ => Functions.powQN.apply q (some n))) =
      Binding.guardValue (Value.lt (Value.abs (Functions.castQR.apply q)) rOne)
        (Functions.invQ.apply (Functions.addQ.apply one (Functions.mulQ.apply minus q))) := by
  rw [ho, hm, hr]; exact geometricQ q

theorem constant [Infinite ι] [Nonempty ι] (weight : α → ℝ) (hw : weight 0 = 0)
    (hfaithful : ∀ x, weight x = 0 ↔ x = 0) (c : Option α) :
    value weight (some (fun _ : ι => c)) =
      Binding.guardValue (c.map (fun c => decide (c=0))) (some 0) := by
  cases c with
  | none => exact undefined_term weight _ (Classical.choice ‹Nonempty ι›) rfl
  | some c =>
    by_cases hc : c = 0
    · subst c; simpa [Binding.guardValue] using (zero (ι := ι) weight hw)
    · have hn : ¬ Summable (fun _ : ι => weight c) := by
        rw [summable_const_iff]; exact fun h => hc ((hfaithful c).mp h)
      simp [value, hn, Binding.guardValue, hc]

theorem constantN [Infinite ι] [Nonempty ι] (c z : Option ℕ) (hz : z = some 0) :
    value (fun n : ℕ => (n : ℝ)) (some (fun _ : ι => c)) =
      Binding.guardValue (Value.not (Functions.nonzeroN.apply c)) z := by
  rw [hz]
  have h := constant (ι := ι) (fun n : ℕ => (n : ℝ)) (by simp) (by intro n; simp) c
  cases c with
  | none => exact h
  | some c => by_cases hc : c = 0 <;> simpa [Function1.apply, Functions.nonzeroN, Value.not, hc] using h

theorem constantZ [Infinite ι] [Nonempty ι] (c z : Option ℤ) (hz : z = some 0) :
    value norm (some (fun _ : ι => c)) =
      Binding.guardValue (Value.not (Functions.nonzeroZ.apply c)) z := by
  rw [hz]
  have h := constant (ι := ι) norm norm_zero (fun _ => norm_eq_zero) c
  cases c with
  | none => exact h
  | some c => by_cases hc : c = 0 <;> simpa [Function1.apply, Functions.nonzeroZ, Value.not, hc] using h

theorem constantQ [Infinite ι] [Nonempty ι] (c z : Option ℚ) (hz : z = some 0) :
    value norm (some (fun _ : ι => c)) =
      Binding.guardValue (Value.not (Functions.nonzeroQ.apply c)) z := by
  rw [hz]
  have h := constant (ι := ι) norm norm_zero (fun _ => norm_eq_zero) c
  cases c with
  | none => exact h
  | some c => by_cases hc : c = 0 <;> simpa [Function1.apply, Functions.nonzeroQ, Value.not, hc] using h

theorem constant_norm {K : Type} [NormedAddCommGroup K] [Infinite ι] [Nonempty ι] (c z : Option K) (hz : z = some 0) :
    value norm (some (fun _ : ι => c)) =
      Binding.guardValue (Value.not (Value.nonzero c)) z := by
  rw [hz]
  have h := constant (ι := ι) norm norm_zero (fun _ => norm_eq_zero) c
  cases c <;> simpa [Value.nonzero, Value.not] using h

theorem nat_weight_zero : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero

theorem norm_ltR (q : Option ℝ) (v : ℝ) (one : Option ℝ)
    (hq : q = some v) (ho : one = some 1)
    (h : Value.lt (Value.abs q) one = some true) : ‖v‖ < 1 := by
  rw [hq,ho] at h
  simpa [Value.lt,Value.abs,Real.norm_eq_abs] using h

theorem norm_ltQ (q : Option ℚ) (v : ℚ) (one : Option ℝ)
    (hq : q = some v) (ho : one = some 1)
    (h : Value.lt (Value.abs (Functions.castQR.apply q)) one = some true) : ‖v‖ < 1 := by
  rw [hq,ho] at h
  simpa [Value.lt,Value.abs,Function1.apply,Functions.castQR,← Real.norm_eq_abs,Rat.norm_cast_real] using h

theorem norm_ltC (q : Option ℂ) (v : ℂ) (one : Option ℝ)
    (hq : q = some v) (ho : one = some 1)
    (h : Value.lt (Functions.absC.apply q) one = some true) : ‖v‖ < 1 := by
  rw [hq,ho] at h
  simpa [Value.lt,Function1.apply,Functions.absC] using h

theorem rational_zero_of_real (x : Option ℚ) (h : Functions.castQR.apply x = some 0) : x = some 0 := by
  cases x with
  | none => simp [Function1.apply,Functions.castQR] at h
  | some x =>
    simp only [Function1.apply,Functions.castQR,Option.some_bind,ite_true,Option.some.injEq] at h ⊢
    exact_mod_cast h

section Tail
variable {K : Type} [NormedField K]

/-- An explicit absolutely summable polynomial-geometric tail. -/
inductive Tail (K : Type) where
  | nil
  | cons (coefficient ratio : K) (degree : ℕ) (rest : Tail K)

noncomputable def Tail.eval : Tail K → ℕ → K
  | .nil, _ => 0
  | .cons c q k rest, n => c * (n : K)^k * q^n + rest.eval n

def Tail.converges : Tail K → Prop
  | .nil => True
  | .cons _ q _ rest => ‖q‖ < 1 ∧ rest.converges

theorem Tail.cons_value
    (add mul : Option K → Option K → Option K) (pow : Option K → Option ℕ → Option K)
    (cast : Option ℕ → Option K)
    (ha : add = Value.add) (hm : mul = Value.mul) (hp : pow = Spectral.power)
    (hcast : cast = RepeatedSpectra.natCast)
    (c q rest : Option K) (cv qv rv : K)
    (hc : c = some cv) (hq : q = some qv) (hr : rest = some rv) (k n : ℕ) :
    add (mul (mul c (pow (cast (some n)) (some k))) (pow q (some n))) rest =
      some (cv * (n : K)^k * qv^n + rv) := by
  rw [ha, hm, hp, hcast, hc, hq, hr]
  rfl

theorem Tail.summable (t : Tail K) (h : t.converges) : Summable t.eval := by
  induction t with
  | nil => exact summable_zero
  | cons c q k rest ih =>
    exact ((summable_pow_mul_geometric_of_norm_lt_one k h.1).mul_left c).congr
      (fun n => by simp [mul_assoc]) |>.add (ih h.2)

theorem Tail.summable_norm (t : Tail K) (h : t.converges) : Summable (fun n => ‖t.eval n‖) := by
  induction t with
  | nil => simpa [Tail.eval] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  | cons c q k rest ih =>
    have hm : Summable (fun n : ℕ => ‖c * (n : K)^k * q^n‖) := by
      simpa [norm_mul, norm_pow, mul_assoc] using
        (summable_norm_pow_mul_geometric_of_norm_lt_one k h.1).mul_left ‖c‖
    exact (hm.add (ih h.2)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)

theorem telescope (f : ℕ → Option K) (g : ℕ → K)
    (hs : Summable g) (ha : Summable (fun n => ‖g n‖))
    (h : ∀ n, f n = some (g (n+1) - g n)) : value norm (some f) = some (-g 0) := by
  have hshift : Summable (fun n => g (n+1)) := (summable_nat_add_iff 1).2 hs
  have hashift : Summable (fun n => ‖g (n+1)‖) := (summable_nat_add_iff 1).2 ha
  have he : (∑' n, g (n+1)) - ∑' n, g n = -g 0 := by
    have hh := hs.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at hh
    linear_combination hh
  apply of_hasSum norm f (fun n => g (n+1)-g n) (-g 0) h
  · exact (hashift.add ha).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
  · exact he ▸ (hshift.hasSum.sub hs.hasSum)

theorem mul_eq (mul : Option K → Option K → Option K) (hm : mul = Value.mul) (a b : Option K) :
    mul a b = a.bind (fun a => b.map (fun b => a*b)) := by
  rw [hm]; cases a <;> cases b <;> rfl

theorem tail_solution (f : ℕ → Option K) (g : Option ℕ → Option K) (t : Tail K)
    (hc : t.converges) (hg : ∀ n, g (some n) = some (t.eval n))
    (add mul : Option K → Option K → Option K)
    (ha : ∀ a b, add a b = a.bind (fun a => b.map (fun b => a+b)))
    (hm : ∀ a b, mul a b = a.bind (fun a => b.map (fun b => a*b)))
    (minus : Option K) (hn : minus = some (-1))
    (hstep : ∀ n, g (Functions.addN.apply (some n) (some 1)) = add (g (some n)) (f n)) :
    value norm (some f) = mul minus (g (some 0)) := by
  have hf : ∀ n, f n = some (t.eval (n+1) - t.eval n) := by
    intro n
    have hh := hstep n
    have hadd : Functions.addN.apply (some n) (some 1) = some (n+1) := by simp [Function2.apply, Functions.addN]
    rw [hadd] at hh
    rw [hg, hg, ha] at hh
    cases he : f n with
    | none => simp [he] at hh
    | some x =>
      have hmath : t.eval (n+1) = t.eval n + x := by simpa [he] using hh
      rw [show t.eval (n+1) - t.eval n = x by rw [hmath]; abel]
  rw [telescope f t.eval (t.summable hc) (t.summable_norm hc) hf, hm, hn, hg]
  simp

end Tail

theorem nonzeroQ : Functions.nonzeroQ.apply = Value.nonzero := by
  funext q; cases q <;> simp [Function1.apply,Functions.nonzeroQ,Value.nonzero]

section FiniteGeometric
variable {K : Type} [NormedField K]

theorem range_geometric_value
    (add mul : Option K → Option K → Option K) (inv : Option K → Option K)
    (pow : Option K → Option ℕ → Option K) (cast : Option ℕ → Option K)
    (nz : Option K → Option Bool) (hnz : nz = Value.nonzero)
    (ha : add = Value.add) (hm : mul = Value.mul) (hi : inv = Value.inv)
    (hp : pow = Spectral.power) (hc : cast = RepeatedSpectra.natCast)
    (zero minus : Option K) (hz : zero = some 0) (hn : minus = some (-1))
    (q : Option K) (n : Option ℕ) :
    rangeValue (some (fun i => pow q (some i))) n =
      add (Value.mask (Value.not (Functions.nonzeroN.apply n)) zero)
        (Value.mask (Functions.nonzeroN.apply n)
          (add (Value.mask (Value.not (nz (add q minus))) (cast n))
            (Value.mask (nz (add q minus)) (mul (add (pow q n) minus) (inv (add q minus)))))) := by
  rw [hnz,ha,hm,hi,hp,hc,hz,hn]
  cases n with
  | none => simp [rangeValue,Value.add,Value.mask,Value.not,Function1.apply,Functions.nonzeroN]
  | some n =>
    cases n with
    | zero => simp [rangeValue,finite,Value.add,Value.mask,Value.not,Function1.apply,Functions.nonzeroN]
    | succ n =>
      cases q with
      | none =>
        have hf : ¬ ∀ i ∈ Finset.range (n+1), (Spectral.power (none : Option K) (some i)).isSome := by
          intro h; have hh := h 0 (by simp); simp [Spectral.power] at hh
        simp [rangeValue,finite,hf,Spectral.power,Value.add,Value.mul,Value.mask,Value.not,Value.nonzero,Function1.apply,Functions.nonzeroN]
        exact ⟨0,Nat.zero_lt_succ n⟩
      | some q =>
        by_cases hq : q = 1
        · subst q
          simp [rangeValue,finite,Spectral.power,RepeatedSpectra.natCast,Value.add,Value.mul,Value.inv,Value.mask,Value.not,Value.nonzero,Function1.apply,Functions.nonzeroN]
        · have hd : q + -1 ≠ 0 := by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hq
          simp [rangeValue,finite,Spectral.power,RepeatedSpectra.natCast,Value.add,Value.mul,Value.inv,Value.mask,Value.not,Value.nonzero,Function1.apply,Functions.nonzeroN,hd,geom_sum_eq hq,div_eq_mul_inv,sub_eq_add_neg]

end FiniteGeometric

section Recurrence
variable (add : Option α → Option α → Option α)
variable (ha : ∀ a b, add a b = a.bind (fun a => b.map (fun b => a+b)))
include ha

theorem add_assoc (a b c : Option α) : add a (add b c) = add (add a b) c := by
  simp only [ha]; cases a <;> cases b <;> cases c <;> simp [_root_.add_assoc]

theorem add_comm (a b : Option α) : add a b = add b a := by
  simp only [ha]; cases a <;> cases b <;> simp [_root_.add_comm]

noncomputable def prefixStep (reverse : Bool) (a : Option α) (h : Option ℕ → Option α)
    (g : ℕ → Option α) (n : ℕ) : Option α :=
  let p := Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))
  let prev := (Functions.subN.apply (some n) (some 1)).bind g
  add (Value.mask p a) (Value.mask (Value.not p)
    (if reverse then add (h (some n)) prev else add prev (h (some n))))

theorem prefixStep_zero (reverse : Bool) (a : Option α) (h : Option ℕ → Option α) (g : ℕ → Option α) :
    prefixStep add reverse a h g 0 = a := by
  simp [prefixStep,Function1.apply,Functions.castNZ,Functions.nonzeroZ,Value.not,Value.mask,ha]

theorem prefixStep_succ (reverse : Bool) (a : Option α) (h : Option ℕ → Option α) (g : ℕ → Option α) (n : ℕ) :
    prefixStep add reverse a h g (n+1) = add (g n) (h (Functions.addN.apply (some n) (some 1))) := by
  have ht : Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some (n+1)))) = some false := by
    have hn : (↑n + 1 : ℤ) ≠ 0 := by omega
    simp [Function1.apply, Functions.nonzeroZ, Functions.castNZ, Value.not, hn]
  have hp : Functions.subN.apply (some (n+1)) (some 1) = some n := by simp [Function2.apply,Functions.subN]
  unfold prefixStep
  rw [ht,hp,Recursion.nat_successor]
  simp only [Option.bind_some,Value.not,Value.mask,Bool.not_false]
  have hz (x : Option α) : add (some 0) x = x := by cases x <;> simp [ha]
  rw [hz]
  cases reverse
  · rfl
  · exact add_comm add ha _ _

theorem solve_prefix (p : Recursion.Program ℕ α α) (reverse : Bool) (a : Option α) (h : Option ℕ → Option α)
    (hp : ∀ g n, p.eval g n = prefixStep add reverse a h g n) :
    FixedPoint.value p.functional = fun n => add a
      (rangeValue (some (fun i => h (Functions.addN.apply (some i) (some 1)))) (some n)) := by
  funext n
  induction n with
  | zero =>
    rw [← p.unfold 0,hp,prefixStep_zero add ha]
    change a = add a (finite (Finset.range 0) _)
    rw [Finset.range_zero,finite_empty]
    cases a <;> simp [ha]
  | succ n ih =>
    rw [← p.unfold (n+1),hp,prefixStep_succ add ha,ih,range_step _ n add ha,add_assoc add ha]

end Recurrence

end QSym.Summation
