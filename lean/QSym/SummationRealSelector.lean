import QSym.Summation

/-! A real-valued index with a left inverse selects at most one summand.
The mask remains lazy in its weight, including when the query falls between
indices. -/
noncomputable section
namespace QSym.Summation
open Function
attribute [local instance] Classical.propDecidable

def realMatch (x y : Option ℝ) : Option Bool :=
  Value.not (Value.nonzero (Value.add x (Value.mul (some ((-1 : ℤ) : ℝ)) y)))

private theorem realMatch_some (x y : ℝ) : realMatch (some x) (some y) = some (decide (x = y)) := by
  by_cases h : x=y <;> simp [realMatch, Value.mul, Value.add, Value.nonzero, Value.not, ← sub_eq_add_neg, sub_eq_zero, h]

private theorem realMatch_comm (x y : Option ℝ) : realMatch x y = realMatch y x := by
  cases x <;> cases y <;> first | rfl | simp [realMatch_some, eq_comm]

variable {α ι : Type} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]

theorem select_real_index [Inhabited ι] [DecidableEq ι] (weight : α → ℝ) (hw : weight 0 = 0)
    (encode : ι → ℝ) (recover : ℝ → ι) (left : LeftInverse recover encode)
    (swap : Bool) (f : ι → Option α) (x : Option ℝ) :
    value weight (some (fun i => Value.mask
      (if swap then realMatch (some (encode i)) x else realMatch x (some (encode i))) (f i))) =
    Value.mask (realMatch x (x.map (fun v => encode (recover v)))) ((x.map recover).bind f) := by
  have dir (i : ι) : (if swap then realMatch (some (encode i)) x else realMatch x (some (encode i))) =
      realMatch x (some (encode i)) := by cases swap <;> simp [realMatch_comm (some (encode i)) x]
  simp only [dir]
  cases x with
  | none => exact undefined_term weight _ default rfl
  | some x =>
    change value weight (some (fun i => Value.mask (realMatch (some x) (some (encode i))) (f i))) =
      Value.mask (realMatch (some x) (some (encode (recover x)))) (f (recover x))
    simp only [realMatch_some]
    by_cases hit : x = encode (recover x)
    · have at_index (i : ι) : x = encode i ↔ i = recover x := by
        constructor
        · rintro rfl; exact (left i).symm
        · rintro rfl; exact hit
      have hm (i : ι) : Value.mask (some (decide (x = encode i))) (f i) =
          (if i = recover x then f i else some 0) := by
        by_cases hi : i = recover x <;> simp [at_index, hi, Value.mask]
      simp_rw [hm]
      simpa only [if_true] using delta_select weight hw (recover x) f
    · have miss (i : ι) : x ≠ encode i := by rintro rfl; exact hit (congrArg encode (left i)).symm
      simpa only [decide_eq_false (miss _), decide_eq_false hit, Value.mask] using (zero (ι := ι) weight hw)

abbrev realIndexZ (i : Option ℤ) := Functions.castQR.apply (Functions.castZQ.apply i)
abbrev realIndexN (i : Option ℕ) := realIndexZ (Functions.castNZ.apply i)

private theorem realIndexZ_map (i : Option ℤ) : realIndexZ i = i.map (fun j : ℤ => (j : ℝ)) := by
  cases i <;> simp [realIndexZ, Function1.apply, Functions.castZQ, Functions.castQR]

private theorem realIndexN_map (i : Option ℕ) : realIndexN i = i.map (fun j : ℕ => (j : ℝ)) := by
  cases i <;> simp [realIndexN, realIndexZ_map, Function1.apply, Functions.castNZ]

theorem select_real_Z (weight : α → ℝ) (hw : weight 0 = 0) (swap : Bool) (f : ℤ → Option α) (x : Option ℝ) :
    value weight (some (fun i => Value.mask
      (if swap then realMatch (realIndexZ (some i)) x else realMatch x (realIndexZ (some i))) (f i))) =
      Value.mask (realMatch x (realIndexZ (Functions.floorR.apply x))) ((Functions.floorR.apply x).bind f) := by
  simpa only [realIndexZ_map, floorInt, Option.map_some, Option.map_map, Function.comp_def] using
    select_real_index weight hw ((↑) : ℤ → ℝ) Int.floor Int.floor_intCast swap f x

theorem select_real_N (weight : α → ℝ) (hw : weight 0 = 0) (swap : Bool) (f : ℕ → Option α) (x : Option ℝ) :
    value weight (some (fun i => Value.mask
      (if swap then realMatch (realIndexN (some i)) x else realMatch x (realIndexN (some i))) (f i))) =
      Value.mask (realMatch x (realIndexN (Functions.floorN.apply x))) ((Functions.floorN.apply x).bind f) := by
  simpa only [realIndexN_map, floorNat, Option.map_some, Option.map_map, Function.comp_def] using
    select_real_index weight hw ((↑) : ℕ → ℝ) Nat.floor Nat.floor_natCast swap f x

/-- A finite range probes the recovered index only when it belongs to the range.
An empty range also skips a missing query. -/
theorem range_real_index (encode : ℕ → ℝ) (recover : ℝ → ℕ) (left : LeftInverse recover encode)
    (swap : Bool) (f : ℕ → Option α) (x : Option ℝ) (n : Option ℕ) :
    rangeValue (some (fun i => Value.mask
      (if swap then realMatch (some (encode i)) x else realMatch x (some (encode i))) (f i))) n =
      Value.mask (Functions.nonzeroN.apply n) (Value.mask (Functions.ltN.apply (x.map recover) n)
        (Value.mask (realMatch x ((x.map recover).map encode)) ((x.map recover).bind f))) := by
  cases n with
  | none => rfl
  | some n =>
    cases n with
    | zero => simp [rangeValue, finite_empty, Functions.nonzeroN, Function1.apply, Value.mask]
    | succ n =>
      cases x with
      | none =>
        change finite (Finset.range (n+1)) _ = _
        rw [range_succ]
        generalize finite (α := α) (Finset.range n) _ = prev
        cases swap <;> cases prev <;>
          simp [Functions.nonzeroN, Functions.ltN, Function1.apply, Function2.apply, realMatch, Value.mask, Value.nonzero, Value.add, Value.mul, Value.not]
      | some x =>
        let pred (i : ℕ) := if swap then realMatch (some (encode i)) (some x) else realMatch (some x) (some (encode i))
        have mask (i : ℕ) : (if i < n+1 then Value.mask (pred i) (f i) else some 0) =
            Value.mask (pred i) (if i < n+1 then f i else some 0) := by
          by_cases hi : i < n+1
          · simp [hi]
          · by_cases hit : x = encode i <;> cases swap <;> simp_all [pred, realMatch_some, Value.mask, eq_comm]
        change finite (Finset.range (n+1)) (fun i => Value.mask (pred i) (f i)) = _
        rw [← range_mask (fun _ => 0) rfl]
        simp_rw [mask]
        have sel := select_real_index (fun _ : α => 0) rfl encode recover left swap
          (fun i => if i < n+1 then f i else some 0) (some x)
        refine sel.trans ?_
        by_cases hi : recover x < n+1 <;>
          simp [Functions.nonzeroN, Functions.ltN, Function1.apply, Function2.apply, Value.mask, realMatch_some, hi] <;>
          cases decide (x = encode (recover x)) <;> rfl

theorem range_real_N (swap : Bool) (f : ℕ → Option α) (x : Option ℝ) (n : Option ℕ) :
    rangeValue (some (fun i => Value.mask
      (if swap then realMatch (realIndexN (some i)) x else realMatch x (realIndexN (some i))) (f i))) n =
      (let j := Functions.floorN.apply x
       Value.mask (Functions.nonzeroN.apply n) (Value.mask (Functions.ltN.apply j n)
         (Value.mask (realMatch x (realIndexN j)) (j.bind f)))) := by
  simpa only [realIndexN_map, floorNat, Option.map_some] using
    range_real_index ((↑) : ℕ → ℝ) Nat.floor Nat.floor_natCast swap f x n

private def shiftedIndex (offFirst : Bool) (off i : Option ℕ) :=
  if offFirst then Functions.addN.apply off i else Functions.addN.apply i off

theorem range_shifted_real_N (swap offFirst : Bool) (f : ℕ → Option α) (x : Option ℝ) (off n : Option ℕ) :
    rangeValue (some (fun i => Value.mask
      (let z := realIndexN (shiftedIndex offFirst off (some i))
       if swap then realMatch z x else realMatch x z) (f i))) n =
      (let j := Functions.floorN.apply (Value.add x (Value.mul (some ((-1 : ℤ) : ℝ)) (realIndexN off)))
       Value.mask (Functions.nonzeroN.apply n) (Value.mask (Functions.ltN.apply j n)
         (Value.mask (realMatch x (realIndexN (shiftedIndex offFirst off j))) (j.bind f)))) := by
  rcases off with _ | o
  · rcases n with _ | n
    · rfl
    · cases n with
      | zero => simp [rangeValue, finite_empty, Functions.nonzeroN, Function1.apply, Value.mask]
      | succ n =>
        change finite (Finset.range (n+1)) _ = _
        rw [range_succ]
        generalize finite (α := α) (Finset.range n) _ = prev
        cases swap <;> cases offFirst <;> cases x <;> cases prev <;>
          simp [shiftedIndex, floorNat, realIndexN_map, Functions.addN, Functions.nonzeroN, Functions.ltN, Function1.apply,
            Function2.apply, Value.mask, realMatch, Value.add, Value.mul, Value.not, Value.nonzero]
  · let recover (x : ℝ) := ⌊x - (o : ℝ)⌋₊
    have left : LeftInverse recover (fun i : ℕ => ((i+o : ℕ) : ℝ)) := by
      intro i
      change ⌊((i+o : ℕ) : ℝ) - o⌋₊ = i
      rw [Nat.cast_add, add_sub_cancel_right, Nat.floor_natCast]
    have shift (i : Option ℕ) : realIndexN (shiftedIndex offFirst (some o) i) = i.map (fun j : ℕ => ((j+o : ℕ) : ℝ)) := by
      cases i <;> cases offFirst <;> simp [realIndexN_map, shiftedIndex, Functions.addN, Function2.apply, Nat.add_comm]
    have inv : Functions.floorN.apply (Value.add x (Value.mul (some ((-1 : ℤ) : ℝ)) (realIndexN (some o)))) = x.map recover := by
      cases x <;> simp [floorNat, realIndexN_map, Value.add, Value.mul, recover, sub_eq_add_neg]
    simpa only [shift, inv, Option.map_some] using
      range_real_index (fun i : ℕ => ((i+o : ℕ) : ℝ)) recover left swap f x n

/-- Moving an independent addend to the other side of a real equality also
preserves missing inputs and the laziness of the masked weight. -/
theorem mask_addend {β : Type} [Zero β] (first : Bool) (i c : Option ℝ) (v : Option β) :
    Value.mask (Value.not (Value.nonzero (if first then Value.add c i else Value.add i c))) v =
      Value.mask (realMatch i (Value.mul (some ((-1 : ℤ) : ℝ)) c)) v := by
  cases first <;> cases i <;> cases c <;> simp [realMatch, Value.add, Value.mul, _root_.add_comm]

end QSym.Summation
