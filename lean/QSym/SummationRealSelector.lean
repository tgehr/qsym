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

end QSym.Summation
