import QSym.Functions
import QSym.Binding
import QSym.Domain

namespace QSym

/-- A strict observation of a guarded input uses exactly the same guard. -/
theorem Binding.map_guard_of_strict {α β : Type} (o : Option α → Option β) (hn : o none = none)
    (p : Option Bool) (x : Option α) : o (guardValue p x) = guardValue p (o x) := by
  unfold guardValue
  split <;> simp_all

/-- Two strict factors whose product refines one can be removed on its
certified domain, even when the intervening observation is missing. -/
theorem Value.mul_pair_one (a b x one : Option ℝ) (p : Option Bool) (outerLeft innerLeft : Bool)
    (hd : Domain.Correct (Value.mul a b) p) (h : Value.Refines (Value.mul a b) one)
    (h1 : one = some 1) :
    (let t := if innerLeft then Value.mul b x else Value.mul x b
     if outerLeft then Value.mul a t else Value.mul t a) = (if p == some true then x else none) := by
  subst one
  rw [hd]
  have assoc : (let t := if innerLeft then Value.mul b x else Value.mul x b
      if outerLeft then Value.mul a t else Value.mul t a) = Value.mul (Value.mul a b) x := by
    cases a <;> cases b <;> cases x <;> cases outerLeft <;> cases innerLeft <;>
      simp [Value.mul, mul_comm, mul_left_comm, mul_assoc]
  rw [assoc]
  cases hv : Value.mul a b with
  | none => rfl
  | some v =>
    have he := Option.some.inj (h v hv)
    rw [← he]
    exact Value.mul_one_left x

/-- Outside zero, a defined test leaves its operand untouched. At zero
and at a missing test, check the partial scalar context itself. -/
theorem Value.mask_nonzero_context {β : Type} [Zero β] (f : Option ℝ → Option β)
    (z : Option ℝ) (hz : z = some 0) (h0 : f z = some 0)
    (hm : Domain.Correct (f (Value.inv z)) (some false)) (u : Option ℝ) :
    Value.mask (Value.nonzero u) (f u) = f u := by
  classical
  subst z
  have inv : Value.inv (some (0 : ℝ)) = none := by simp [Value.inv]
  rw [inv] at hm
  cases u with
  | none => cases he : f none <;> simp_all [Domain.Correct, Value.nonzero, Value.mask]
  | some x =>
    by_cases hx : x = 0
    · subst x; simp [Value.nonzero, Value.mask, h0]
    · simp [Value.nonzero, Value.mask, hx]

/-- Removing a puncture is pointwise sound when the masked value is
defined and zero at that point. Its value elsewhere may be partial. -/
theorem Value.mask_nonzero_of_zero {α β : Type} [Zero α] [Zero β]
    (p : Option α → Option Bool) (hp : p = Value.nonzero)
    (f : Option α → Option β) (z : Option α) (hz : z = some 0)
    (hf : f z = some 0) (x : α) :
    Value.mask (p (some x)) (f (some x)) = f (some x) := by
  classical
  subst p
  subst z
  by_cases h : x = 0
  · subst x
    simp [Value.nonzero, Value.mask, hf]
  · simp [Value.nonzero, Value.mask, h]

theorem Functions.nonzeroN_eq : nonzeroN.apply = Value.nonzero := by
  funext x
  cases x <;> simp [nonzeroN, Function1.apply, Value.nonzero]

theorem Functions.nonzeroZ_eq : nonzeroZ.apply = Value.nonzero := by
  funext x
  cases x <;> simp [nonzeroZ, Function1.apply, Value.nonzero]

theorem Functions.nonzeroCastNZ_eq :
    (fun x => nonzeroZ.apply (castNZ.apply x)) = Value.nonzero := by
  funext x
  cases x <;> simp [nonzeroZ, castNZ, Function1.apply, Value.nonzero]

theorem Value.mask_and_of_right {β : Type} [Zero β] (p : Option Bool)
    {q : Option Bool} {v : Option β} (h : Value.mask q v = v) :
    Value.mask (Value.and p q) v = Value.mask p v := by
  cases p with
  | none => rfl
  | some p => cases p <;> first | rfl | exact h

theorem Value.mask_and_congr_right {β : Type} [Zero β] (p : Option Bool)
    {q r : Option Bool} {v : Option β} (h : Value.mask q v = Value.mask r v) :
    Value.mask (Value.and p q) v = Value.mask (Value.and p r) v := by
  cases p with
  | none => rfl
  | some p => cases p <;> first | rfl | exact h

theorem Function1.apply_mask {α β : Type} [Zero α] [Zero β] (f : Function1 α β)
    (p : Option Bool) (x : Option α) (hd : f.domain 0) (hz : f.value 0 = 0) :
    f.apply (Value.mask p x) = Value.mask p (f.apply x) := by
  cases p with
  | none => rfl
  | some p => cases p <;> simp [Function1.apply, Value.mask, hd, hz]

theorem Functions.sin_mask (p : Option Bool) (x : Option ℝ) :
    sinR.apply (Value.mask p x) = Value.mask p (sinR.apply x) :=
  Function1.apply_mask _ p x (by simp [sinR]) (by simp [sinR])

theorem Functions.sinh_mask (p : Option Bool) (x : Option ℝ) :
    sinhR.apply (Value.mask p x) = Value.mask p (sinhR.apply x) :=
  Function1.apply_mask _ p x (by simp [sinhR]) (by simp [sinhR])

theorem Functions.tanh_mask (p : Option Bool) (x : Option ℝ) :
    tanhR.apply (Value.mask p x) = Value.mask p (tanhR.apply x) :=
  Function1.apply_mask _ p x (by simp [tanhR]) (by simp [tanhR])

theorem Functions.atan_mask (p : Option Bool) (x : Option ℝ) :
    atanR.apply (Value.mask p x) = Value.mask p (atanR.apply x) :=
  Function1.apply_mask _ p x (by simp [atanR]) (by simp [atanR])

theorem Functions.asin_mask (p : Option Bool) (x : Option ℝ) :
    asinR.apply (Value.mask p x) = Value.mask p (asinR.apply x) :=
  Function1.apply_mask _ p x (by simp [asinR]) (by simp [asinR])

end QSym
