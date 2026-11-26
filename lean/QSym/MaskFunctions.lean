import QSym.Functions

namespace QSym

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
