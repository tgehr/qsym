import QSym.Functions

namespace QSym

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
