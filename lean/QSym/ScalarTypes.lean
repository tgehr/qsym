import QSym.PowerPredicates
import Mathlib.Data.Rat.Floor

namespace QSym.ScalarTypes

theorem rational_integer (q : ℚ) : (q : ℝ)=(⌊(q : ℝ)⌋ : ℤ) ↔ q.den=1 := by
  rw [PowerPredicates.integer_iff]
  constructor
  · rintro ⟨k, h⟩
    have hq : q=(k : ℚ) := by exact_mod_cast h
    simp [hq]
  · intro h
    refine ⟨q.num, ?_⟩
    exact_mod_cast ((Rat.den_eq_one_iff q).mp h).symm

theorem rational_integer_cast (q : ℚ) : (q : ℝ)=(⌊q⌋ : ℤ) ↔ q.den=1 := by
  simpa only [Rat.floor_cast] using rational_integer q

theorem even_int (k : ℤ) : Even k ↔ ((k : ℚ)/2).den=1 := by
  rw [← rational_integer, PowerPredicates.even_iff]
  push_cast
  rfl

theorem odd_int (k : ℤ) : Odd k ↔ (((k : ℚ)-1)/2).den=1 := by
  rw [← rational_integer, PowerPredicates.odd_iff]
  push_cast
  rfl

theorem even_nat (n : ℕ) : Even n ↔ ((n : ℚ)/2).den=1 := by
  simpa using even_int (n : ℤ)

theorem odd_nat (n : ℕ) : Odd n ↔ (((n : ℚ)-1)/2).den=1 := by
  simpa using odd_int (n : ℤ)

theorem complex_int_unit {z : ℂ} (hz : z.im=0) (n : ℤ) :
    z^n=1 ↔ n=0 ∨ z=1 ∨ (z=-1 ∧ ((n : ℚ)/2).den=1) := by
  have h := PowerPredicates.complex_real_eq_one hz (show (n : ℂ).im=0 by simp)
  simpa [Complex.cpow_intCast, ← PowerPredicates.even_iff, even_int] using h

theorem complex_nat_unit {z : ℂ} (hz : z.im=0) (n : ℕ) :
    z^n=1 ↔ n=0 ∨ z=1 ∨ (z=-1 ∧ ((n : ℚ)/2).den=1) := by
  simpa using complex_int_unit hz (n : ℤ)

end QSym.ScalarTypes
