import QSym.Elementary
import QSym.Order
import Mathlib.Algebra.Order.Field.Power

namespace QSym.PowerPredicates

theorem real_value (x t : ℝ) : Functions.powerR.value x t=x^t := rfl
theorem complex_value (z w : ℂ) : Functions.powerC.value z w=z^w := rfl

theorem integer_iff (x : ℝ) : x=(⌊x⌋ : ℤ) ↔ ∃ k : ℤ, x=k := by
  constructor
  · exact fun h => ⟨⌊x⌋, h⟩
  · rintro ⟨k, rfl⟩; simp

theorem even_iff (k : ℤ) : Even k ↔ (k : ℝ)/2=(⌊(k : ℝ)/2⌋ : ℤ) := by
  rw [integer_iff]
  constructor
  · rintro ⟨j, rfl⟩; refine ⟨j, ?_⟩; push_cast; ring
  · rintro ⟨j, h⟩; refine ⟨j, ?_⟩; exact_mod_cast (show (k : ℝ)=(j : ℝ)+j by linarith)

theorem odd_iff (k : ℤ) : Odd k ↔ ((k : ℝ)-1)/2=(⌊((k : ℝ)-1)/2⌋ : ℤ) := by
  rw [integer_iff]
  constructor
  · rintro ⟨j, rfl⟩; refine ⟨j, ?_⟩; push_cast; ring
  · rintro ⟨j, h⟩; refine ⟨j, ?_⟩; exact_mod_cast (show (k : ℝ)=2*(j : ℝ)+1 by linarith)

theorem nonnegative_eq_one {x t : ℝ} (hx : 0≤x) :
    x^t=1 ↔ t=0 ∨ x=1 := by
  by_cases ht : t=0
  · simp [ht]
  · simpa [ht] using Real.rpow_left_inj hx (by norm_num : (0 : ℝ)≤1) ht

theorem real_eq_one {x t : ℝ} (hd : Functions.powerR.domain x t) :
    x^t=1 ↔ t=0 ∨ x=1 ∨ (x=-1 ∧ t/2=(⌊t/2⌋ : ℤ)) := by
  by_cases hx : 0≤x
  · rw [nonnegative_eq_one hx]
    have hn : x≠-1 := by linarith
    simp [hn]
  · rcases hd with h | ⟨h, _⟩ | ⟨_, k, rfl⟩
    · exact (hx h.le).elim
    · simp [h] at hx
    · rw [Real.rpow_intCast, zpow_eq_one_iff_cases₀, even_iff]
      simp only [Int.cast_eq_zero]

theorem real_eq_neg_one {x t : ℝ} (hd : Functions.powerR.domain x t) :
    x^t=-1 ↔ x=-1 ∧ (t-1)/2=(⌊(t-1)/2⌋ : ℤ) := by
  by_cases hx : 0≤x
  · have h : x^t≠-1 := by have := Real.rpow_nonneg hx t; linarith
    have hn : x≠-1 := by linarith
    simp [h, hn]
  · rcases hd with h | ⟨h, _⟩ | ⟨_, k, rfl⟩
    · exact (hx h.le).elim
    · simp [h] at hx
    · rw [Real.rpow_intCast, zpow_eq_neg_one_iff₀, odd_iff]

theorem complex_neg_one_eq_one (t : ℝ) :
    (-1 : ℂ)^(t : ℂ)=1 ↔ t/2=(⌊t/2⌋ : ℤ) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (-1 : ℂ)≠0), Complex.log_neg_one,
    Complex.exp_eq_one_iff, integer_iff]
  constructor
  · rintro ⟨k, h⟩
    have hi := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, zero_add, mul_one,
      Complex.intCast_re, Complex.intCast_im] at hi
    norm_num at hi
    refine ⟨k, ?_⟩
    have he : t=2*(k : ℝ) := by
      apply (mul_left_cancel₀ Real.pi_ne_zero)
      nlinarith only [hi]
    linarith only [he]
  · rintro ⟨k, h⟩
    refine ⟨k, ?_⟩
    have ht : t=2*(k : ℝ) := by linarith
    rw [ht]; push_cast; ring

theorem complex_ofReal_eq_one (x t : ℝ) :
    (x : ℂ)^(t : ℂ)=1 ↔ t=0 ∨ x=1 ∨ (x=-1 ∧ t/2=(⌊t/2⌋ : ℤ)) := by
  by_cases ht : t=0
  · simp [ht]
  constructor
  · intro h
    have hn := congrArg norm h
    rw [Complex.norm_cpow_real] at hn
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_one] at hn
    have ha : |x|=1 := (nonnegative_eq_one (abs_nonneg x)).mp hn |>.resolve_left ht
    rcases (abs_eq (by norm_num : (0 : ℝ)≤1)).mp ha with hx | hx
    · exact Or.inr (Or.inl hx)
    · refine Or.inr (Or.inr ⟨hx, ?_⟩)
      subst x
      exact (complex_neg_one_eq_one t).mp (by simpa using h)
  · rintro (h | h | ⟨h, he⟩)
    · exact (ht h).elim
    · simp [h]
    · simpa [h] using (complex_neg_one_eq_one t).mpr he

theorem complex_real_eq_one {z w : ℂ} (hz : z.im=0) (hw : w.im=0) :
    z^w=1 ↔ w.re=0 ∨ z=1 ∨ (z=-1 ∧ w.re/2=(⌊w.re/2⌋ : ℤ)) := by
  rw [← Elementary.real_exponent hz, ← Elementary.real_exponent hw]
  simpa only [Complex.ofReal_re, ← Complex.ofReal_neg, ← Complex.ofReal_one, Complex.ofReal_inj] using complex_ofReal_eq_one z.re w.re

theorem complex_nonnegative_power {z w : ℂ} (hz : z.im=0) (hx : 0≤z.re) (hw : w.im=0) :
    z^w=(z.re^w.re : ℝ) := by
  rw [← Elementary.real_exponent hz, ← Elementary.real_exponent hw]
  exact (Complex.ofReal_cpow hx _).symm

theorem real_neg_one_eq_one {t : ℝ} (hd : Functions.powerR.domain (-1) t) :
    (-1 : ℝ)^t=1 ↔ t/2=(⌊t/2⌋ : ℤ) := by
  rw [real_eq_one hd]
  by_cases ht : t=0 <;> norm_num [ht]

theorem noninteger_eq_one {x t : ℝ} (hi : t≠(⌊t⌋ : ℤ)) (hd : Functions.powerR.domain x t) :
    x^t=1 ↔ x=1 := by
  simpa only [Real.one_rpow] using Order.power_noninteger_eq hi hd
    (show Functions.powerR.domain 1 t from Or.inl zero_lt_one)

theorem complex_minus_one_eq_one {w : ℂ} (hw : w.im=0) :
    (-1 : ℂ)^w=1 ↔ w.re/2=(⌊w.re/2⌋ : ℤ) := by
  rw [← Elementary.real_exponent hw]
  simpa using complex_neg_one_eq_one w.re

theorem nonnegative_domain {z w : ℂ} (hz : z.im=0) (hx : 0≤z.re) (hw : w.im=0)
    (hd : Functions.powerC.domain z w) : Functions.powerR.domain z.re w.re := by
  rcases hx.eq_or_lt with he | hp
  · have hzero : z=0 := Complex.ext he.symm hz
    subst z
    rcases hd with h | rfl | ⟨hr, _⟩
    · exact (h rfl).elim
    · exact Or.inr (Or.inl ⟨rfl, le_rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, hr.le⟩)
  · exact Or.inl hp

end QSym.PowerPredicates
