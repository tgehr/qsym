import QSym.Functions

namespace QSym.Elementary

theorem log_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x*y) = Real.log x + Real.log y := Real.log_mul hx.ne' hy.ne'

theorem half_ne_int (n : ℤ) : (1/2 : ℝ) ≠ n := by
  intro h
  have h0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have h1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

theorem inv_two_ne_int (n : ℤ) : (2 : ℝ)⁻¹ ≠ n := by
  simpa only [one_div] using half_ne_int n

theorem nonnegative_of_pos_or_zero {x : ℝ} (h : 0 < x ∨ x = 0) : 0 ≤ x := by
  rcases h with h | rfl
  · exact h.le
  · exact le_rfl

theorem rpow_half (x : ℝ) : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
  simpa only [one_div] using (Real.sqrt_eq_rpow x).symm

theorem sqrt_not_neg (x : ℝ) : ¬Real.sqrt x < 0 := not_lt.mpr (Real.sqrt_nonneg x)

theorem rpow_mul_pos {x : ℝ} (hx : 0 < x) (y z : ℝ) :
    x ^ (y*z) = (x ^ y) ^ z := Real.rpow_mul hx.le y z

theorem half_domain (x : ℝ) : Functions.powerR.domain x (1/2) ↔ 0 ≤ x := by
  simp only [Functions.powerR, half_ne_int, exists_const, and_false, or_false]
  constructor
  · rintro (h | ⟨rfl, _⟩) <;> linarith
  · intro h; rcases eq_or_lt_of_le h with h | h
    · exact Or.inr ⟨h.symm, by norm_num⟩
    · exact Or.inl h

theorem root_power (y : ℝ) (m n : ℕ) (hy : 0 ≤ y) :
    (y ^ (n+1)) ^ ((m : ℝ)/(n+1)) = y ^ m := by
  calc
    _ = (y ^ ((n+1 : ℕ) : ℝ)) ^ ((m : ℝ)/(n+1)) := by rw [Real.rpow_natCast]
    _ = y ^ (((n+1 : ℕ) : ℝ)*((m : ℝ)/(n+1))) := (Real.rpow_mul hy _ _).symm
    _ = y ^ (m : ℝ) := by congr 1; push_cast; field_simp
    _ = y ^ m := Real.rpow_natCast y m

theorem sin_three_half_pi : Real.sin ((3/2 : ℝ)*Real.pi) = -1 := by
  rw [show (3/2 : ℝ)*Real.pi = Real.pi/2+Real.pi by ring, Real.sin_add_pi]
  simp

theorem cos_three_half_pi : Real.cos ((3/2 : ℝ)*Real.pi) = 0 := by
  rw [show (3/2 : ℝ)*Real.pi = Real.pi/2+Real.pi by ring, Real.cos_add_pi]
  simp

theorem sin_period (x : ℝ) (n : ℤ) :
    Real.sin (x + -1*((n : ℝ)*(2*Real.pi))) = Real.sin x := by
  simpa only [neg_one_mul, sub_eq_add_neg] using Real.sin_sub_int_mul_two_pi x n

theorem cos_period (x : ℝ) (n : ℤ) :
    Real.cos (x + -1*((n : ℝ)*(2*Real.pi))) = Real.cos x := by
  simpa only [neg_one_mul, sub_eq_add_neg] using Real.cos_sub_int_mul_two_pi x n

theorem exp_phase (z : ℂ) (h : z.re = 0) : Complex.exp (z.im*Complex.I) = Complex.exp z := by
  congr 1
  apply Complex.ext <;> simp [h]

theorem phase_period (x : ℝ) (n : ℤ) :
    Complex.exp (((x + -1*((n : ℝ)*(2*Real.pi)) : ℝ) : ℂ)*Complex.I) =
      Complex.exp (x*Complex.I) := by
  push_cast
  rw [show ((x : ℂ) + -1*((n : ℂ)*(2*Real.pi)))*Complex.I =
    x*Complex.I - n*(2*Real.pi*Complex.I) by ring, Complex.exp_sub]
  simp

theorem phase_half_pi : Complex.exp (Complex.I*(Real.pi : ℂ)/2) = Complex.I := by
  convert Complex.exp_pi_div_two_mul_I using 2; ring

theorem phase_period_normal (x : ℝ) (n : ℤ) :
    Complex.exp (Complex.I*(x : ℂ) - (Real.pi : ℂ)*(Complex.I*n)*2) =
      Complex.exp (Complex.I*x) := by
  convert phase_period x n using 2 <;> push_cast <;> ring

end QSym.Elementary
