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

theorem floor_exact {x : ℝ} {n : ℤ} (hl : (n : ℝ) ≤ x) (hu : x < n+1) :
    n = ⌊x⌋ := ((Int.floor_eq_iff).mpr ⟨hl, hu⟩).symm

theorem ceil_exact {x : ℝ} {n : ℤ} (hl : (n : ℝ) < x+1) (hu : x ≤ n) :
    n = ⌈x⌉ := ((Int.ceil_eq_iff).mpr ⟨by linarith, hu⟩).symm

theorem sqrt_imaginary (y : ℝ) (hy : 0 ≤ y) :
    Complex.I*(y : ℂ) = (-(y : ℂ)^2)^(2⁻¹ : ℂ) := by
  have hl : -(Real.pi/2) < (Complex.I*(y : ℂ)).arg := by
    apply Complex.neg_pi_div_two_lt_arg_iff.mpr
    right; simpa using hy
  have hu : (Complex.I*(y : ℂ)).arg ≤ Real.pi/2 := by
    apply Complex.arg_le_pi_div_two_iff.mpr
    left; simp
  have h := Complex.pow_cpow_ofNat_inv (x := Complex.I*(y : ℂ)) (n := 2) hl hu
  simpa [mul_pow] using h.symm

theorem cartesian_ne_zero {x y : ℝ} (h : x ≠ 0 ∨ y ≠ 0) :
    (x : ℂ)+Complex.I*y ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp at hr hi
  aesop

theorem gamma_real_next {x : ℝ} (n : ℕ) (h : x+(-2-(n : ℝ))=0) :
    Real.Gamma (n+1)+(n : ℝ)*Real.Gamma (n+1)=Real.Gamma x := by
  have hx : x=(n : ℝ)+1+1 := by linarith
  rw [hx, Real.Gamma_add_one (by positivity : (n : ℝ)+1 ≠ 0)]
  ring

theorem gamma_complex_next {x : ℂ} (n : ℕ) (h : x+(-2-(n : ℂ))=0) :
    Complex.Gamma (n+1)+(n : ℂ)*Complex.Gamma (n+1)=Complex.Gamma x := by
  have hx : x=(n : ℂ)+1+1 := by linear_combination h
  have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast (show (n : ℝ)+1 ≠ 0 by positivity)
  rw [hx, Complex.Gamma_add_one _ hn]
  ring

theorem complex_nat_succ_ne_neg (n k : ℕ) : (n : ℂ)+1 ≠ -(k : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem indexed_negative {K : Type*} [Field K] {x : K} {y : ℤ} (n : ℕ)
    (hd : x ≠ 0 ∨ 0 ≤ y) (he : (n : ℤ)+(y+1)=0) :
    x ≠ 0 ∧ x⁻¹/x^n = x^y := by
  have hy : y = -((n : ℤ)+1) := by omega
  have hn : x ≠ 0 := by rcases hd with h | h; exact h; omega
  constructor
  · exact hn
  · rw [hy, ← Nat.cast_add_one, zpow_neg, zpow_natCast, pow_succ]
    simp [div_eq_mul_inv, mul_comm]

theorem complex_negative {x y : ℂ} (n : ℕ)
    (hd : x ≠ 0 ∨ y=0 ∨ 0<y.re ∧ y.im=0) (he : (n : ℂ)+(y+1)=0) :
    x ≠ 0 ∧ x⁻¹/x^n = x^y := by
  have hy : y = -((n : ℂ)+1) := by linear_combination he
  have hn : x ≠ 0 := by
    rcases hd with h | h | ⟨h, _⟩
    · exact h
    · have hr := congrArg Complex.re h
      simp [hy] at hr
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    · simp [hy] at h
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
  constructor
  · exact hn
  · rw [hy, ← Nat.cast_add_one, Complex.cpow_neg, Complex.cpow_natCast, pow_succ]
    simp [div_eq_mul_inv, mul_comm]

theorem nonnegative_cases {x : ℝ} {P : Prop} (h : 0 ≤ x) : 0<x ∨ x=0 ∨ P := by
  rcases lt_or_eq_of_le h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h.symm)

theorem negative_power {x y : ℝ} (hy : y<0) (hd : Functions.powerR.domain x y) :
    Functions.powerR.domain x (-y) ∧ x^(-y) ≠ 0 ∧ (x^(-y))⁻¹=x^y := by
  rcases hd with h | ⟨rfl, h⟩ | ⟨h, n, rfl⟩
  · exact ⟨Or.inl h, (Real.rpow_pos_of_pos h _).ne', by rw [Real.rpow_neg h.le, inv_inv]⟩
  · linarith
  · refine ⟨Or.inr (Or.inr ⟨h, -n, by simp⟩), ?_, ?_⟩
    · rw [← Int.cast_neg, Real.rpow_intCast]
      exact zpow_ne_zero _ h.ne
    · rw [← Int.cast_neg, Real.rpow_intCast, Real.rpow_intCast, zpow_neg, inv_inv]


theorem real_exponent {w : ℂ} (hi : w.im=0) : (w.re : ℂ)=w := by
  apply Complex.ext <;> simp [hi]

theorem log_cpow_contract (z w : ℂ) (hi : w.im=0) (hl : 0<w.re) (hu : w.re≤1) :
    Complex.log (z^w) = Complex.log z*w := by
  by_cases hz : z=0
  · have hw : w≠0 := by intro h; simp [h] at hl
    simp [hz, Complex.zero_cpow hw]
  rw [Complex.cpow_def_of_ne_zero hz]
  apply Complex.log_exp
  · simp only [Complex.mul_im, Complex.log_im, hi, mul_zero, zero_add]
    have h := mul_lt_mul_of_pos_right (Complex.neg_pi_lt_arg z) hl
    have h' := mul_le_mul_of_nonpos_left hu (neg_nonpos.mpr Real.pi_pos.le)
    linarith
  · simp only [Complex.mul_im, Complex.log_im, hi, mul_zero, zero_add]
    have h := mul_le_mul_of_nonneg_right (Complex.arg_le_pi z) hl.le
    have h' := mul_le_mul_of_nonneg_left hu Real.pi_pos.le
    linarith

theorem arg_cpow_contract (z w : ℂ) (hi : w.im=0) (hl : 0<w.re) (hu : w.re≤1) :
    Complex.arg (z^w) = w.re*Complex.arg z := by
  have h := congrArg Complex.im (log_cpow_contract z w hi hl hu)
  simpa [Complex.log_im, Complex.mul_im, hi, mul_comm] using h

theorem log_sqrt (z : ℂ) : Complex.log (z^(2⁻¹ : ℂ)) = Complex.log z/2 := by
  simpa [div_eq_mul_inv] using log_cpow_contract z (2⁻¹) (by norm_num) (by norm_num) (by norm_num)

theorem arg_sqrt (z : ℂ) : Complex.arg (z^(2⁻¹ : ℂ)) = (2 : ℝ)⁻¹*Complex.arg z := by
  simpa using arg_cpow_contract z (2⁻¹) (by norm_num) (by norm_num) (by norm_num)

theorem norm_cpow_real {z w : ℂ} (hi : w.im=0) : ‖z^w‖=‖z‖^w.re := by
  rw [← real_exponent hi, Complex.norm_cpow_real]
  simp

theorem norm_sqrt (z : ℂ) : ‖z^(2⁻¹ : ℂ)‖ = Real.sqrt ‖z‖ := by
  calc
    _ = ‖z‖^(2⁻¹ : ℝ) := by simpa using Complex.norm_cpow_inv_nat z 2
    _ = _ := rpow_half ‖z‖

theorem arg_exp {z : ℂ} (hl : -Real.pi<z.im) (hu : z.im≤Real.pi) :
    Complex.arg (Complex.exp z)=z.im := by
  simpa only [Complex.log_im] using congrArg Complex.im (Complex.log_exp hl hu)


theorem norm_power_domain {z w : ℂ} (h : z≠0 ∨ w=0 ∨ 0<w.re) :
    z≠0 ∨ z=0 ∧ 0≤w.re := by
  by_cases hz : z=0
  · right; refine ⟨hz, ?_⟩
    rcases h with h | rfl | h
    · exact (h hz).elim
    · simp
    · exact h.le
  · exact Or.inl hz

end QSym.Elementary
