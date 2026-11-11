import QSym.Functions

namespace QSym.Trigonometry

section Parity
variable {α : Type*} [Field α]
theorem parity_even (k : ℤ) : (-1 : α) ^ (2*k) = 1 :=
  (show Even (2*k) from ⟨k, by ring⟩).neg_one_zpow
theorem parity_odd (k : ℤ) : (-1 : α) ^ (2*k+1) = -1 :=
  by rw [zpow_add₀ (by norm_num), parity_even]; simp
theorem parity_neg (k : ℤ) : (-1 : α) ^ (-k) = (-1 : α) ^ k := by
  rw [zpow_neg, ← inv_zpow]; simp
theorem parity_square (k : ℤ) : ((-1 : α)^k)^2=1 := by
  rw [← zpow_natCast, ← zpow_mul]
  norm_num only [Nat.cast_ofNat]
  rw [mul_comm, parity_even]
theorem parity_inverse (k : ℤ) : ((-1 : α)^k)⁻¹=(-1 : α)^k := by
  rw [← zpow_neg, parity_neg]
end Parity

theorem real_integer_cos (k : ℤ) : Real.cos ((k : ℝ)*Real.pi)=(-1 : ℝ)^k := by
  simpa using Real.cos_add_int_mul_pi 0 k

theorem real_sin_half (x : ℝ) (k : ℤ) :
    Real.sin x=(-1 : ℝ)^k*Real.sin (x-k*Real.pi) := by
  rw [Real.sin_sub_int_mul_pi, ← mul_assoc, ← pow_two, parity_square, one_mul]
theorem real_cos_half (x : ℝ) (k : ℤ) :
    Real.cos x=(-1 : ℝ)^k*Real.cos (x-k*Real.pi) := by
  rw [Real.cos_sub_int_mul_pi, ← mul_assoc, ← pow_two, parity_square, one_mul]

theorem complex_sin_sub (z : ℂ) (k : ℤ) :
    Complex.sin (z-k*Real.pi)=(-1 : ℂ)^k*Complex.sin z := by
  simpa only [Int.cast_negOnePow] using Complex.sin_antiperiodic.sub_int_mul_eq (x:=z) k

theorem complex_cos_sub (z : ℂ) (k : ℤ) :
    Complex.cos (z-k*Real.pi)=(-1 : ℂ)^k*Complex.cos z := by
  simpa only [Int.cast_negOnePow] using Complex.cos_antiperiodic.sub_int_mul_eq (x:=z) k

theorem complex_sin_half (z : ℂ) (k : ℤ) :
    Complex.sin z=(-1 : ℂ)^k*Complex.sin (z-k*Real.pi) := by
  rw [complex_sin_sub, ← mul_assoc, ← pow_two, parity_square, one_mul]
theorem complex_cos_half (z : ℂ) (k : ℤ) :
    Complex.cos z=(-1 : ℂ)^k*Complex.cos (z-k*Real.pi) := by
  rw [complex_cos_sub, ← mul_assoc, ← pow_two, parity_square, one_mul]

theorem exp_sub (z : ℂ) (k : ℤ) :
    Complex.exp (z-k*(Real.pi*Complex.I))=(-1 : ℂ)^k*Complex.exp z := by
  simpa only [Int.cast_negOnePow] using Complex.exp_antiperiodic.sub_int_mul_eq (x:=z) k

theorem exp_half (z : ℂ) (k : ℤ) :
    Complex.exp z=(-1 : ℂ)^k*Complex.exp (z-k*(Real.pi*Complex.I)) := by
  rw [exp_sub, ← mul_assoc, ← pow_two, parity_square, one_mul]

theorem sinh_sub (z : ℂ) (k : ℤ) :
    Complex.sinh (z-k*(Real.pi*Complex.I))=(-1 : ℂ)^k*Complex.sinh z := by
  rw [Complex.sinh, exp_sub]
  have h : -(z-k*(Real.pi*Complex.I)) = -z-((-k : ℤ) : ℂ)*(Real.pi*Complex.I) := by push_cast; ring
  rw [h, exp_sub, parity_neg, Complex.sinh]; ring

theorem cosh_sub (z : ℂ) (k : ℤ) :
    Complex.cosh (z-k*(Real.pi*Complex.I))=(-1 : ℂ)^k*Complex.cosh z := by
  rw [Complex.cosh, exp_sub]
  have h : -(z-k*(Real.pi*Complex.I)) = -z-((-k : ℤ) : ℂ)*(Real.pi*Complex.I) := by push_cast; ring
  rw [h, exp_sub, parity_neg, Complex.cosh]; ring

theorem sinh_half (z : ℂ) (k : ℤ) :
    Complex.sinh z=(-1 : ℂ)^k*Complex.sinh (z-k*(Real.pi*Complex.I)) := by
  rw [sinh_sub, ← mul_assoc, ← pow_two, parity_square, one_mul]
theorem cosh_half (z : ℂ) (k : ℤ) :
    Complex.cosh z=(-1 : ℂ)^k*Complex.cosh (z-k*(Real.pi*Complex.I)) := by
  rw [cosh_sub, ← mul_assoc, ← pow_two, parity_square, one_mul]

theorem tan_period (z : ℂ) (k : ℤ) : Complex.tan (z-k*Real.pi)=Complex.tan z :=
  Complex.tan_sub_int_mul_pi z k

theorem tan_period_domain (z : ℂ) (k : ℤ) :
    Complex.cos (z-k*Real.pi)≠0 ↔ Complex.cos z≠0 := by
  rw [complex_cos_sub, mul_ne_zero_iff]; simp [zpow_ne_zero]

theorem tanh_period (z : ℂ) (k : ℤ) :
    Complex.tanh (z-k*(Real.pi*Complex.I))=Complex.tanh z := by
  simp only [Complex.tanh_eq_sinh_div_cosh, sinh_sub, cosh_sub]
  exact mul_div_mul_left _ _ (zpow_ne_zero _ (by norm_num))

theorem tanh_period_domain (z : ℂ) (k : ℤ) :
    Complex.cosh (z-k*(Real.pi*Complex.I))≠0 ↔ Complex.cosh z≠0 := by
  rw [cosh_sub, mul_ne_zero_iff]; simp [zpow_ne_zero]

theorem exp_quarter (z : ℂ) :
    Complex.exp z=Complex.I*Complex.exp (z-Complex.I*(Real.pi/2)) := by
  rw [Complex.exp_sub]
  have h : Complex.exp (Complex.I*(Real.pi/2))=Complex.I := by
    simpa only [mul_comm] using Complex.exp_pi_div_two_mul_I
  rw [h]; simp only [div_eq_mul_inv, Complex.inv_I]; ring_nf; simp [Complex.I_sq] <;> ring

theorem sinh_quarter (z : ℂ) :
    Complex.sinh z=Complex.I*Complex.cosh (z-Complex.I*(Real.pi/2)) := by
  rw [Complex.sinh, Complex.cosh, Complex.exp_sub]
  have h : Complex.exp (Complex.I*(Real.pi/2))=Complex.I := by simpa only [mul_comm] using Complex.exp_pi_div_two_mul_I
  have hn : -(z-Complex.I*(Real.pi/2)) = -z+Complex.I*(Real.pi/2) := by ring
  rw [hn, Complex.exp_add, h]
  simp only [div_eq_mul_inv, Complex.inv_I]; ring_nf; simp [Complex.I_sq] <;> ring

theorem cosh_quarter (z : ℂ) :
    Complex.cosh z=Complex.I*Complex.sinh (z-Complex.I*(Real.pi/2)) := by
  rw [Complex.cosh, Complex.sinh, Complex.exp_sub]
  have h : Complex.exp (Complex.I*(Real.pi/2))=Complex.I := by simpa only [mul_comm] using Complex.exp_pi_div_two_mul_I
  have hn : -(z-Complex.I*(Real.pi/2)) = -z+Complex.I*(Real.pi/2) := by ring
  rw [hn, Complex.exp_add, h]
  simp only [div_eq_mul_inv, Complex.inv_I]; ring_nf; simp [Complex.I_sq] <;> ring

theorem parity_cancel_mul {α : Type*} [Field α] (k : ℤ) (x : α) :
    (-1 : α)^k*((-1 : α)^k*x)=x := by
  rw [← mul_assoc, ← pow_two, parity_square, one_mul]

theorem integer_phase (k : ℤ) :
    Complex.exp (((k : ℝ)*Real.pi : ℝ)*Complex.I)=((-1 : ℝ)^k : ℂ) := by
  push_cast
  rw [mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem phase_sub (x : ℝ) (k : ℤ) :
    Complex.exp (((x-k*Real.pi : ℝ) : ℂ)*Complex.I)=
      ((-1 : ℝ)^k : ℂ)*Complex.exp ((x : ℂ)*Complex.I) := by
  push_cast
  rw [show ((x : ℂ)-k*Real.pi)*Complex.I=x*Complex.I-k*(Real.pi*Complex.I) by ring]
  exact exp_sub _ _

theorem sinh_period (z : ℂ) (k : ℤ) :
    Complex.sinh (z-Complex.I*(k*(2*Real.pi)))=Complex.sinh z := by
  have h := sinh_sub z (2*k)
  rw [parity_even, one_mul] at h
  push_cast at h
  simpa only [ mul_assoc, mul_left_comm, mul_comm] using h

theorem cosh_period (z : ℂ) (k : ℤ) :
    Complex.cosh (z-Complex.I*(k*(2*Real.pi)))=Complex.cosh z := by
  have h := cosh_sub z (2*k)
  rw [parity_even, one_mul] at h
  push_cast at h
  simpa only [ mul_assoc, mul_left_comm, mul_comm] using h

theorem exp_period (z : ℂ) (k : ℤ) :
    Complex.exp (z-Complex.I*(k*(2*Real.pi)))=Complex.exp z := by
  have h := exp_sub z (2*k)
  rw [parity_even, one_mul] at h
  push_cast at h
  simpa only [ mul_assoc, mul_left_comm, mul_comm] using h

theorem sinh_sub_imaginary (z : ℂ) (k : ℤ) :
    Complex.sinh (z-Complex.I*(k*Real.pi))=(-1 : ℂ)^k*Complex.sinh z := by
  convert sinh_sub z k using 2 <;> ring

theorem cosh_sub_imaginary (z : ℂ) (k : ℤ) :
    Complex.cosh (z-Complex.I*(k*Real.pi))=(-1 : ℂ)^k*Complex.cosh z := by
  convert cosh_sub z k using 2 <;> ring

theorem exp_sub_imaginary (z : ℂ) (k : ℤ) :
    Complex.exp (z-Complex.I*(k*Real.pi))=(-1 : ℂ)^k*Complex.exp z := by
  convert exp_sub z k using 2 <;> ring

theorem tanh_period_imaginary (z : ℂ) (k : ℤ) :
    Complex.tanh (z-Complex.I*(k*Real.pi))=Complex.tanh z := by
  convert tanh_period z k using 2 <;> ring

theorem cosh_quarter_sub (z : ℂ) :
    Complex.cosh (z-Complex.I*(Real.pi/2))=-Complex.I*Complex.sinh z := by
  have h := congrArg (fun w : ℂ => -Complex.I*w) (sinh_quarter z)
  simpa [← mul_assoc] using h.symm

theorem sinh_quarter_sub (z : ℂ) :
    Complex.sinh (z-Complex.I*(Real.pi/2))=-Complex.I*Complex.cosh z := by
  have h := congrArg (fun w : ℂ => -Complex.I*w) (cosh_quarter z)
  simpa [← mul_assoc] using h.symm

theorem exp_quarter_sub (z : ℂ) :
    Complex.exp (z-Complex.I*(Real.pi/2))=-Complex.I*Complex.exp z := by
  have h := congrArg (fun w : ℂ => -Complex.I*w) (exp_quarter z)
  simpa [← mul_assoc] using h.symm

theorem tanh_lt_one (x : ℝ) : Real.tanh x<1 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (Real.cosh_pos x)]
  have h := Real.exp_pos (-x)
  rw [← Real.cosh_sub_sinh] at h; linarith

theorem neg_one_lt_tanh (x : ℝ) : -1<Real.tanh x := by
  have h := tanh_lt_one (-x)
  rw [Real.tanh_neg] at h; linarith

theorem real_sin_half_normal (x : ℝ) (k : ℤ) :
    Real.sin (x-Real.pi*k)=(-1 : ℝ)^k*Real.sin x := by
  simpa only [mul_comm] using Real.sin_sub_int_mul_pi x k

theorem real_cos_half_normal (x : ℝ) (k : ℤ) :
    Real.cos (x-Real.pi*k)=(-1 : ℝ)^k*Real.cos x := by
  simpa only [mul_comm] using Real.cos_sub_int_mul_pi x k

theorem complex_sin_half_normal (x : ℂ) (k : ℤ) :
    Complex.sin (x-Real.pi*k)=(-1 : ℂ)^k*Complex.sin x := by
  simpa only [mul_comm] using complex_sin_sub x k

theorem complex_cos_half_normal (x : ℂ) (k : ℤ) :
    Complex.cos (x-Real.pi*k)=(-1 : ℂ)^k*Complex.cos x := by
  simpa only [mul_comm] using complex_cos_sub x k

theorem complex_sin_period_normal (z : ℂ) (k : ℤ) :
    Complex.sin (z-Real.pi*k*2)=Complex.sin z := by
  convert Complex.sin_sub_int_mul_two_pi z k using 2 <;> ring

theorem complex_cos_period_normal (z : ℂ) (k : ℤ) :
    Complex.cos (z-Real.pi*k*2)=Complex.cos z := by
  convert Complex.cos_sub_int_mul_two_pi z k using 2 <;> ring

theorem tan_period_normal (z : ℂ) (k : ℤ) :
    Complex.tan (z-Real.pi*k)=Complex.tan z := by
  simpa only [mul_comm] using tan_period z k

theorem sinh_period_normal (z : ℂ) (k : ℤ) :
    Complex.sinh (z-Real.pi*(Complex.I*k)*2)=Complex.sinh z := by
  convert sinh_period z k using 2 <;> ring

theorem sinh_half_normal (z : ℂ) (k : ℤ) :
    Complex.sinh (z-Real.pi*(Complex.I*k))=(-1 : ℂ)^k*Complex.sinh z := by
  convert sinh_sub z k using 2 <;> ring

theorem sinh_quarter_normal (z : ℂ) :
    Complex.sinh (z+Complex.I*Real.pi*(-1/2))=-Complex.I*Complex.cosh z := by
  convert sinh_quarter_sub z using 2 <;> ring

theorem cosh_period_normal (z : ℂ) (k : ℤ) :
    Complex.cosh (z-Real.pi*(Complex.I*k)*2)=Complex.cosh z := by
  convert cosh_period z k using 2 <;> ring

theorem cosh_half_normal (z : ℂ) (k : ℤ) :
    Complex.cosh (z-Real.pi*(Complex.I*k))=(-1 : ℂ)^k*Complex.cosh z := by
  convert cosh_sub z k using 2 <;> ring

theorem cosh_quarter_normal (z : ℂ) :
    Complex.cosh (z+Complex.I*Real.pi*(-1/2))=-Complex.I*Complex.sinh z := by
  convert cosh_quarter_sub z using 2 <;> ring

theorem exp_period_normal (z : ℂ) (k : ℤ) :
    Complex.exp (z-Real.pi*(Complex.I*k)*2)=Complex.exp z := by
  convert exp_period z k using 2 <;> ring

theorem exp_half_normal (z : ℂ) (k : ℤ) :
    Complex.exp (z-Real.pi*(Complex.I*k))=(-1 : ℂ)^k*Complex.exp z := by
  convert exp_sub z k using 2 <;> ring

theorem exp_quarter_normal (z : ℂ) :
    Complex.exp (z+Complex.I*Real.pi*(-1/2))=-Complex.I*Complex.exp z := by
  convert exp_quarter_sub z using 2 <;> ring

theorem tanh_period_normal (z : ℂ) (k : ℤ) :
    Complex.tanh (z-Real.pi*(Complex.I*k))=Complex.tanh z := by
  convert tanh_period z k using 2 <;> ring

theorem exp_integer_half_normal (k : ℤ) :
    Complex.exp (Real.pi*(Complex.I*k))=(-1 : ℂ)^k := by
  have h := integer_phase k
  push_cast at h
  convert h using 2 <;> ring

theorem exp_integer_period_normal (k : ℤ) :
    Complex.exp (Real.pi*(Complex.I*k)*2)=1 := by
  convert Complex.exp_int_mul_two_pi_mul_I k using 2 <;> ring

theorem exp_quarter_value : Complex.exp (Complex.I*Real.pi/2)=Complex.I := by
  convert Complex.exp_pi_div_two_mul_I using 2 <;> ring


theorem complex_sin_quarter_normal (z : ℂ) :
    Complex.sin (z+Real.pi*(-1/2))=-Complex.cos z := by
  convert Complex.sin_sub_pi_div_two z using 2 <;> ring

theorem complex_cos_quarter_normal (z : ℂ) :
    Complex.cos (z+Real.pi*(-1/2))=Complex.sin z := by
  convert Complex.cos_sub_pi_div_two z using 2 <;> ring

theorem integer_cos_normal (k : ℤ) : Real.cos (Real.pi*k)=(-1 : ℝ)^k := by
  simpa only [mul_comm] using real_integer_cos k

theorem cosh_not_nonpositive (x : ℝ) : ¬Real.cosh x≤0 := not_le.mpr (Real.cosh_pos x)
theorem tanh_not_ge_one (x : ℝ) : ¬1≤Real.tanh x := not_le.mpr (tanh_lt_one x)
theorem tanh_not_le_neg_one (x : ℝ) : ¬Real.tanh x≤-1 := not_le.mpr (neg_one_lt_tanh x)

theorem integer_phase_normal (k : ℤ) :
    Complex.exp (Complex.I*(Real.pi*k))=(-1 : ℂ)^k := by
  convert exp_integer_half_normal k using 2 <;> ring


theorem sinh_quarter_add (z : ℂ) :
    Complex.sinh (z+Complex.I*(Real.pi/2))=Complex.I*Complex.cosh z := by
  simpa only [add_sub_cancel_right] using sinh_quarter (z+Complex.I*(Real.pi/2))
theorem cosh_quarter_add (z : ℂ) :
    Complex.cosh (z+Complex.I*(Real.pi/2))=Complex.I*Complex.sinh z := by
  simpa only [add_sub_cancel_right] using cosh_quarter (z+Complex.I*(Real.pi/2))
theorem sinh_quarter_add_normal (z : ℂ) :
    Complex.sinh (z+Complex.I*Real.pi/2)=Complex.I*Complex.cosh z := by
  convert sinh_quarter_add z using 2 <;> ring
theorem cosh_quarter_add_normal (z : ℂ) :
    Complex.cosh (z+Complex.I*Real.pi/2)=Complex.I*Complex.sinh z := by
  convert cosh_quarter_add z using 2 <;> ring

end QSym.Trigonometry
