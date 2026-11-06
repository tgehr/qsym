import QSym.Functions

namespace QSym.Identities

theorem min_eq_max (x y : ℝ) : min x y=max x y ↔ x=y := by
  rcases le_total x y with h | h <;> simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h, eq_comm]

theorem min_mul_max (x y : ℝ) : min x y*max x y=x*y := by
  rcases le_total x y with h | h <;> simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h, mul_comm]

theorem abs_even_power (x : ℝ) (n : ℕ) : |x|^(n+n)=x^(n+n) :=
  (show Even (n+n) from ⟨n, rfl⟩).pow_abs x

theorem log_even_power (x : ℝ) (n : ℕ) : Real.log (x^(n+n+2))=2*(n+1)*Real.log |x| := by
  rw [Real.log_pow, Real.log_abs]
  push_cast
  ring

theorem log_even_domain {x : ℝ} (n : ℕ) (h : 0<x^(n+n+2)) : 0 < |x| := by
  apply abs_pos.mpr
  intro hx
  subst x
  simp at h

theorem exp_log_scale {x : ℝ} (y : ℝ) (hx : 0<x) : Real.exp (y*Real.log x)=x^y := by
  rw [Real.rpow_def_of_pos hx, mul_comm]

theorem exp_log_scale_right {x : ℝ} (y : ℝ) (hx : 0<x) : Real.exp (Real.log x*y)=x^y :=
  (Real.rpow_def_of_pos hx y).symm

theorem cexp_log_scale {z : ℂ} (w : ℂ) (hz : z≠0) : Complex.exp (w*Complex.log z)=z^w := by
  rw [Complex.cpow_def_of_ne_zero hz, mul_comm]

theorem cexp_log_scale_right {z : ℂ} (w : ℂ) (hz : z≠0) : Complex.exp (Complex.log z*w)=z^w :=
  (Complex.cpow_def_of_ne_zero hz w).symm

theorem clog_inj {z w : ℂ} (hz : z≠0) (hw : w≠0) : Complex.log z=Complex.log w ↔ z=w := by
  constructor
  · intro h
    simpa [Complex.exp_log hz, Complex.exp_log hw] using congrArg Complex.exp h
  · rintro rfl; rfl

theorem clog_zero {z : ℂ} (hz : z≠0) : Complex.log z=0 ↔ z=1 := by
  simpa using (clog_inj hz (one_ne_zero : (1 : ℂ)≠0))

theorem csqrt_inj (z w : ℂ) : z^(2⁻¹ : ℂ)=w^(2⁻¹ : ℂ) ↔ z=w := by
  constructor
  · intro h
    have he := congrArg (fun a : ℂ => a^2) h
    change (z^(2⁻¹ : ℂ))^2=(w^(2⁻¹ : ℂ))^2 at he
    rw [Complex.cpow_ofNat_inv_pow z 2, Complex.cpow_ofNat_inv_pow w 2] at he
    exact he
  · rintro rfl; rfl

theorem cexp_inj {z w : ℂ} (hz₁ : -Real.pi<z.im) (hz₂ : z.im≤Real.pi)
    (hw₁ : -Real.pi<w.im) (hw₂ : w.im≤Real.pi) : Complex.exp z=Complex.exp w ↔ z=w :=
  ⟨Complex.exp_inj_of_neg_pi_lt_of_le_pi hz₁ hz₂ hw₁ hw₂, congrArg Complex.exp⟩

theorem conj_eq (z : ℂ) : z=starRingEnd ℂ z ↔ z.im=0 := by
  rw [Complex.ext_iff]
  simp only [Complex.conj_re, Complex.conj_im, true_and]
  constructor <;> intro h <;> linarith

theorem square_re (z : ℂ) : (z^2).re=z.re^2-z.im^2 := by
  simp [pow_two, Complex.mul_re]

theorem square_im (z : ℂ) : (z^2).im=2*z.re*z.im := by
  simp [pow_two, Complex.mul_im]
  ring

theorem power_product_domain {x y t : ℝ} (hx : 0≤x) (hy : 0≤y)
    (dx : Functions.powerR.domain x t) (dy : Functions.powerR.domain y t) :
    Functions.powerR.domain (x*y) t := by
  by_cases hx0 : x=0
  · subst x
    simpa [Functions.powerR] using dx
  by_cases hy0 : y=0
  · subst y
    simpa [Functions.powerR] using dy
  exact Or.inl (mul_pos (lt_of_le_of_ne hx (Ne.symm hx0)) (lt_of_le_of_ne hy (Ne.symm hy0)))

end QSym.Identities
