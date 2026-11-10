import QSym.Elementary
import QSym.FunctionOrder

namespace QSym.Inverse

private theorem sqrt_sq (z : ℂ) : (z^(1/2 : ℂ))^2=z := by simp

private theorem log_pair (z s : ℂ) (hs : s^2=z^2+1) :
    Complex.sinh (Complex.log (z+s))=z ∧ Complex.cosh (Complex.log (z+s))=s := by
  have hp : (z+s)*(s-z)=1 := by
    calc
      _=s^2-z^2 := by ring
      _=1 := by rw [hs]; ring
  have hz : z+s≠0 := by intro h; rw [h, zero_mul] at hp; norm_num at hp
  have hi : (z+s)⁻¹=s-z := by
    apply mul_left_cancel₀ hz
    rw [mul_inv_cancel₀ hz, hp]
  constructor
  · rw [Complex.sinh, Complex.exp_neg, Complex.exp_log hz, hi]; ring
  · rw [Complex.cosh, Complex.exp_neg, Complex.exp_log hz, hi]; ring

private theorem log_pair_cosh (z s : ℂ) (hs : s^2=z^2-1) :
    Complex.cosh (Complex.log (z+s))=z ∧ Complex.sinh (Complex.log (z+s))=s := by
  have h := log_pair s z (by rw [hs]; ring)
  simpa only [add_comm] using And.intro h.2 h.1

theorem complex_sinh_asinh (z : ℂ) : Complex.sinh (Functions.asinhC.value z)=z :=
  (log_pair z _ (sqrt_sq _)).1

theorem complex_cosh_asinh (z : ℂ) :
    Complex.cosh (Functions.asinhC.value z)=(z^2+1)^(1/2 : ℂ) :=
  (log_pair z _ (sqrt_sq _)).2

private theorem acosh_root_sq (z : ℂ) :
    ((z-1)^(1/2 : ℂ)*(z+1)^(1/2 : ℂ))^2=z^2-1 := by
  rw [mul_pow, sqrt_sq, sqrt_sq]; ring

theorem complex_cosh_acosh (z : ℂ) : Complex.cosh (Functions.acoshC.value z)=z :=
  (log_pair_cosh z _ (acosh_root_sq z)).1

theorem complex_sinh_acosh (z : ℂ) :
    Complex.sinh (Functions.acoshC.value z)=(z-1)^(1/2 : ℂ)*(z+1)^(1/2 : ℂ) :=
  (log_pair_cosh z _ (acosh_root_sq z)).2

private theorem asin_pair (z : ℂ) :
    Complex.sinh (Complex.log (Complex.I*z+(1-z^2)^(1/2 : ℂ)))=Complex.I*z ∧
    Complex.cosh (Complex.log (Complex.I*z+(1-z^2)^(1/2 : ℂ)))=(1-z^2)^(1/2 : ℂ) := by
  apply log_pair
  rw [sqrt_sq, mul_pow, Complex.I_sq]
  ring

theorem complex_sin_asin (z : ℂ) : Complex.sin (Functions.asinC.value z)=z := by
  change Complex.sin (-Complex.I*Complex.log (Complex.I*z+(1-z^2)^(1/2 : ℂ)))=z
  rw [neg_mul, Complex.sin_neg, Elementary.sin_imaginary, (asin_pair z).1]
  simp [← mul_assoc]

theorem complex_cos_asin (z : ℂ) :
    Complex.cos (Functions.asinC.value z)=(1-z^2)^(1/2 : ℂ) := by
  change Complex.cos (-Complex.I*Complex.log (Complex.I*z+(1-z^2)^(1/2 : ℂ)))=_
  rw [neg_mul, Complex.cos_neg, Elementary.cos_imaginary, (asin_pair z).2]

theorem complex_cos_acos (z : ℂ) : Complex.cos (Functions.acosC.value z)=z := by
  change Complex.cos ((Real.pi : ℂ)/2-Functions.asinC.value z)=z
  rw [Complex.cos_sub, Complex.cos_pi_div_two, Complex.sin_pi_div_two, complex_sin_asin]
  ring

theorem complex_sin_acos (z : ℂ) :
    Complex.sin (Functions.acosC.value z)=(1-z^2)^(1/2 : ℂ) := by
  change Complex.sin ((Real.pi : ℂ)/2-Functions.asinC.value z)=_
  rw [Complex.sin_sub, Complex.cos_pi_div_two, Complex.sin_pi_div_two, complex_cos_asin]
  ring

private theorem tanh_of_exp (w z : ℂ) (h : Complex.exp (2*w)*(1-z)=1+z) :
    Complex.tanh w=z := by
  have he := Complex.exp_ne_zero w
  have hh : Complex.exp w^2*(1-z)=1+z := by
    simpa only [two_mul, Complex.exp_add, pow_two] using h
  have hn : Complex.exp w^2+1≠0 := by
    intro hn
    have : (2 : ℂ)=0 := by linear_combination -hh+(1-z)*hn
    norm_num at this
  have hd : Complex.exp w+(Complex.exp w)⁻¹≠0 := by
    intro hd
    apply hn
    calc
      _=Complex.exp w*(Complex.exp w+(Complex.exp w)⁻¹) := by field_simp; ring
      _=0 := by rw [hd, mul_zero]
  have hs : Complex.exp w-(Complex.exp w)⁻¹=z*(Complex.exp w+(Complex.exp w)⁻¹) := by
    apply mul_left_cancel₀ he
    field_simp
    linear_combination hh
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.sinh, Complex.cosh, Complex.exp_neg, hs]
  field_simp [hd]
  exact mul_div_cancel_right₀ z (by simpa only [pow_two] using hn)

theorem complex_tanh_atanh (z : ℂ) (hp : z≠1) (hm : z≠-1) :
    Complex.tanh (Functions.atanhC.value z)=z := by
  have hp' : 1+z≠0 := by intro h; apply hm; linear_combination h
  have hm' : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hp)
  apply tanh_of_exp
  change Complex.exp (2*((Complex.log (1+z)-Complex.log (1-z))/2))*(1-z)=1+z
  rw [show 2*((Complex.log (1+z)-Complex.log (1-z))/2)=Complex.log (1+z)-Complex.log (1-z) by ring]
  rw [Complex.exp_sub, Complex.exp_log hp', Complex.exp_log hm', div_mul_cancel₀ _ hm']

theorem complex_tan_atan (z : ℂ) (hp : z≠Complex.I) (hm : z≠-Complex.I) :
    Complex.tan (Functions.atanC.value z)=z := by
  have hp' : Complex.I*z≠1 := by
    intro h; apply hm
    calc
      z=-(Complex.I*(Complex.I*z)) := by simp [← mul_assoc]
      _=-Complex.I := by rw [h]; ring
  have hm' : Complex.I*z≠-1 := by
    intro h; apply hp
    calc
      z=-(Complex.I*(Complex.I*z)) := by simp [← mul_assoc]
      _=Complex.I := by rw [h]; ring
  have hv : Functions.atanC.value z=-(Complex.I*Functions.atanhC.value (Complex.I*z)) := by
    simp only [Functions.atanC, Functions.atanhC]
    ring
  rw [hv, Complex.tan_neg, Elementary.tan_imaginary, complex_tanh_atanh _ hp' hm']
  simp [← mul_assoc]

theorem real_cosh_acosh (x : ℝ) (hx : 1≤x) : Real.cosh (Functions.acoshR.value x)=x := by
  have hs := Real.sq_sqrt (show 0≤x^2-1 by nlinarith)
  have hn := Real.sqrt_nonneg (x^2-1)
  have hp : 0<x+Real.sqrt (x^2-1) := by linarith
  have hi : (x+Real.sqrt (x^2-1))⁻¹=x-Real.sqrt (x^2-1) := by
    apply mul_left_cancel₀ hp.ne'
    rw [mul_inv_cancel₀ hp.ne']
    nlinarith
  change Real.cosh (Real.log (x+Real.sqrt (x^2-1)))=x
  rw [Real.cosh_log hp, hi]; ring

theorem real_sinh_acosh (x : ℝ) (hx : 1≤x) :
    Real.sinh (Functions.acoshR.value x)=Real.sqrt (x^2-1) := by
  have hs := Real.sq_sqrt (show 0≤x^2-1 by nlinarith)
  have hn := Real.sqrt_nonneg (x^2-1)
  have hp : 0<x+Real.sqrt (x^2-1) := by linarith
  have hi : (x+Real.sqrt (x^2-1))⁻¹=x-Real.sqrt (x^2-1) := by
    apply mul_left_cancel₀ hp.ne'
    rw [mul_inv_cancel₀ hp.ne']
    nlinarith
  change Real.sinh (Real.log (x+Real.sqrt (x^2-1)))=_
  rw [Real.sinh_log hp, hi]; ring

theorem real_acosh_cosh (x : ℝ) : Functions.acoshR.value (Real.cosh x)=|x| := by
  have hp (x : ℝ) (hx : 0≤x) : Functions.acoshR.value (Real.cosh x)=x := by
    change Real.log (Real.cosh x+Real.sqrt (Real.cosh x^2-1))=x
    rw [show Real.cosh x^2-1=Real.sinh x^2 by linarith [Real.cosh_sq_sub_sinh_sq x],
      Real.sqrt_sq (Real.sinh_nonneg_iff.mpr hx), Real.cosh_add_sinh, Real.log_exp]
  by_cases hx : 0≤x
  · rw [hp x hx, abs_of_nonneg hx]
  · rw [← Real.cosh_neg, hp (-x) (by linarith), abs_of_neg (lt_of_not_ge hx)]

theorem real_tanh_atanh (x : ℝ) (hl : -1<x) (hu : x<1) :
    Real.tanh (Functions.atanhR.value x)=x := by
  have he : (Functions.atanhR.value x : ℂ)=Functions.atanhC.value (x : ℂ) := by
    simp only [Functions.atanhR, Functions.atanhC, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_ofNat, Complex.ofReal_log (show 0≤1+x by linarith),
      Complex.ofReal_log (show 0≤1-x by linarith), Complex.ofReal_add, Complex.ofReal_one]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tanh, he, complex_tanh_atanh]
  · exact_mod_cast (ne_of_lt hu)
  · exact_mod_cast (ne_of_gt hl)

theorem real_atanh_tanh (x : ℝ) (h : Functions.atanhR.domain (Real.tanh x)) :
    Functions.atanhR.value (Real.tanh x)=x := by
  apply FunctionOrder.tanh.injOn (show Functions.tanhR.domain (Functions.atanhR.value (Real.tanh x)) from trivial)
    (show Functions.tanhR.domain x from trivial)
  exact real_tanh_atanh _ h.1 h.2

end QSym.Inverse
