import QSym.RefinementBase

namespace QSym.AtanhCompositions

theorem real_exp (x : ℝ) (hl : -1<x) (hu : x<1) :
    Real.exp (Functions.atanhR.value x)=(1+x)/(Real.sqrt (1-x^2)) := by
  rw [← Real.cosh_add_sinh, Inverse.real_cosh_atanh x hl hu,
    Inverse.real_sinh_atanh x hl hu]
  ring

theorem complex_exp (z : ℂ) (hp : z≠1) (hm : z≠-1) :
    Complex.exp (Functions.atanhC.value z)=(1+z)^(1/2 : ℂ)/(1-z)^(1/2 : ℂ) := by
  have ha : 1+z≠0 := by intro h; apply hm; linear_combination h
  have hb : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hp)
  rw [Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hb, ← Complex.exp_sub]
  congr 1
  dsimp [Functions.atanhC]
  ring

theorem complex_cosh (z : ℂ) (hp : z≠1) (hm : z≠-1) :
    Complex.cosh (Functions.atanhC.value z)=((1+z)^(1/2 : ℂ)*(1-z)^(1/2 : ℂ))⁻¹ := by
  have ha : 1+z≠0 := by intro h; apply hm; linear_combination h
  have hb : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hp)
  have hs (w : ℂ) : (w^(1/2 : ℂ))^2=w := by simp
  have hna : (1+z)^(1/2 : ℂ)≠0 := by simpa using ha
  have hnb : (1-z)^(1/2 : ℂ)≠0 := by simpa using hb
  rw [Complex.cosh, Complex.exp_neg, complex_exp z hp hm]
  field_simp
  linear_combination ((1+z)^(1/2 : ℂ)*(1-z)^(1/2 : ℂ))*(hs (1+z)+hs (1-z))

theorem complex_sinh (z : ℂ) (hp : z≠1) (hm : z≠-1) :
    Complex.sinh (Functions.atanhC.value z)=z*((1+z)^(1/2 : ℂ)*(1-z)^(1/2 : ℂ))⁻¹ := by
  have ht := Inverse.complex_tanh_atanh z hp hm
  have hc := complex_cosh z hp hm
  have ha : 1+z≠0 := by intro h; apply hm; linear_combination h
  have hb : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hp)
  have hn : Complex.cosh (Functions.atanhC.value z)≠0 := by simp [hc, ha, hb]
  rw [Complex.tanh_eq_sinh_div_cosh] at ht
  rw [← hc]
  exact (div_eq_iff hn).mp ht

theorem imaginary_domain (z : ℂ) (hp : z≠Complex.I) (hm : z≠-Complex.I) :
    Complex.I*z≠1 ∧ Complex.I*z≠-1 := by
  constructor
  · intro h; apply hm
    calc
      z=-(Complex.I*(Complex.I*z)) := by simp [← mul_assoc]
      _=-Complex.I := by rw [h]; ring
  · intro h; apply hp
    calc
      z=-(Complex.I*(Complex.I*z)) := by simp [← mul_assoc]
      _=Complex.I := by rw [h]; ring

theorem atan_atanh (z : ℂ) : Functions.atanC.value z=-(Complex.I*Functions.atanhC.value (Complex.I*z)) := by
  dsimp [Functions.atanC, Functions.atanhC]
  ring

theorem complex_cos (z : ℂ) (hp : z≠Complex.I) (hm : z≠-Complex.I) :
    Complex.cos (Functions.atanC.value z)=((1+Complex.I*z)^(1/2 : ℂ)*(1-Complex.I*z)^(1/2 : ℂ))⁻¹ := by
  have h := imaginary_domain z hp hm
  rw [atan_atanh, Complex.cos_neg, Elementary.cos_imaginary, complex_cosh _ h.1 h.2]

theorem complex_sin (z : ℂ) (hp : z≠Complex.I) (hm : z≠-Complex.I) :
    Complex.sin (Functions.atanC.value z)=z*((1+Complex.I*z)^(1/2 : ℂ)*(1-Complex.I*z)^(1/2 : ℂ))⁻¹ := by
  have h := imaginary_domain z hp hm
  rw [atan_atanh, Complex.sin_neg, Elementary.sin_imaginary, complex_sinh _ h.1 h.2]
  simp [← mul_assoc]

end QSym.AtanhCompositions

namespace QSym.Value

theorem refines_real_exp_atanh (x : Option ℝ) :
    Refines (Functions.expR.apply (Functions.atanhR.apply x))
      (mul (add (some 1) x) (inv (Functions.sqrtR.apply (add (some 1) (mul (some (-1)) (x.map (fun v => v^2))))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases hx : -1<x ∧ x<1
    · have hp : 0<1-x^2 := by nlinarith [hx.1,hx.2]
      have hn : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.2 hp).ne'
      have he := AtanhCompositions.real_exp x hx.1 hx.2
      dsimp [Functions.atanhR] at he
      simp only [div_eq_mul_inv] at he
      apply refines_of_eq
      simp [Function1.apply, Functions.expR, Functions.atanhR, Functions.sqrtR, add, mul, inv,
        hx, hp.le, hn, ← sub_eq_add_neg, he, div_eq_mul_inv]
    · intro v hv; simp [Function1.apply, Functions.atanhR, hx] at hv

theorem refines_complex_exp_atanh (z : Option ℂ) :
    Refines (Functions.expC.apply (Functions.atanhC.apply z))
      (mul (Functions.sqrtC.apply (add (some 1) z))
        (inv (Functions.sqrtC.apply (add (some 1) (mul (some (-1)) z))))) := by
  classical
  cases z with
  | none => intro v hv; cases hv
  | some z =>
    by_cases hz : z≠1 ∧ z≠-1
    · have hb : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hz.1)
      have he := AtanhCompositions.complex_exp z hz.1 hz.2
      dsimp [Functions.atanhC] at he
      simp only [div_eq_mul_inv] at he
      apply refines_of_eq
      simp [Function1.apply, Functions.expC, Functions.atanhC, Functions.sqrtC, add, mul, inv,
        hz, hb, ← sub_eq_add_neg, he, div_eq_mul_inv]
    · intro v hv; simp [Function1.apply, Functions.atanhC, hz] at hv

theorem refines_complex_cosh_atanh (z : Option ℂ) :
    Refines (Functions.coshC.apply (Functions.atanhC.apply z))
      (inv (mul (Functions.sqrtC.apply (add (some 1) z))
        (Functions.sqrtC.apply (add (some 1) (mul (some (-1)) z))))) := by
  classical
  cases z with
  | none => intro v hv; cases hv
  | some z =>
    by_cases hz : z≠1 ∧ z≠-1
    · have ha : 1+z≠0 := by intro h; apply hz.2; linear_combination h
      have hb : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hz.1)
      have he := AtanhCompositions.complex_cosh z hz.1 hz.2
      dsimp [Functions.atanhC] at he
      apply refines_of_eq
      simp [Function1.apply, Functions.coshC, Functions.atanhC, Functions.sqrtC, add, mul, inv,
        hz, ha, hb, ← sub_eq_add_neg, he]
    · intro v hv; simp [Function1.apply, Functions.atanhC, hz] at hv

theorem refines_complex_sinh_atanh (z : Option ℂ) :
    Refines (Functions.sinhC.apply (Functions.atanhC.apply z))
      (mul z (inv (mul (Functions.sqrtC.apply (add (some 1) z))
        (Functions.sqrtC.apply (add (some 1) (mul (some (-1)) z)))))) := by
  classical
  cases z with
  | none => intro v hv; cases hv
  | some z =>
    by_cases hz : z≠1 ∧ z≠-1
    · have ha : 1+z≠0 := by intro h; apply hz.2; linear_combination h
      have hb : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hz.1)
      have he := AtanhCompositions.complex_sinh z hz.1 hz.2
      dsimp [Functions.atanhC] at he
      apply refines_of_eq
      simp [Function1.apply, Functions.sinhC, Functions.atanhC, Functions.sqrtC, add, mul, inv,
        hz, ha, hb, ← sub_eq_add_neg, he]
    · intro v hv; simp [Function1.apply, Functions.atanhC, hz] at hv

theorem refines_complex_cos_atan (z : Option ℂ) :
    Refines (Functions.cosC.apply (Functions.atanC.apply z))
      (inv (mul (Functions.sqrtC.apply (add (some 1) (mul (some Complex.I) z)))
        (Functions.sqrtC.apply (add (some 1) (mul (some (-1)) (mul (some Complex.I) z)))))) := by
  classical
  cases z with
  | none => intro v hv; cases hv
  | some z =>
    by_cases hz : z≠Complex.I ∧ z≠-Complex.I
    · have hi := AtanhCompositions.imaginary_domain z hz.1 hz.2
      have ha : 1+Complex.I*z≠0 := by intro h; apply hi.2; linear_combination h
      have hb : 1-Complex.I*z≠0 := sub_ne_zero.mpr (Ne.symm hi.1)
      have he := AtanhCompositions.complex_cos z hz.1 hz.2
      dsimp [Functions.atanC] at he
      apply refines_of_eq
      simp [Function1.apply, Functions.cosC, Functions.atanC, Functions.sqrtC, add, mul, inv,
        hz, ha, hb, ← sub_eq_add_neg, he]
    · intro v hv; simp [Function1.apply, Functions.atanC, hz] at hv

theorem refines_complex_sin_atan (z : Option ℂ) :
    Refines (Functions.sinC.apply (Functions.atanC.apply z))
      (mul z (inv (mul (Functions.sqrtC.apply (add (some 1) (mul (some Complex.I) z)))
        (Functions.sqrtC.apply (add (some 1) (mul (some (-1)) (mul (some Complex.I) z))))))) := by
  classical
  cases z with
  | none => intro v hv; cases hv
  | some z =>
    by_cases hz : z≠Complex.I ∧ z≠-Complex.I
    · have hi := AtanhCompositions.imaginary_domain z hz.1 hz.2
      have ha : 1+Complex.I*z≠0 := by intro h; apply hi.2; linear_combination h
      have hb : 1-Complex.I*z≠0 := sub_ne_zero.mpr (Ne.symm hi.1)
      have he := AtanhCompositions.complex_sin z hz.1 hz.2
      dsimp [Functions.atanC] at he
      apply refines_of_eq
      simp [Function1.apply, Functions.sinC, Functions.atanC, Functions.sqrtC, add, mul, inv,
        hz, ha, hb, ← sub_eq_add_neg, he]
    · intro v hv; simp [Function1.apply, Functions.atanC, hz] at hv

end QSym.Value
