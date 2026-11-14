import QSym.RefinementBase
import QSym.Elementary

namespace QSym.TrigMagnitudes

theorem normSq_sin (z : ℂ) :
    Complex.normSq (Complex.sin z)=Real.sin z.re^2+Real.sinh z.im^2 := by
  simp only [Complex.normSq_apply, Elementary.sin_re, Elementary.sin_im]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq_sub_sinh_sq z.im,
    mul_nonneg (sq_nonneg (Real.sin z.re)) (sq_nonneg (Real.sinh z.im))]

theorem normSq_cos (z : ℂ) :
    Complex.normSq (Complex.cos z)=Real.cos z.re^2+Real.sinh z.im^2 := by
  simp only [Complex.normSq_apply, Elementary.cos_re, Elementary.cos_im]
  nlinarith [Real.sin_sq_add_cos_sq z.re, Real.cosh_sq_sub_sinh_sq z.im,
    mul_nonneg (sq_nonneg (Real.cos z.re)) (sq_nonneg (Real.sinh z.im))]

theorem normSq_sinh (z : ℂ) :
    Complex.normSq (Complex.sinh z)=Real.sinh z.re^2+Real.sin z.im^2 := by
  simp only [Complex.normSq_apply, Elementary.sinh_re, Elementary.sinh_im]
  nlinarith [Real.sin_sq_add_cos_sq z.im, Real.cosh_sq_sub_sinh_sq z.re,
    mul_nonneg (sq_nonneg (Real.sinh z.re)) (sq_nonneg (Real.sin z.im))]

theorem normSq_cosh (z : ℂ) :
    Complex.normSq (Complex.cosh z)=Real.sinh z.re^2+Real.cos z.im^2 := by
  simp only [Complex.normSq_apply, Elementary.cosh_re, Elementary.cosh_im]
  nlinarith [Real.sin_sq_add_cos_sq z.im, Real.cosh_sq_sub_sinh_sq z.re,
    mul_nonneg (sq_nonneg (Real.sinh z.re)) (sq_nonneg (Real.cos z.im))]

theorem norm_sin (z : ℂ) :
    ‖Complex.sin z‖=Real.sqrt (Real.sin z.re^2+Real.sinh z.im^2) := by
  rw [Complex.norm_def, normSq_sin]

theorem norm_cos (z : ℂ) :
    ‖Complex.cos z‖=Real.sqrt (Real.cos z.re^2+Real.sinh z.im^2) := by
  rw [Complex.norm_def, normSq_cos]

theorem norm_sinh (z : ℂ) :
    ‖Complex.sinh z‖=Real.sqrt (Real.sinh z.re^2+Real.sin z.im^2) := by
  rw [Complex.norm_def, normSq_sinh]

theorem norm_cosh (z : ℂ) :
    ‖Complex.cosh z‖=Real.sqrt (Real.sinh z.re^2+Real.cos z.im^2) := by
  rw [Complex.norm_def, normSq_cosh]

end QSym.TrigMagnitudes

namespace QSym.Value

theorem norm_sin (z : Option ℂ) :
    Functions.absC.apply (Functions.sinC.apply z)=Functions.sqrtR.apply
      (add ((Functions.sinR.apply (Functions.reC.apply z)).map (fun x => x^2))
        ((Functions.sinhR.apply (Functions.imC.apply z)).map (fun x => x^2))) := by
  classical
  cases z <;> simp [Function1.apply, Functions.absC, Functions.sinC,
    Functions.sinR, Functions.sinhR, Functions.reC, Functions.imC, Functions.sqrtR,
    add, TrigMagnitudes.norm_sin]; positivity

theorem norm_cos (z : Option ℂ) :
    Functions.absC.apply (Functions.cosC.apply z)=Functions.sqrtR.apply
      (add ((Functions.cosR.apply (Functions.reC.apply z)).map (fun x => x^2))
        ((Functions.sinhR.apply (Functions.imC.apply z)).map (fun x => x^2))) := by
  classical
  cases z <;> simp [Function1.apply, Functions.absC, Functions.cosC,
    Functions.cosR, Functions.sinhR, Functions.reC, Functions.imC, Functions.sqrtR,
    add, TrigMagnitudes.norm_cos]; positivity

theorem norm_sinh (z : Option ℂ) :
    Functions.absC.apply (Functions.sinhC.apply z)=Functions.sqrtR.apply
      (add ((Functions.sinhR.apply (Functions.reC.apply z)).map (fun x => x^2))
        ((Functions.sinR.apply (Functions.imC.apply z)).map (fun x => x^2))) := by
  classical
  cases z <;> simp [Function1.apply, Functions.absC, Functions.sinhC,
    Functions.sinhR, Functions.sinR, Functions.reC, Functions.imC, Functions.sqrtR,
    add, TrigMagnitudes.norm_sinh]; positivity

theorem norm_cosh (z : Option ℂ) :
    Functions.absC.apply (Functions.coshC.apply z)=Functions.sqrtR.apply
      (add ((Functions.sinhR.apply (Functions.reC.apply z)).map (fun x => x^2))
        ((Functions.cosR.apply (Functions.imC.apply z)).map (fun x => x^2))) := by
  classical
  cases z <;> simp [Function1.apply, Functions.absC, Functions.coshC,
    Functions.sinhR, Functions.cosR, Functions.reC, Functions.imC, Functions.sqrtR,
    add, TrigMagnitudes.norm_cosh]; positivity

theorem norm_tan (z : Option ℂ) :
    Functions.absC.apply (Functions.tanC.apply z)=
      mul (Functions.absC.apply (Functions.sinC.apply z))
        (inv (Functions.absC.apply (Functions.cosC.apply z))) := by
  classical
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    by_cases h : Complex.cos z=0
    · simp [Function1.apply, Functions.absC, Functions.tanC, Functions.sinC,
        Functions.cosC, mul, inv, h]
    · simp [Function1.apply, Functions.absC, Functions.tanC, Functions.sinC,
        Functions.cosC, mul, inv, h, Complex.tan_eq_sin_div_cos, norm_div, div_eq_mul_inv]

theorem norm_tanh (z : Option ℂ) :
    Functions.absC.apply (Functions.tanhC.apply z)=
      mul (Functions.absC.apply (Functions.sinhC.apply z))
        (inv (Functions.absC.apply (Functions.coshC.apply z))) := by
  classical
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    by_cases h : Complex.cosh z=0
    · simp [Function1.apply, Functions.absC, Functions.tanhC, Functions.sinhC,
        Functions.coshC, mul, inv, h]
    · simp [Function1.apply, Functions.absC, Functions.tanhC, Functions.sinhC,
        Functions.coshC, mul, inv, h, Complex.tanh_eq_sinh_div_cosh, norm_div, div_eq_mul_inv]

end QSym.Value
