import QSym.Functions

namespace QSym.Value

theorem sin_argC (z : Option ℂ) :
    Functions.sinR.apply (Functions.argC.apply z)=
      mul (Functions.imC.apply z) (inv (Functions.absC.apply z)) := by
  classical
  cases z with
  | none => rfl
  | some z =>
    by_cases hz : z=0
    · subst z
      simp [Function1.apply, Functions.sinR, Functions.argC, Functions.imC,
        Functions.absC, inv, mul]
    · have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
      simp [Function1.apply, Functions.sinR, Functions.argC, Functions.imC,
        Functions.absC, inv, mul, hz, hn, Complex.sin_arg, div_eq_mul_inv]

theorem cos_argC (z : Option ℂ) :
    Functions.cosR.apply (Functions.argC.apply z)=
      mul (Functions.reC.apply z) (inv (Functions.absC.apply z)) := by
  classical
  cases z with
  | none => rfl
  | some z =>
    by_cases hz : z=0
    · subst z
      simp [Function1.apply, Functions.cosR, Functions.argC, Functions.reC,
        Functions.absC, inv, mul]
    · have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
      simp [Function1.apply, Functions.cosR, Functions.argC, Functions.reC,
        Functions.absC, inv, mul, hz, hn, Complex.cos_arg hz, div_eq_mul_inv]

theorem tan_argC (z : Option ℂ) :
    Functions.tanR.apply (Functions.argC.apply z)=
      mul (Functions.imC.apply z) (inv (Functions.reC.apply z)) := by
  classical
  cases z with
  | none => rfl
  | some z =>
    by_cases hz : z=0
    · subst z
      simp [Function1.apply, Functions.tanR, Functions.argC, Functions.imC,
        Functions.reC, inv, mul]
    · have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
      by_cases hr : z.re=0
      · simp [Function1.apply, Functions.tanR, Functions.argC, Functions.imC,
          Functions.reC, inv, mul, hz, hr, Complex.cos_arg hz]
      · have hc : Real.cos (Complex.arg z)≠0 := by
          rw [Complex.cos_arg hz]
          exact div_ne_zero hr hn
        simp [Function1.apply, Functions.tanR, Functions.argC, Functions.imC,
          Functions.reC, inv, mul, hz, hr, hc, Complex.tan_arg, div_eq_mul_inv]

theorem cis_argC (z : Option ℂ) :
    Functions.cisR.apply (Functions.argC.apply z)=
      mul z (inv (Functions.castRC.apply (Functions.absC.apply z))) := by
  classical
  cases z with
  | none => rfl
  | some z =>
    by_cases hz : z=0
    · subst z
      simp [Function1.apply, Functions.cisR, Functions.argC, Functions.absC,
        Functions.castRC, inv, mul]
    · have hn : (‖z‖ : ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      have hp : Complex.exp (Complex.arg z*Complex.I)=z/(‖z‖ : ℂ) := by
        apply (eq_div_iff hn).2
        simpa only [mul_comm] using Complex.norm_mul_exp_arg_mul_I z
      simp [Function1.apply, Functions.cisR, Functions.argC, Functions.absC,
        Functions.castRC, inv, mul, hz, hn, hp, div_eq_mul_inv]

end QSym.Value
