import QSym.RefinementBase
import QSym.Elementary

namespace QSym.SqrtProducts

theorem exp_half (t : ℂ) (hl : -Real.pi<t.im) (hu : t.im≤Real.pi) :
    Functions.sqrtC.value (Complex.exp t)=Complex.exp (t/2) := by
  simp only [Functions.sqrtC, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero t),
    Complex.log_exp hl hu, one_div, div_eq_mul_inv, one_mul]

theorem exp_half_upper (t : ℂ) (hl : Real.pi<t.im) (hu : t.im≤3*Real.pi) :
    Functions.sqrtC.value (Complex.exp t)= -Complex.exp (t/2) := by
  have hl' : -Real.pi<(t-2*Real.pi*Complex.I).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] ; norm_num at *; linarith
  have hu' : (t-2*Real.pi*Complex.I).im≤Real.pi := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] ; norm_num at *; linarith
  have he : Complex.exp (t-2*Real.pi*Complex.I)=Complex.exp t := by
    rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  rw [← he, exp_half _ hl' hu']
  convert Complex.exp_sub_pi_mul_I (t/2) using 1 <;> congr 1 <;> ring

theorem exp_half_lower (t : ℂ) (hl : -3*Real.pi<t.im) (hu : t.im≤ -Real.pi) :
    Functions.sqrtC.value (Complex.exp t)= -Complex.exp (t/2) := by
  have hl' : -Real.pi<(t+2*Real.pi*Complex.I).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] ; norm_num at *; linarith
  have hu' : (t+2*Real.pi*Complex.I).im≤Real.pi := by
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] ; norm_num at *; linarith
  have he : Complex.exp (t+2*Real.pi*Complex.I)=Complex.exp t := by
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [← he, exp_half _ hl' hu']
  convert Complex.exp_add_pi_mul_I (t/2) using 1 <;> congr 1 <;> ring

theorem mul_exp (z w : ℂ) (hz : z≠0) (hw : w≠0) :
    Functions.sqrtC.value z*Functions.sqrtC.value w=
      Complex.exp ((Complex.log z+Complex.log w)/2) := by
  simp only [Functions.sqrtC, Complex.cpow_def_of_ne_zero hz,
    Complex.cpow_def_of_ne_zero hw, div_eq_mul_inv, one_div, one_mul, add_mul, Complex.exp_add]

theorem div_exp (z w : ℂ) (hz : z≠0) (hw : w≠0) :
    Functions.sqrtC.value z/Functions.sqrtC.value w=
      Complex.exp ((Complex.log z-Complex.log w)/2) := by
  simp only [Functions.sqrtC, Complex.cpow_def_of_ne_zero hz,
    Complex.cpow_def_of_ne_zero hw, div_eq_mul_inv, one_div, one_mul, sub_mul, Complex.exp_sub, div_eq_mul_inv]

theorem mul_middle (z w : ℂ) (hz : z≠0) (hw : w≠0)
    (hl : -Real.pi<Complex.arg z+Complex.arg w) (hu : Complex.arg z+Complex.arg w≤Real.pi) :
    Functions.sqrtC.value z*Functions.sqrtC.value w=Functions.sqrtC.value (z*w) := by
  have he := exp_half (Complex.log z+Complex.log w)
    (by simpa [Complex.log_im] using hl) (by simpa [Complex.log_im] using hu)
  rw [Complex.exp_add, Complex.exp_log hz, Complex.exp_log hw] at he
  rw [mul_exp z w hz hw, he]

theorem mul_upper (z w : ℂ) (hz : z≠0) (hw : w≠0)
    (h : Real.pi<Complex.arg z+Complex.arg w) :
    Functions.sqrtC.value z*Functions.sqrtC.value w= -Functions.sqrtC.value (z*w) := by
  have hu : (Complex.log z+Complex.log w).im≤3*Real.pi := by
    simp only [Complex.add_im, Complex.log_im]
    linarith [Complex.arg_le_pi z, Complex.arg_le_pi w, Real.pi_pos]
  have he := exp_half_upper (Complex.log z+Complex.log w) (by simpa [Complex.log_im] using h) hu
  rw [Complex.exp_add, Complex.exp_log hz, Complex.exp_log hw] at he
  rw [mul_exp z w hz hw, he, neg_neg]

theorem mul_lower (z w : ℂ) (hz : z≠0) (hw : w≠0)
    (h : Complex.arg z+Complex.arg w≤ -Real.pi) :
    Functions.sqrtC.value z*Functions.sqrtC.value w= -Functions.sqrtC.value (z*w) := by
  have hl : -3*Real.pi<(Complex.log z+Complex.log w).im := by
    simp only [Complex.add_im, Complex.log_im]
    linarith [Complex.neg_pi_lt_arg z, Complex.neg_pi_lt_arg w, Real.pi_pos]
  have he := exp_half_lower (Complex.log z+Complex.log w) hl (by simpa [Complex.log_im] using h)
  rw [Complex.exp_add, Complex.exp_log hz, Complex.exp_log hw] at he
  rw [mul_exp z w hz hw, he, neg_neg]

theorem div_middle (z w : ℂ) (hz : z≠0) (hw : w≠0)
    (hl : -Real.pi<Complex.arg z-Complex.arg w) (hu : Complex.arg z-Complex.arg w≤Real.pi) :
    Functions.sqrtC.value z/Functions.sqrtC.value w=Functions.sqrtC.value (z/w) := by
  have he := exp_half (Complex.log z-Complex.log w) (by simpa [Complex.log_im] using hl) (by simpa [Complex.log_im] using hu)
  rw [Complex.exp_sub, Complex.exp_log hz, Complex.exp_log hw] at he
  rw [div_exp z w hz hw, he]

theorem div_upper (z w : ℂ) (hz : z≠0) (hw : w≠0)
    (h : Real.pi<Complex.arg z-Complex.arg w) :
    Functions.sqrtC.value z/Functions.sqrtC.value w= -Functions.sqrtC.value (z/w) := by
  have hu : (Complex.log z-Complex.log w).im≤3*Real.pi := by
    simp only [Complex.sub_im, Complex.log_im]
    linarith [Complex.arg_le_pi z, Complex.neg_pi_lt_arg w, Real.pi_pos]
  have he := exp_half_upper (Complex.log z-Complex.log w) (by simpa [Complex.log_im] using h) hu
  rw [Complex.exp_sub, Complex.exp_log hz, Complex.exp_log hw] at he
  rw [div_exp z w hz hw, he, neg_neg]

theorem div_lower (z w : ℂ) (hz : z≠0) (hw : w≠0)
    (h : Complex.arg z-Complex.arg w≤ -Real.pi) :
    Functions.sqrtC.value z/Functions.sqrtC.value w= -Functions.sqrtC.value (z/w) := by
  have hl : -3*Real.pi<(Complex.log z-Complex.log w).im := by
    simp only [Complex.sub_im, Complex.log_im]
    linarith [Complex.neg_pi_lt_arg z, Complex.arg_le_pi w, Real.pi_pos]
  have he := exp_half_lower (Complex.log z-Complex.log w) hl (by simpa [Complex.log_im] using h)
  rw [Complex.exp_sub, Complex.exp_log hz, Complex.exp_log hw] at he
  rw [div_exp z w hz hw, he, neg_neg]

end QSym.SqrtProducts

namespace QSym.Value

theorem refines_sqrt_mul_middle (z w : Option ℂ)
    (hl : Refines (lt (mul (some (-1)) (some Functions.pi)) (add (Functions.argC.apply z) (Functions.argC.apply w))) (some true))
    (hu : Refines (le (add (Functions.argC.apply z) (Functions.argC.apply w)) (some Functions.pi)) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (Functions.sqrtC.apply w)) (Functions.sqrtC.apply (mul z w)) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hz : z=0
      · subst z; norm_num [Function1.apply, Functions.sqrtC, mul]
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul]
      have he := SqrtProducts.mul_middle z w hz hw (by simpa [Refines, Function1.apply, Functions.argC, Functions.pi, lt, le, add, mul, hz, hw, sub_eq_add_neg] using hl) (by simpa [Refines, Function1.apply, Functions.argC, Functions.pi, lt, le, add, mul, hz, hw, sub_eq_add_neg] using hu)
      simpa [Function1.apply, Functions.sqrtC, mul] using congrArg some he

theorem refines_sqrt_mul_upper (z w : Option ℂ)
    (h : Refines (lt (some Functions.pi) (add (Functions.argC.apply z) (Functions.argC.apply w))) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (Functions.sqrtC.apply w)) (mul (some (-1)) (Functions.sqrtC.apply (mul z w))) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hz : z=0
      · subst z; norm_num [Function1.apply, Functions.sqrtC, mul]
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul]
      have he := SqrtProducts.mul_upper z w hz hw (by simpa [Refines, Function1.apply, Functions.argC, Functions.pi, lt, le, add, mul, hz, hw, sub_eq_add_neg] using h)
      simpa [Function1.apply, Functions.sqrtC, mul] using congrArg some he

theorem refines_sqrt_mul_lower (z w : Option ℂ)
    (h : Refines (le (add (Functions.argC.apply z) (Functions.argC.apply w)) (mul (some (-1)) (some Functions.pi))) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (Functions.sqrtC.apply w)) (mul (some (-1)) (Functions.sqrtC.apply (mul z w))) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hz : z=0
      · subst z; norm_num [Function1.apply, Functions.sqrtC, mul]
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul]
      have he := SqrtProducts.mul_lower z w hz hw (by simpa [Refines, Function1.apply, Functions.argC, Functions.pi, lt, le, add, mul, hz, hw, sub_eq_add_neg] using h)
      simpa [Function1.apply, Functions.sqrtC, mul] using congrArg some he

theorem refines_sqrt_div_middle (z w : Option ℂ)
    (hl : Refines (lt (mul (some (-1)) (some Functions.pi)) (add (Functions.argC.apply z) (mul (some (-1)) (Functions.argC.apply w)))) (some true))
    (hu : Refines (le (add (Functions.argC.apply z) (mul (some (-1)) (Functions.argC.apply w))) (some Functions.pi)) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (inv (Functions.sqrtC.apply w))) (Functions.sqrtC.apply (mul z (inv w))) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul, inv]
      have hs : Functions.sqrtC.value w≠0 := by
        simpa [Functions.sqrtC, Complex.cpow_eq_zero_iff] using hw
      by_cases hz : z=0
      · subst z; simp [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs]
      have he := SqrtProducts.div_middle z w hz hw (by simpa [Refines, Function1.apply, Functions.argC, Functions.pi, lt, le, add, mul, hz, hw, sub_eq_add_neg] using hl) (by simpa [Refines, Function1.apply, Functions.argC, Functions.pi, lt, le, add, mul, hz, hw, sub_eq_add_neg] using hu)
      simpa [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs, div_eq_mul_inv] using congrArg some he

theorem refines_sqrt_div_upper (z w : Option ℂ)
    (h : Refines (lt (some Functions.pi) (add (Functions.argC.apply z) (mul (some (-1)) (Functions.argC.apply w)))) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (inv (Functions.sqrtC.apply w))) (mul (some (-1)) (Functions.sqrtC.apply (mul z (inv w)))) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul, inv]
      have hs : Functions.sqrtC.value w≠0 := by
        simpa [Functions.sqrtC, Complex.cpow_eq_zero_iff] using hw
      by_cases hz : z=0
      · subst z; simp [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs]
      have he := SqrtProducts.div_upper z w hz hw (by simpa [Refines, Function1.apply, Functions.argC, Functions.pi, lt, le, add, mul, hz, hw, sub_eq_add_neg] using h)
      simpa [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs, div_eq_mul_inv] using congrArg some he

theorem refines_sqrt_div_lower (z w : Option ℂ)
    (h : Refines (le (add (Functions.argC.apply z) (mul (some (-1)) (Functions.argC.apply w))) (mul (some (-1)) (some Functions.pi))) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (inv (Functions.sqrtC.apply w))) (mul (some (-1)) (Functions.sqrtC.apply (mul z (inv w)))) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul, inv]
      have hs : Functions.sqrtC.value w≠0 := by
        simpa [Functions.sqrtC, Complex.cpow_eq_zero_iff] using hw
      by_cases hz : z=0
      · subst z; simp [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs]
      have he := SqrtProducts.div_lower z w hz hw (by simpa [Refines, Function1.apply, Functions.argC, Functions.pi, lt, le, add, mul, hz, hw, sub_eq_add_neg] using h)
      simpa [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs, div_eq_mul_inv] using congrArg some he

theorem refines_sqrt_mul_pi (z w : Option ℂ)
    (h : Refines (not (nonzero (add (add (Functions.argC.apply z) (Functions.argC.apply w)) (mul (some (-1)) (some Functions.pi))))) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (Functions.sqrtC.apply w)) (Functions.sqrtC.apply (mul z w)) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hz : z=0
      · subst z; norm_num [Function1.apply, Functions.sqrtC, mul]
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul]
      have ha : Complex.arg z+Complex.arg w=Real.pi := by
        have hh : (Complex.arg z+Complex.arg w)-Real.pi=0 := by
          simpa [Refines, Function1.apply, Functions.argC, Functions.pi, not, nonzero,
            add, mul, hz, hw, sub_eq_add_neg] using h
        linarith
      have he := SqrtProducts.mul_middle z w hz hw (by rw [ha]; linarith [Real.pi_pos]) (by rw [ha])
      simpa [Function1.apply, Functions.sqrtC, mul] using congrArg some he

theorem refines_sqrt_mul_neg_pi (z w : Option ℂ)
    (h : Refines (not (nonzero (add (add (Functions.argC.apply z) (Functions.argC.apply w)) (mul (some (-1)) (mul (some (-1)) (some Functions.pi)))))) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (Functions.sqrtC.apply w)) (mul (some (-1)) (Functions.sqrtC.apply (mul z w))) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hz : z=0
      · subst z; norm_num [Function1.apply, Functions.sqrtC, mul]
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul]
      have ha : Complex.arg z+Complex.arg w=-Real.pi := by
        have hh : (Complex.arg z+Complex.arg w)+Real.pi=0 := by
          simpa [Refines, Function1.apply, Functions.argC, Functions.pi, not, nonzero,
            add, mul, hz, hw, sub_eq_add_neg] using h
        linarith
      have he := SqrtProducts.mul_lower z w hz hw (by rw [ha])
      simpa [Function1.apply, Functions.sqrtC, mul] using congrArg some he

theorem refines_sqrt_div_pi (z w : Option ℂ)
    (h : Refines (not (nonzero (add (add (Functions.argC.apply z) (mul (some (-1)) (Functions.argC.apply w))) (mul (some (-1)) (some Functions.pi))))) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (inv (Functions.sqrtC.apply w))) (Functions.sqrtC.apply (mul z (inv w))) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul, inv]
      have hs : Functions.sqrtC.value w≠0 := by
        simpa [Functions.sqrtC, Complex.cpow_eq_zero_iff] using hw
      by_cases hz : z=0
      · subst z; simp [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs]
      have ha : Complex.arg z-Complex.arg w=Real.pi := by
        have hh : (Complex.arg z-Complex.arg w)-Real.pi=0 := by
          simpa [Refines, Function1.apply, Functions.argC, Functions.pi, not, nonzero,
            add, mul, hz, hw, sub_eq_add_neg] using h
        linarith
      have he := SqrtProducts.div_middle z w hz hw (by rw [ha]; linarith [Real.pi_pos]) (by rw [ha])
      simpa [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs, div_eq_mul_inv] using congrArg some he

theorem refines_sqrt_div_neg_pi (z w : Option ℂ)
    (h : Refines (not (nonzero (add (add (Functions.argC.apply z) (mul (some (-1)) (Functions.argC.apply w))) (mul (some (-1)) (mul (some (-1)) (some Functions.pi)))))) (some true)) :
    Refines (mul (Functions.sqrtC.apply z) (inv (Functions.sqrtC.apply w))) (mul (some (-1)) (Functions.sqrtC.apply (mul z (inv w)))) := by
  apply refines_of_eq
  cases z with
  | none => simp [Function1.apply, mul, inv]
  | some z =>
    cases w with
    | none => simp [Function1.apply, mul, inv]
    | some w =>
      by_cases hw : w=0
      · subst w; norm_num [Function1.apply, Functions.sqrtC, mul, inv]
      have hs : Functions.sqrtC.value w≠0 := by
        simpa [Functions.sqrtC, Complex.cpow_eq_zero_iff] using hw
      by_cases hz : z=0
      · subst z; simp [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs]
      have ha : Complex.arg z-Complex.arg w=-Real.pi := by
        have hh : (Complex.arg z-Complex.arg w)+Real.pi=0 := by
          simpa [Refines, Function1.apply, Functions.argC, Functions.pi, not, nonzero,
            add, mul, hz, hw, sub_eq_add_neg] using h
        linarith
      have he := SqrtProducts.div_lower z w hz hw (by rw [ha])
      simpa [Function1.apply, Functions.sqrtC, mul, inv, hw, hs, show w^(1/2:ℂ)≠0 from hs, div_eq_mul_inv] using congrArg some he

end QSym.Value
