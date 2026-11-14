import QSym.InverseSymmetry
import QSym.AxiomCheck

namespace QSym
#qsym_check_axioms InverseSymmetry.atanh_neg
#qsym_check_axioms InverseSymmetry.atan_neg
#qsym_check_axioms InverseSymmetry.atanh_neg_domain
#qsym_check_axioms InverseSymmetry.atan_neg_domain
#qsym_check_axioms InverseSymmetry.atanh_conj_domain
#qsym_check_axioms InverseSymmetry.atan_conj_domain
#qsym_check_axioms InverseSymmetry.atanh_conj
#qsym_check_axioms InverseSymmetry.atan_conj
#qsym_check_axioms Value.inverse_neg
#qsym_check_axioms Value.inverse_neg_reverse
#qsym_check_axioms Value.inverse_conj
#qsym_check_axioms Value.refines_atanh_neg
#qsym_check_axioms Value.refines_atan_neg
#qsym_check_axioms Value.refines_atanh_negative_literal
#qsym_check_axioms Value.refines_atan_negative_literal
#qsym_check_axioms Value.refines_atanh_conj_im
#qsym_check_axioms Value.refines_atanh_conj_re
#qsym_check_axioms Value.refines_atan_conj_re
#qsym_check_axioms Value.refines_atan_conj_im
end QSym

namespace QSym.InverseSymmetry

theorem atanh_two_im : (Functions.atanhC.value 2).im = -Real.pi/2 := by
  norm_num [Functions.atanhC, Complex.div_im, Complex.log_im]

theorem atanh_conj_cut :
    (starRingEnd ℂ) (Functions.atanhC.value 2) ≠ Functions.atanhC.value ((starRingEnd ℂ) 2) := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_ofNat, Complex.conj_im, atanh_two_im] at hi
  linarith [Real.pi_pos]

theorem atan_two_I_re : (Functions.atanC.value (2*Complex.I)).re = Real.pi/2 := by
  rw [AtanhCompositions.atan_atanh]
  have h : Complex.I*(2*Complex.I) = -(2:ℂ) := by linear_combination 2*Complex.I_sq
  rw [h, atanh_neg]
  simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_im, zero_mul, one_mul, zero_sub, neg_neg, atanh_two_im]
  ring

theorem atan_conj_cut :
    (starRingEnd ℂ) (Functions.atanC.value (2*Complex.I)) ≠ Functions.atanC.value ((starRingEnd ℂ) (2*Complex.I)) := by
  intro h
  have hi := congrArg Complex.re h
  have hc : (starRingEnd ℂ) (2*Complex.I)= -(2*Complex.I) := by simp [map_ofNat]
  rw [hc, atan_neg] at hi
  simp only [Complex.conj_re, Complex.neg_re, atan_two_I_re] at hi
  linarith [Real.pi_pos]
#qsym_check_axioms atanh_two_im
#qsym_check_axioms atanh_conj_cut
#qsym_check_axioms atan_two_I_re
#qsym_check_axioms atan_conj_cut
end QSym.InverseSymmetry
