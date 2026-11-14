import QSym.SqrtProducts
import QSym.AxiomCheck
namespace QSym
#qsym_check_axioms SqrtProducts.exp_half
#qsym_check_axioms SqrtProducts.exp_half_upper
#qsym_check_axioms SqrtProducts.exp_half_lower
#qsym_check_axioms SqrtProducts.mul_exp
#qsym_check_axioms SqrtProducts.div_exp
#qsym_check_axioms SqrtProducts.mul_middle
#qsym_check_axioms SqrtProducts.mul_upper
#qsym_check_axioms SqrtProducts.mul_lower
#qsym_check_axioms SqrtProducts.div_middle
#qsym_check_axioms SqrtProducts.div_upper
#qsym_check_axioms SqrtProducts.div_lower
#qsym_check_axioms Value.refines_sqrt_mul_middle
#qsym_check_axioms Value.refines_sqrt_mul_upper
#qsym_check_axioms Value.refines_sqrt_mul_lower
#qsym_check_axioms Value.refines_sqrt_div_middle
#qsym_check_axioms Value.refines_sqrt_div_upper
#qsym_check_axioms Value.refines_sqrt_div_lower
#qsym_check_axioms Value.refines_sqrt_mul_pi
#qsym_check_axioms Value.refines_sqrt_mul_neg_pi
#qsym_check_axioms Value.refines_sqrt_div_pi
#qsym_check_axioms Value.refines_sqrt_div_neg_pi
end QSym

namespace QSym.SqrtProducts

theorem mul_positive_boundary :
    Functions.sqrtC.value Complex.I*Functions.sqrtC.value Complex.I=Functions.sqrtC.value (-1) := by
  simpa using mul_middle Complex.I Complex.I (by simp) (by simp) (by simp only [Complex.arg_I, Complex.arg_neg_I]; linarith [Real.pi_pos]) (by simp only [Complex.arg_I, Complex.arg_neg_I]; linarith)

theorem mul_negative_boundary :
    Functions.sqrtC.value (-Complex.I)*Functions.sqrtC.value (-Complex.I)=-Functions.sqrtC.value (-1) := by
  simpa using mul_lower (-Complex.I) (-Complex.I) (by simp) (by simp) (by simp only [Complex.arg_I, Complex.arg_neg_I]; linarith)

theorem div_positive_boundary :
    Functions.sqrtC.value Complex.I/Functions.sqrtC.value (-Complex.I)=Functions.sqrtC.value (-1) := by
  simpa using div_middle Complex.I (-Complex.I) (by simp) (by simp) (by simp only [Complex.arg_I, Complex.arg_neg_I]; linarith [Real.pi_pos]) (by simp only [Complex.arg_I, Complex.arg_neg_I]; linarith)

theorem div_negative_boundary :
    Functions.sqrtC.value (-Complex.I)/Functions.sqrtC.value Complex.I=-Functions.sqrtC.value (-1) := by
  simpa using div_lower (-Complex.I) Complex.I (by simp) (by simp) (by simp only [Complex.arg_I, Complex.arg_neg_I]; linarith)

theorem zero_denominator :
    Value.mul (Functions.sqrtC.apply (some Complex.I)) (Value.inv (Functions.sqrtC.apply (some 0)))=none := by
  norm_num [Value.mul, Value.inv, Function1.apply, Functions.sqrtC]

theorem undefined_product :
    Value.mul (Functions.sqrtC.apply (some 0)) (Functions.sqrtC.apply none)=none := by
  simp [Value.mul, Function1.apply]

theorem false_mask_pole :
    Value.mask (some false) (Value.mul (Functions.sqrtC.apply (some Complex.I))
      (Value.inv (Functions.sqrtC.apply (some 0))))=some 0 := rfl

theorem defined_quotient (z w : Option ℂ) :
    Value.Defined (Value.mul (Functions.sqrtC.apply z) (Value.inv (Functions.sqrtC.apply w))) ↔
      Value.Defined (Functions.sqrtC.apply (Value.mul z (Value.inv w))) := by
  cases z <;> cases w <;>
    simp [Value.Defined, Value.mul, Value.inv, Function1.apply, Functions.sqrtC, Complex.cpow_eq_zero_iff] <;> split_ifs <;> simp_all

#qsym_check_axioms mul_positive_boundary
#qsym_check_axioms mul_negative_boundary
#qsym_check_axioms div_positive_boundary
#qsym_check_axioms div_negative_boundary
#qsym_check_axioms zero_denominator
#qsym_check_axioms undefined_product
#qsym_check_axioms false_mask_pole
#qsym_check_axioms defined_quotient
end QSym.SqrtProducts
