import QSym.SqrtBranches
import QSym.AxiomCheck
namespace QSym
#qsym_check_axioms SqrtBranches.conj_off_cut
#qsym_check_axioms SqrtBranches.conj_on_cut
#qsym_check_axioms SqrtBranches.inv_off_cut
#qsym_check_axioms SqrtBranches.inv_on_cut
#qsym_check_axioms SqrtBranches.sqrt_ne_zero
#qsym_check_axioms Value.sqrt_conj_off_cut
#qsym_check_axioms Value.sqrt_inv_off_cut
#qsym_check_axioms Value.sqrt_inv_on_cut
#qsym_check_axioms Value.refines_sqrt_conj_re
#qsym_check_axioms Value.refines_sqrt_conj_im
#qsym_check_axioms Value.refines_sqrt_inv_re
#qsym_check_axioms Value.refines_sqrt_inv_im
#qsym_check_axioms Value.refines_sqrt_inv_cut
end QSym

namespace QSym.SqrtBranches

theorem negative_one_sqrt : Functions.sqrtC.value (-1)=Complex.I := by
  simpa [Functions.sqrtC, one_div] using Elementary.sqrt_real_negative (z:=(-1)) (by norm_num) (by norm_num)

theorem negative_one_conj_boundary :
    (starRingEnd ℂ) (Functions.sqrtC.value (-1)) ≠ Functions.sqrtC.value ((starRingEnd ℂ) (-1)) := by
  rw [show (starRingEnd ℂ) (-1)=(-1:ℂ) by simp, negative_one_sqrt]
  intro h
  have := congrArg Complex.im h
  norm_num at this

theorem negative_one_inv_boundary :
    Functions.sqrtC.value ((-1:ℂ)⁻¹) ≠ (Functions.sqrtC.value (-1))⁻¹ := by
  rw [inv_neg, inv_one, negative_one_sqrt]
  intro h
  have := congrArg Complex.im h
  norm_num [Complex.inv_im] at this

theorem zero_sqrt_defined : Functions.sqrtC.apply (some 0)=some 0 := by
  norm_num [Function1.apply, Functions.sqrtC]

theorem zero_inv_undefined : Functions.sqrtC.apply (Value.inv (some 0))=none := by
  norm_num [Function1.apply, Value.inv]

theorem undefined_conj : Value.conj (Functions.sqrtC.apply none)=none := rfl

#qsym_check_axioms negative_one_sqrt
#qsym_check_axioms negative_one_conj_boundary
#qsym_check_axioms negative_one_inv_boundary
#qsym_check_axioms zero_sqrt_defined
#qsym_check_axioms zero_inv_undefined
#qsym_check_axioms undefined_conj
end QSym.SqrtBranches
