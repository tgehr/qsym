import QSym.TrigMagnitudes
import QSym.AxiomCheck

namespace QSym
#qsym_check_axioms TrigMagnitudes.normSq_sin
#qsym_check_axioms TrigMagnitudes.normSq_cos
#qsym_check_axioms TrigMagnitudes.normSq_sinh
#qsym_check_axioms TrigMagnitudes.normSq_cosh
#qsym_check_axioms TrigMagnitudes.norm_sin
#qsym_check_axioms TrigMagnitudes.norm_cos
#qsym_check_axioms TrigMagnitudes.norm_sinh
#qsym_check_axioms TrigMagnitudes.norm_cosh
#qsym_check_axioms Value.norm_sin
#qsym_check_axioms Value.norm_cos
#qsym_check_axioms Value.norm_sinh
#qsym_check_axioms Value.norm_cosh
#qsym_check_axioms Value.norm_tan
#qsym_check_axioms Value.norm_tanh
end QSym

namespace QSym.TrigMagnitudes

theorem sin_undefined : Functions.absC.apply (Functions.sinC.apply none)=none := by
  simp [Function1.apply]
theorem tan_undefined : Functions.absC.apply (Functions.tanC.apply none)=none := by
  simp [Function1.apply]
theorem tan_pole :
    Functions.absC.apply (Functions.tanC.apply (some ((Real.pi/2 : ℝ) : ℂ)))=none := by
  norm_num [Function1.apply, Functions.absC, Functions.tanC, Complex.ofReal_div]
theorem tanh_pole :
    Functions.absC.apply (Functions.tanhC.apply (some (Complex.I*((Real.pi/2 : ℝ) : ℂ))))=none := by
  norm_num [Function1.apply, Functions.absC, Functions.tanhC, Elementary.cosh_imaginary, Complex.ofReal_div]
theorem false_mask_pole :
    Value.mask (some false) (Functions.absC.apply (Functions.tanC.apply (some ((Real.pi/2 : ℝ) : ℂ))))=some 0 := rfl
theorem true_mask_pole :
    Value.mask (some true) (Functions.absC.apply (Functions.tanhC.apply (some (Complex.I*((Real.pi/2 : ℝ) : ℂ)))))=none := tanh_pole
theorem undefined_mask (z : Option ℂ) :
    Value.mask none (Functions.absC.apply (Functions.sinC.apply z))=none := rfl
theorem cosh_zero : Functions.absC.apply (Functions.coshC.apply (some 0))=some 1 := by
  norm_num [Function1.apply, Functions.absC, Functions.coshC]
#qsym_check_axioms sin_undefined
#qsym_check_axioms tan_undefined
#qsym_check_axioms tan_pole
#qsym_check_axioms tanh_pole
#qsym_check_axioms false_mask_pole
#qsym_check_axioms true_mask_pole
#qsym_check_axioms undefined_mask
#qsym_check_axioms cosh_zero
end QSym.TrigMagnitudes
