import QSym.ZeroPowers
import QSym.AxiomCheck

namespace QSym

#qsym_check_axioms ZeroPowers.powNN
#qsym_check_axioms ZeroPowers.powZN
#qsym_check_axioms ZeroPowers.powQN
#qsym_check_axioms ZeroPowers.powRN
#qsym_check_axioms ZeroPowers.powCN
#qsym_check_axioms ZeroPowers.powQZ
#qsym_check_axioms ZeroPowers.powRZ
#qsym_check_axioms ZeroPowers.powCZ
#qsym_check_axioms ZeroPowers.powQZ_positive
#qsym_check_axioms ZeroPowers.powRZ_positive
#qsym_check_axioms ZeroPowers.powCZ_positive
#qsym_check_axioms ZeroPowers.powerR
#qsym_check_axioms ZeroPowers.powerC

theorem zero_power_negative_rational : Functions.powQZ.apply (some 0) (some (-1))=none := by
  norm_num [Function2.apply, Functions.powQZ]
theorem zero_power_negative_real : Functions.powRZ.apply (some 0) (some (-1))=none := by
  norm_num [Function2.apply, Functions.powRZ]
theorem zero_power_negative_complex : Functions.powCZ.apply (some 0) (some (-1))=none := by
  norm_num [Function2.apply, Functions.powCZ]
theorem zero_power_negative_rpow : Functions.powerR.apply (some 0) (some (-1))=none := by
  norm_num [Function2.apply, Functions.powerR]
theorem zero_power_negative_cpow : Functions.powerC.apply (some 0) (some (-1))=none := by
  norm_num [Function2.apply, Functions.powerC]
theorem zero_power_imaginary : Functions.powerC.apply (some 0) (some Complex.I)=none := by
  simp [Function2.apply, Functions.powerC]
theorem zero_power_positive_nonreal :
    Functions.powerC.apply (some 0) (some (1+Complex.I))=none := by
  norm_num [Function2.apply, Functions.powerC, Complex.ext_iff]
theorem zero_power_undefined : Functions.powNN.apply (some 0) none=none := rfl
theorem zero_power_zero : Functions.powNN.apply (some 0) (some 0)=some 1 := by
  simp [Function2.apply, Functions.powNN]
theorem zero_power_false_mask :
    Value.mask (some false) (Functions.powerC.apply (some 0) (some Complex.I))=some 0 := rfl
theorem zero_power_true_mask :
    Value.mask (some true) (Functions.powerC.apply (some 0) (some Complex.I))=none :=
  zero_power_imaginary

#qsym_check_axioms zero_power_negative_rational
#qsym_check_axioms zero_power_negative_real
#qsym_check_axioms zero_power_negative_complex
#qsym_check_axioms zero_power_negative_rpow
#qsym_check_axioms zero_power_negative_cpow
#qsym_check_axioms zero_power_imaginary
#qsym_check_axioms zero_power_positive_nonreal
#qsym_check_axioms zero_power_undefined
#qsym_check_axioms zero_power_zero
#qsym_check_axioms zero_power_false_mask
#qsym_check_axioms zero_power_true_mask

end QSym
