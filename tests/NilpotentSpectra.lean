import QSym.NilpotentSpectra
import QSym.AxiomCheck
#qsym_check_axioms QSym.NilpotentSpectra.square_zero
#qsym_check_axioms QSym.NilpotentSpectra.two
#qsym_check_axioms QSym.NilpotentSpectra.value_some
#qsym_check_axioms QSym.NilpotentSpectra.two_value
#qsym_check_axioms QSym.NilpotentSpectra.block_value

namespace QSym.NilpotentSpectra

theorem boundary_zero (x y : ℚ) : formula x y 0=x := by simp [formula]
theorem boundary_one (x y : ℚ) : formula x y 1=y := by simp [formula]
theorem boundary_later (x y : ℚ) (n : ℕ) : formula x y (n+2)=0 := by simp [formula]
theorem undefined_exponent (x y : Option ℚ) : value Value.add x y none=none := rfl

#qsym_check_axioms boundary_zero
#qsym_check_axioms boundary_one
#qsym_check_axioms boundary_later
#qsym_check_axioms undefined_exponent

end QSym.NilpotentSpectra
