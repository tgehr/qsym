import QSym.CubeZeroSpectra
import QSym.AxiomCheck

namespace QSym.CubeZeroSpectra
#qsym_check_axioms power
#qsym_check_axioms step_some
#qsym_check_axioms square_some
#qsym_check_axioms index_some
#qsym_check_axioms mask_some
#qsym_check_axioms value_some
#qsym_check_axioms checked_cube
#qsym_check_axioms three_value
#qsym_check_axioms three_compact_value

theorem boundary_zero (x y z : ℕ) : formula x y z 0=x := by simp [formula]
theorem boundary_one (x y z : ℤ) : formula x y z 1=y := by simp [formula]
theorem boundary_two (x y z : ℚ) : formula x y z 2=z := by simp [formula]
theorem boundary_later (x y z : ℂ) (n : ℕ) : formula x y z (n+3)=0 := by simp [formula]
theorem undefined_exponent (a : Fin 3 → Fin 3 → Option ℝ) (v : Fin 3 → Option ℝ) (i : Fin 3) :
    value Value.add Value.mul a v none i=none := rfl
#qsym_check_axioms boundary_zero
#qsym_check_axioms boundary_one
#qsym_check_axioms boundary_two
#qsym_check_axioms boundary_later
#qsym_check_axioms undefined_exponent
end QSym.CubeZeroSpectra
