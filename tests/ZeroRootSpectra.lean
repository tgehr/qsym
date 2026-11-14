import QSym.ZeroRootSpectra
import QSym.AxiomCheck
namespace QSym.ZeroRootSpectra
#qsym_check_axioms decomposition
#qsym_check_axioms three_value

theorem boundary_zero (r : Fin 3 → ℝ) (c : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    value Value.add Value.mul Spectral.power (fun j => some (r j)) (fun j i => some (c j i)) (some 0) i =
      some ((c 0 i+c 1 i)+c 2 i) := by simp [value, Spectral.power, Value.add, Value.mul]
theorem boundary_one (r : Fin 3 → ℂ) (c : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    value Value.add Value.mul Spectral.power (fun j => some (r j)) (fun j i => some (c j i)) (some 1) i =
      some ((r 0*c 0 i+r 1*c 1 i)+r 2*c 2 i) := by simp [value, Spectral.power, Value.add, Value.mul]
theorem undefined_exponent (r : Fin 3 → Option ℚ) (c : Fin 3 → Fin 3 → Option ℚ) (i : Fin 3) :
    value Value.add Value.mul Spectral.power r c none i=none := by
  simp [value, Spectral.power, Value.add, Value.mul, Option.bind_assoc]
#qsym_check_axioms boundary_zero
#qsym_check_axioms boundary_one
#qsym_check_axioms undefined_exponent
end QSym.ZeroRootSpectra
