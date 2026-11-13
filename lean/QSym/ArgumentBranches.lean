import QSym.Functions

namespace QSym.ArgumentBranches

theorem arg_on_cut (z : ℂ) : Complex.arg z=Real.pi ↔ z.re<0 ∧ z.im=0 :=
  Complex.arg_eq_pi_iff

theorem arg_off_cut (z : ℂ) : Complex.arg z≠Real.pi ↔ 0≤z.re ∨ z.im≠0 := by
  simp only [ne_eq, arg_on_cut, not_and_or, not_lt]

theorem arg_conj_off_cut (z : ℂ) (h : Complex.arg z≠Real.pi) :
    Complex.arg ((starRingEnd ℂ) z)=-Complex.arg z := by
  simpa only [if_neg h] using Complex.arg_conj z

theorem arg_inv_off_cut (z : ℂ) (h : Complex.arg z≠Real.pi) :
    Complex.arg z⁻¹=-Complex.arg z := by
  simpa only [if_neg h] using Complex.arg_inv z

theorem log_conj_off_cut (z : ℂ) (h : Complex.arg z≠Real.pi) :
    Complex.log ((starRingEnd ℂ) z)=(starRingEnd ℂ) (Complex.log z) :=
  Complex.log_conj z h

theorem arg_conj_on_cut (z : ℂ) (h : Complex.arg z=Real.pi) :
    Complex.arg ((starRingEnd ℂ) z)=Real.pi := by
  simpa only [if_pos h] using Complex.arg_conj z

theorem arg_inv_on_cut (z : ℂ) (h : Complex.arg z=Real.pi) :
    Complex.arg z⁻¹=Real.pi := by
  simpa only [if_pos h] using Complex.arg_inv z

theorem log_conj_on_cut (z : ℂ) (h : Complex.arg z=Real.pi) :
    Complex.log ((starRingEnd ℂ) z)=Complex.log z := by
  simpa only [if_pos h] using Complex.log_conj_eq_ite z

theorem log_inv_on_cut (z : ℂ) (h : Complex.arg z=Real.pi) :
    Complex.log z⁻¹= -(starRingEnd ℂ) (Complex.log z) := by
  simpa only [if_pos h] using Complex.log_inv_eq_ite z

end QSym.ArgumentBranches
