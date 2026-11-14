import QSym.RefinementBase
import QSym.Elementary
import QSym.ArgumentBranches

namespace QSym.SqrtBranches

theorem conj_off_cut (z : ℂ) (h : Complex.arg z≠Real.pi) :
    (starRingEnd ℂ) (Functions.sqrtC.value z) = Functions.sqrtC.value ((starRingEnd ℂ) z) := by
  simpa [Functions.sqrtC, map_ofNat] using (Complex.conj_cpow z (1/2) h).symm

theorem conj_on_cut (z : ℂ) (h : Complex.arg z=Real.pi) :
    (starRingEnd ℂ) (Functions.sqrtC.value z) = -Functions.sqrtC.value z := by
  obtain ⟨hr, hi⟩ := (ArgumentBranches.arg_on_cut z).mp h
  simp [Functions.sqrtC, one_div, Elementary.sqrt_real_negative hi hr]

theorem inv_off_cut (z : ℂ) (h : Complex.arg z≠Real.pi) :
    Functions.sqrtC.value z⁻¹ = (Functions.sqrtC.value z)⁻¹ :=
  Complex.inv_cpow z (1/2) h

theorem inv_on_cut (z : ℂ) (h : Complex.arg z=Real.pi) :
    Functions.sqrtC.value z⁻¹ = -(Functions.sqrtC.value z)⁻¹ := by
  have hc := conj_on_cut z h
  dsimp [Functions.sqrtC] at hc ⊢
  rw [Complex.inv_cpow_eq_ite, if_pos h]
  simpa [map_ofNat] using congrArg Inv.inv hc

theorem sqrt_ne_zero (z : ℂ) : Functions.sqrtC.value z≠0 ↔ z≠0 := by
  simp [Functions.sqrtC, Complex.cpow_eq_zero_iff]

end QSym.SqrtBranches

namespace QSym.Value

theorem sqrt_conj_off_cut (z : ℂ) (h : Complex.arg z≠Real.pi) :
    conj (Functions.sqrtC.apply (some z)) = Functions.sqrtC.apply (conj (some z)) := by
  simpa [conj, Function1.apply, Functions.sqrtC] using congrArg some (SqrtBranches.conj_off_cut z h)

theorem sqrt_inv_off_cut (z : ℂ) (h : Complex.arg z≠Real.pi) :
    Functions.sqrtC.apply (inv (some z)) = inv (Functions.sqrtC.apply (some z)) := by
  have hn := SqrtBranches.sqrt_ne_zero z
  have hv := SqrtBranches.inv_off_cut z h
  by_cases hz : z=0
  · subst z; norm_num [inv, Function1.apply, Functions.sqrtC]
  · have hs := hn.mpr hz
    simpa [inv, Function1.apply, Functions.sqrtC, hz, hs] using congrArg some hv

theorem sqrt_inv_on_cut (z : ℂ) (h : Complex.arg z=Real.pi) :
    Functions.sqrtC.apply (inv (some z)) = mul (some (-1)) (inv (Functions.sqrtC.apply (some z))) := by
  have hr := ((ArgumentBranches.arg_on_cut z).mp h).1
  have hz : z≠0 := by intro hz; simp [hz] at hr
  have hs := (SqrtBranches.sqrt_ne_zero z).mpr hz
  simpa [inv, mul, Function1.apply, Functions.sqrtC, hz, hs] using congrArg some (SqrtBranches.inv_on_cut z h)

theorem refines_sqrt_conj_re (z : Option ℂ)
    (h : Refines (le (some 0) (Functions.reC.apply z)) (some true)) :
    Refines (conj (Functions.sqrtC.apply z)) (Functions.sqrtC.apply (conj z)) := by
  cases z with
  | none => simp [Refines, Function1.apply, conj]
  | some z =>
    have hz : 0≤z.re := by simpa [Refines, Function1.apply, Functions.reC, le] using h
    exact refines_of_eq (sqrt_conj_off_cut z ((ArgumentBranches.arg_off_cut z).mpr (Or.inl hz)))

theorem refines_sqrt_conj_im (z : Option ℂ)
    (h : Refines (nonzero (Functions.imC.apply z)) (some true)) :
    Refines (conj (Functions.sqrtC.apply z)) (Functions.sqrtC.apply (conj z)) := by
  cases z with
  | none => simp [Refines, Function1.apply, conj]
  | some z =>
    have hz : z.im≠0 := by simpa [Refines, Function1.apply, Functions.imC, nonzero] using h
    exact refines_of_eq (sqrt_conj_off_cut z ((ArgumentBranches.arg_off_cut z).mpr (Or.inr hz)))

theorem refines_sqrt_inv_re (z : Option ℂ)
    (h : Refines (le (some 0) (Functions.reC.apply z)) (some true)) :
    Refines (Functions.sqrtC.apply (inv z)) (inv (Functions.sqrtC.apply z)) := by
  cases z with
  | none => simp [Refines, Function1.apply, inv]
  | some z =>
    have hz : 0≤z.re := by simpa [Refines, Function1.apply, Functions.reC, le] using h
    exact refines_of_eq (sqrt_inv_off_cut z ((ArgumentBranches.arg_off_cut z).mpr (Or.inl hz)))

theorem refines_sqrt_inv_im (z : Option ℂ)
    (h : Refines (nonzero (Functions.imC.apply z)) (some true)) :
    Refines (Functions.sqrtC.apply (inv z)) (inv (Functions.sqrtC.apply z)) := by
  cases z with
  | none => simp [Refines, Function1.apply, inv]
  | some z =>
    have hz : z.im≠0 := by simpa [Refines, Function1.apply, Functions.imC, nonzero] using h
    exact refines_of_eq (sqrt_inv_off_cut z ((ArgumentBranches.arg_off_cut z).mpr (Or.inr hz)))

theorem refines_sqrt_inv_cut (z : Option ℂ)
    (hr : Refines (lt (Functions.reC.apply z) (some 0)) (some true))
    (hi : Refines (not (nonzero (Functions.imC.apply z))) (some true)) :
    Refines (Functions.sqrtC.apply (inv z)) (mul (some (-1)) (inv (Functions.sqrtC.apply z))) := by
  cases z with
  | none => simp [Refines, Function1.apply, inv]
  | some z =>
    have hr' : z.re<0 := by simpa [Refines, Function1.apply, Functions.reC, lt] using hr
    have hi' : z.im=0 := by simpa [Refines, Function1.apply, Functions.imC, nonzero, not] using hi
    exact refines_of_eq (sqrt_inv_on_cut z ((ArgumentBranches.arg_on_cut z).mpr ⟨hr', hi'⟩))

end QSym.Value
