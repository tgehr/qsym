import QSym.AtanhCompositions
import QSym.ArgumentBranches

namespace QSym.InverseSymmetry

theorem atanh_neg (z : ℂ) : Functions.atanhC.value (-z) = -Functions.atanhC.value z := by
  dsimp [Functions.atanhC]
  simp only [← sub_eq_add_neg, sub_neg_eq_add]
  ring

theorem atan_neg (z : ℂ) : Functions.atanC.value (-z) = -Functions.atanC.value z := by
  dsimp [Functions.atanC]
  simp only [mul_neg, ← sub_eq_add_neg, sub_neg_eq_add]
  ring

theorem atanh_neg_domain (z : ℂ) : Functions.atanhC.domain (-z) ↔ Functions.atanhC.domain z := by
  simp [Functions.atanhC, neg_eq_iff_eq_neg, and_comm]

theorem atan_neg_domain (z : ℂ) : Functions.atanC.domain (-z) ↔ Functions.atanC.domain z := by
  simp [Functions.atanC, neg_eq_iff_eq_neg, and_comm]

theorem atanh_conj_domain (z : ℂ) : Functions.atanhC.domain ((starRingEnd ℂ) z) ↔ Functions.atanhC.domain z := by
  have hp : (starRingEnd ℂ) z=1 ↔ z=1 := by
    constructor <;> intro h
    · have := congrArg (starRingEnd ℂ) h; simpa using this
    · simp [h]
  have hm : (starRingEnd ℂ) z=-1 ↔ z=-1 := by
    constructor <;> intro h
    · have := congrArg (starRingEnd ℂ) h; simpa using this
    · simp [h]
  simp only [Functions.atanhC, ne_eq, hp, hm]

theorem atan_conj_domain (z : ℂ) : Functions.atanC.domain ((starRingEnd ℂ) z) ↔ Functions.atanC.domain z := by
  have hp : (starRingEnd ℂ) z=Complex.I ↔ z=-Complex.I := by
    constructor <;> intro h
    · have := congrArg (starRingEnd ℂ) h; simpa using this
    · simp [h]
  have hm : (starRingEnd ℂ) z=-Complex.I ↔ z=Complex.I := by
    constructor <;> intro h
    · have := congrArg (starRingEnd ℂ) h; simpa using this
    · simp [h]
  simp only [Functions.atanC, ne_eq, hp, hm, and_comm]

theorem atanh_conj (z : ℂ) (h : z.im≠0 ∨ (-1<z.re ∧ z.re<1)) :
    (starRingEnd ℂ) (Functions.atanhC.value z) = Functions.atanhC.value ((starRingEnd ℂ) z) := by
  have hp : Complex.arg (1+z)≠Real.pi := by
    apply (ArgumentBranches.arg_off_cut _).mpr
    rcases h with h | ⟨hl, hu⟩
    · right; simpa using h
    · left; simp only [Complex.add_re, Complex.one_re]; linarith
  have hm : Complex.arg (1-z)≠Real.pi := by
    apply (ArgumentBranches.arg_off_cut _).mpr
    rcases h with h | ⟨hl, hu⟩
    · right; simpa using h
    · left; simp only [Complex.sub_re, Complex.one_re]; linarith
  dsimp [Functions.atanhC]
  rw [map_div₀, map_sub, ← Complex.log_conj _ hp, ← Complex.log_conj _ hm]
  simp [map_ofNat]

theorem atan_conj (z : ℂ) (h : z.re≠0 ∨ (-1<z.im ∧ z.im<1)) :
    (starRingEnd ℂ) (Functions.atanC.value z) = Functions.atanC.value ((starRingEnd ℂ) z) := by
  have hi : (Complex.I*z).im≠0 ∨ (-1<(Complex.I*z).re ∧ (Complex.I*z).re<1) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, add_zero, zero_add]
    rcases h with h | ⟨hl, hu⟩
    · exact Or.inl h
    · right; constructor <;> linarith
  rw [AtanhCompositions.atan_atanh, AtanhCompositions.atan_atanh, map_neg, map_mul,
    atanh_conj _ hi]
  have hc : (starRingEnd ℂ) (Complex.I*z)= -(Complex.I*((starRingEnd ℂ) z)) := by simp
  rw [hc, atanh_neg]
  simp

end QSym.InverseSymmetry

namespace QSym.Value

theorem inverse_neg (f : Function1 ℂ ℂ)
    (hd : ∀ z, f.domain (-z) ↔ f.domain z) (hf : ∀ z, f.value (-z) = -f.value z)
    (z : Option ℂ) :
    f.apply (mul (some (-1)) z) = mul (some (-1)) (f.apply z) := by
  cases z with
  | none => rfl
  | some z =>
    by_cases h : f.domain z <;> simp [mul, Function1.apply, hd, hf, h]

theorem inverse_conj (f : Function1 ℂ ℂ) (z : ℂ)
    (hd : f.domain ((starRingEnd ℂ) z) ↔ f.domain z)
    (hf : (starRingEnd ℂ) (f.value z) = f.value ((starRingEnd ℂ) z)) :
    conj (f.apply (some z)) = f.apply (conj (some z)) := by
  by_cases h : f.domain z <;> simp [conj, Function1.apply, hd, hf, h]

theorem inverse_neg_reverse (f : Function1 ℂ ℂ)
    (hd : ∀ z, f.domain (-z) ↔ f.domain z) (hf : ∀ z, f.value (-z) = -f.value z)
    (z : Option ℂ) :
    f.apply z = mul (some (-1)) (f.apply (mul (some (-1)) z)) := by
  rw [inverse_neg f hd hf]
  cases f.apply z <;> simp [mul]

theorem refines_atanh_neg (z : Option ℂ) :
    Refines (Functions.atanhC.apply (mul (some (-1)) z))
      (mul (some (-1)) (Functions.atanhC.apply z)) :=
  refines_of_eq (inverse_neg _ InverseSymmetry.atanh_neg_domain InverseSymmetry.atanh_neg z)

theorem refines_atan_neg (z : Option ℂ) :
    Refines (Functions.atanC.apply (mul (some (-1)) z))
      (mul (some (-1)) (Functions.atanC.apply z)) :=
  refines_of_eq (inverse_neg _ InverseSymmetry.atan_neg_domain InverseSymmetry.atan_neg z)

theorem refines_atanh_negative_literal (z : Option ℂ) :
    Refines (Functions.atanhC.apply z) (mul (some (-1)) (Functions.atanhC.apply (mul (some (-1)) z))) :=
  refines_of_eq (inverse_neg_reverse _ InverseSymmetry.atanh_neg_domain InverseSymmetry.atanh_neg z)

theorem refines_atan_negative_literal (z : Option ℂ) :
    Refines (Functions.atanC.apply z) (mul (some (-1)) (Functions.atanC.apply (mul (some (-1)) z))) :=
  refines_of_eq (inverse_neg_reverse _ InverseSymmetry.atan_neg_domain InverseSymmetry.atan_neg z)

theorem refines_atanh_conj_im (z : Option ℂ) (h : Refines (nonzero (Functions.imC.apply z)) (some true)) :
    Refines (conj (Functions.atanhC.apply z)) (Functions.atanhC.apply (conj z)) := by
  cases z with
  | none => simp [Refines, Function1.apply, conj]
  | some z =>
    have hz : z.im≠0 := by simpa [Refines, Function1.apply, Functions.imC, nonzero] using h
    exact refines_of_eq (inverse_conj _ _ (InverseSymmetry.atanh_conj_domain z) (InverseSymmetry.atanh_conj z (Or.inl hz)))

theorem refines_atanh_conj_re (z : Option ℂ)
    (hl : Refines (lt (some (-1)) (Functions.reC.apply z)) (some true))
    (hu : Refines (lt (Functions.reC.apply z) (some 1)) (some true)) :
    Refines (conj (Functions.atanhC.apply z)) (Functions.atanhC.apply (conj z)) := by
  cases z with
  | none => simp [Refines, Function1.apply, conj]
  | some z =>
    have hl' : -1<z.re := by simpa [Refines, Function1.apply, Functions.reC, lt] using hl
    have hu' : z.re<1 := by simpa [Refines, Function1.apply, Functions.reC, lt] using hu
    exact refines_of_eq (inverse_conj _ _ (InverseSymmetry.atanh_conj_domain z) (InverseSymmetry.atanh_conj z (Or.inr ⟨hl',hu'⟩)))

theorem refines_atan_conj_re (z : Option ℂ) (h : Refines (nonzero (Functions.reC.apply z)) (some true)) :
    Refines (conj (Functions.atanC.apply z)) (Functions.atanC.apply (conj z)) := by
  cases z with
  | none => simp [Refines, Function1.apply, conj]
  | some z =>
    have hz : z.re≠0 := by simpa [Refines, Function1.apply, Functions.reC, nonzero] using h
    exact refines_of_eq (inverse_conj _ _ (InverseSymmetry.atan_conj_domain z) (InverseSymmetry.atan_conj z (Or.inl hz)))

theorem refines_atan_conj_im (z : Option ℂ)
    (hl : Refines (lt (some (-1)) (Functions.imC.apply z)) (some true))
    (hu : Refines (lt (Functions.imC.apply z) (some 1)) (some true)) :
    Refines (conj (Functions.atanC.apply z)) (Functions.atanC.apply (conj z)) := by
  cases z with
  | none => simp [Refines, Function1.apply, conj]
  | some z =>
    have hl' : -1<z.im := by simpa [Refines, Function1.apply, Functions.imC, lt] using hl
    have hu' : z.im<1 := by simpa [Refines, Function1.apply, Functions.imC, lt] using hu
    exact refines_of_eq (inverse_conj _ _ (InverseSymmetry.atan_conj_domain z) (InverseSymmetry.atan_conj z (Or.inr ⟨hl',hu'⟩)))

end QSym.Value
