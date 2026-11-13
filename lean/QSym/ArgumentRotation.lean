import QSym.Functions

namespace QSym.ArgumentRotation

theorem arg_positive_iff (z : ℂ) :
    0<Complex.arg z ↔ 0<z.im ∨ z.im=0 ∧ z.re<0 := by
  constructor
  · intro h
    have hi := Complex.arg_nonneg_iff.mp h.le
    rcases lt_or_eq_of_le hi with hi|hi
    · exact Or.inl hi
    · refine Or.inr ⟨hi.symm, lt_of_not_ge ?_⟩
      intro hr
      have hz := Complex.arg_eq_zero_iff.mpr ⟨hr, hi.symm⟩
      linarith
  · rintro (hi|⟨hi,hr⟩)
    · apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hi.le)
      intro h
      have hz := (Complex.arg_eq_zero_iff.mp h.symm).2
      linarith
    · rw [Complex.arg_eq_pi_iff.mpr ⟨hr,hi⟩]
      exact Real.pi_pos

theorem arg_nonpositive_iff (z : ℂ) :
    Complex.arg z≤0 ↔ z.im<0 ∨ 0≤z.re ∧ z.im=0 := by
  constructor
  · intro h
    by_cases hi : z.im<0
    · exact Or.inl hi
    · exact Or.inr (Complex.arg_eq_zero_iff.mp
        (le_antisymm h (Complex.arg_nonneg_iff.mpr (le_of_not_gt hi))))
  · rintro (hi|h)
    · exact (Complex.arg_neg_iff.mpr hi).le
    · rw [Complex.arg_eq_zero_iff.mpr h]

theorem arg_scale {z w : ℂ} (hi : z.im=0) (hr : 0<z.re) :
    Complex.arg (z*w)=Complex.arg w := by
  have hz : z=(z.re : ℂ) := by apply Complex.ext <;> simp [hi]
  rw [hz]
  exact Complex.arg_real_mul w hr

theorem arg_positive_of_im_pos {z : ℂ} (h : 0<z.im) : 0<Complex.arg z :=
  (arg_positive_iff z).mpr (Or.inl h)

theorem arg_nonpositive_of_im_neg {z : ℂ} (h : z.im<0) : Complex.arg z≤0 :=
  (Complex.arg_neg_iff.mpr h).le

theorem arg_scale_right {z w : ℂ} (hi : w.im=0) (hr : 0<w.re) :
    Complex.arg (z*w)=Complex.arg z := by
  simpa only [mul_comm] using arg_scale (w:=z) hi hr

theorem arg_negative_scale {z w : ℂ} (hi : z.im=0) (hr : z.re<0) :
    Complex.arg (z*w)=Complex.arg (-w) := by
  have h := arg_scale (z := -z) (w := -w) (by simp [hi]) (by simpa using neg_pos.mpr hr)
  simpa only [neg_mul_neg] using h

theorem arg_negative_scale_right {z w : ℂ} (hi : w.im=0) (hr : w.re<0) :
    Complex.arg (z*w)=Complex.arg (-z) := by
  simpa only [mul_comm] using arg_negative_scale (w:=z) hi hr

theorem arg_neg_scale {z w : ℂ} (hi : z.im=0) (hr : 0<z.re) :
    Complex.arg (-(z*w))=Complex.arg (-w) := by
  rw [← mul_neg]
  exact arg_scale hi hr

theorem arg_neg_scale_right {z w : ℂ} (hi : w.im=0) (hr : 0<w.re) :
    Complex.arg (-(z*w))=Complex.arg (-z) := by
  rw [← neg_mul]
  exact arg_scale_right hi hr

theorem arg_neg_positive (z : ℂ) (h : 0<Complex.arg z) :
    Complex.arg (-z)=Complex.arg z-Real.pi :=
  Complex.arg_neg_eq_arg_sub_pi_iff.mpr ((arg_positive_iff z).mp h)

theorem arg_neg_nonpositive (z : ℂ) (hz : z≠0) (h : Complex.arg z≤0) :
    Complex.arg (-z)=Complex.arg z+Real.pi := by
  apply Complex.arg_neg_eq_arg_add_pi_iff.mpr
  rcases (arg_nonpositive_iff z).mp h with hi|⟨hr,hi⟩
  · exact Or.inl hi
  · refine Or.inr ⟨hi, lt_of_le_of_ne hr ?_⟩
    intro heq
    apply hz
    apply Complex.ext <;> simp [hi, heq.symm]

theorem log_neg_positive (z : ℂ) (h : 0<Complex.arg z) :
    Complex.log (-z)=Complex.log z-(Real.pi : ℂ)*Complex.I := by
  simp only [Complex.log, norm_neg, arg_neg_positive z h, Complex.ofReal_sub]
  ring

theorem log_neg_nonpositive (z : ℂ) (hz : z≠0) (h : Complex.arg z≤0) :
    Complex.log (-z)=Complex.log z+(Real.pi : ℂ)*Complex.I := by
  simp only [Complex.log, norm_neg, arg_neg_nonpositive z hz h, Complex.ofReal_add]
  ring

theorem log_negative_real {z : ℂ} (hi : z.im=0) (hr : z.re<0) :
    Complex.log z=(Real.log (-z.re) : ℂ)+(Real.pi : ℂ)*Complex.I := by
  have hz : z=(z.re : ℂ) := by apply Complex.ext <;> simp [hi]
  calc
    Complex.log z=Complex.log (z.re : ℂ) := congrArg Complex.log hz
    _ = _ := by simp [Complex.log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg hr, Complex.arg_ofReal_of_neg hr]

theorem log_I : Complex.log Complex.I=(Real.pi/2 : ℂ)*Complex.I :=
  Complex.log_I

theorem log_neg_I : Complex.log (-Complex.I)= -(Real.pi/2 : ℂ)*Complex.I :=
  Complex.log_neg_I

end QSym.ArgumentRotation
