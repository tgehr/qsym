import QSym.Functions

namespace QSym.Order

theorem log_eq_exp {x y : ℝ} (hx : 0<x) : Real.log x=y ↔ x=Real.exp y := by
  constructor
  · intro h; rw [← h, Real.exp_log hx]
  · intro h; rw [h, Real.log_exp]

theorem log_nonpositive {x : ℝ} (hx : 0<x) : Real.log x≤0 ↔ x≤1 := Real.log_nonpos_iff hx.le
theorem log_positive {x : ℝ} (hx : 0<x) : 0<Real.log x ↔ 1<x := Real.log_pos_iff hx.le

theorem abs_eq_cases (x y : ℝ) : |x|=y ↔ 0≤y ∧ (x=-y ∨ x=y) := by
  by_cases hy : 0≤y
  · simp [hy, abs_eq hy, or_comm]
  · have h : |x|≠y := by have := abs_nonneg x; intro he; linarith
    simp [hy, h]

theorem lt_abs_cases (x y : ℝ) : y < |x| ↔ x < -y ∨ y<x := by
  rw [lt_abs]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

theorem le_abs_cases (x y : ℝ) : y ≤ |x| ↔ x≤-y ∨ y≤x := by
  rw [le_abs]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

theorem nonnegative_add_eq_zero {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    x+y=0 ↔ x=0 ∧ y=0 := by
  constructor
  · intro h; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; simp

theorem nonpositive_add_eq_zero {x y : ℝ} (hx : x≤0) (hy : y≤0) :
    x+y=0 ↔ x=0 ∧ y=0 := by
  constructor
  · intro h; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; simp

theorem odd_power_lt (x y : ℝ) (n : ℕ) : x^(n+n+1)<y^(n+n+1) ↔ x<y :=
  (show Odd (n+n+1) from ⟨n, by omega⟩).pow_lt_pow

theorem odd_power_le (x y : ℝ) (n : ℕ) : x^(n+n+1)≤y^(n+n+1) ↔ x≤y :=
  (show Odd (n+n+1) from ⟨n, by omega⟩).pow_le_pow

theorem odd_power_eq (x y : ℝ) (n : ℕ) : x^(n+n+1)=y^(n+n+1) ↔ x=y :=
  (show Odd (n+n+1) from ⟨n, by omega⟩).pow_inj

theorem odd_negative (x : ℝ) (n : ℕ) : x^(n+n+1)<0 ↔ x<0 :=
  (show Odd (n+n+1) from ⟨n, by omega⟩).pow_neg_iff

theorem odd_nonpositive (x : ℝ) (n : ℕ) : x^(n+n+1)≤0 ↔ x≤0 :=
  (show Odd (n+n+1) from ⟨n, by omega⟩).pow_nonpos_iff

theorem odd_positive (x : ℝ) (n : ℕ) : 0<x^(n+n+1) ↔ 0<x :=
  (show Odd (n+n+1) from ⟨n, by omega⟩).pow_pos_iff

theorem odd_nonnegative (x : ℝ) (n : ℕ) : 0≤x^(n+n+1) ↔ 0≤x :=
  (show Odd (n+n+1) from ⟨n, by omega⟩).pow_nonneg_iff

theorem even_nonnegative (x : ℝ) (n : ℕ) : 0≤x^(n+n+2) :=
  (show Even (n+n+2) from ⟨n+1, by omega⟩).pow_nonneg x

theorem even_lt_nonpositive (x c : ℝ) (n : ℕ) (hc : c≤0) : x^(n+n+2)<c ↔ False :=
  iff_false_intro (not_lt_of_ge (hc.trans (even_nonnegative x n)))

theorem even_le_negative (x c : ℝ) (n : ℕ) (hc : c<0) : x^(n+n+2)≤c ↔ False :=
  iff_false_intro (not_le_of_gt (hc.trans_le (even_nonnegative x n)))

theorem negative_lt_even (x c : ℝ) (n : ℕ) (hc : c<0) : c<x^(n+n+2) ↔ True :=
  iff_true_intro (hc.trans_le (even_nonnegative x n))

theorem nonpositive_le_even (x c : ℝ) (n : ℕ) (hc : c≤0) : c≤x^(n+n+2) ↔ True :=
  iff_true_intro (hc.trans (even_nonnegative x n))

theorem odd_mul_negative (x y : ℝ) (n : ℕ) : x^(n+n+1)*y<0 ↔ x*y<0 := by
  simp only [mul_neg_iff, odd_negative, odd_nonpositive, odd_positive, odd_nonnegative]

theorem odd_mul_nonpositive (x y : ℝ) (n : ℕ) : x^(n+n+1)*y≤0 ↔ x*y≤0 := by
  simp only [mul_nonpos_iff, odd_negative, odd_nonpositive, odd_positive, odd_nonnegative]

theorem odd_mul_positive (x y : ℝ) (n : ℕ) : 0<x^(n+n+1)*y ↔ 0<x*y := by
  simp only [mul_pos_iff, odd_negative, odd_nonpositive, odd_positive, odd_nonnegative]

theorem odd_mul_nonnegative (x y : ℝ) (n : ℕ) : 0≤x^(n+n+1)*y ↔ 0≤x*y := by
  simp only [mul_nonneg_iff, odd_negative, odd_nonpositive, odd_positive, odd_nonnegative]

theorem even_mul_negative (x y : ℝ) (n : ℕ) : x^(n+n+2)*y<0 ↔ x≠0 ∧ y<0 := by
  by_cases hx : x=0
  · simp [hx]
  · have hp : 0<x^(n+n+2) := (show Even (n+n+2) from ⟨n+1, by omega⟩).pow_pos_iff (by omega) |>.mpr hx
    simp [hx, mul_neg_iff, mul_nonpos_iff, mul_pos_iff, mul_nonneg_iff,
      hp, hp.le, not_lt_of_ge hp.le, not_le_of_gt hp]

theorem even_mul_nonpositive (x y : ℝ) (n : ℕ) : x^(n+n+2)*y≤0 ↔ x=0 ∨ y≤0 := by
  by_cases hx : x=0
  · simp [hx]
  · have hp : 0<x^(n+n+2) := (show Even (n+n+2) from ⟨n+1, by omega⟩).pow_pos_iff (by omega) |>.mpr hx
    simp [hx, mul_neg_iff, mul_nonpos_iff, mul_pos_iff, mul_nonneg_iff,
      hp, hp.le, not_lt_of_ge hp.le, not_le_of_gt hp]

theorem even_mul_positive (x y : ℝ) (n : ℕ) : 0<x^(n+n+2)*y ↔ x≠0 ∧ 0<y := by
  by_cases hx : x=0
  · simp [hx]
  · have hp : 0<x^(n+n+2) := (show Even (n+n+2) from ⟨n+1, by omega⟩).pow_pos_iff (by omega) |>.mpr hx
    simp [hx, mul_neg_iff, mul_nonpos_iff, mul_pos_iff, mul_nonneg_iff,
      hp, hp.le, not_lt_of_ge hp.le, not_le_of_gt hp]

theorem even_mul_nonnegative (x y : ℝ) (n : ℕ) : 0≤x^(n+n+2)*y ↔ x=0 ∨ 0≤y := by
  by_cases hx : x=0
  · simp [hx]
  · have hp : 0<x^(n+n+2) := (show Even (n+n+2) from ⟨n+1, by omega⟩).pow_pos_iff (by omega) |>.mpr hx
    simp [hx, mul_neg_iff, mul_nonpos_iff, mul_pos_iff, mul_nonneg_iff,
      hp, hp.le, not_lt_of_ge hp.le, not_le_of_gt hp]

theorem even_power_lt (x y : ℝ) (n : ℕ) : x^(n+n+2)<y^(n+n+2) ↔ |x| < |y| := by
  have h : Even (n+n+2) := ⟨n+1, by omega⟩
  rw [← h.pow_abs x, ← h.pow_abs y]
  exact pow_lt_pow_iff_left₀ (abs_nonneg x) (abs_nonneg y) (by omega)

theorem even_power_le (x y : ℝ) (n : ℕ) : x^(n+n+2)≤y^(n+n+2) ↔ |x| ≤ |y| := by
  have h : Even (n+n+2) := ⟨n+1, by omega⟩
  rw [← h.pow_abs x, ← h.pow_abs y]
  exact pow_le_pow_iff_left₀ (abs_nonneg x) (abs_nonneg y) (by omega)

theorem even_power_eq (x y : ℝ) (n : ℕ) : x^(n+n+2)=y^(n+n+2) ↔ x=-y ∨ x=y := by
  have h : Even (n+n+2) := ⟨n+1, by omega⟩
  simp [pow_eq_pow_iff_of_ne_zero (by omega : n+n+2≠0), h, or_comm]

theorem nonnegative_power_lt {x y : ℝ} (n : ℕ) (hx : 0≤x) (hy : 0≤y) :
    x^(n+1)<y^(n+1) ↔ x<y := pow_lt_pow_iff_left₀ hx hy (Nat.succ_ne_zero n)

theorem nonnegative_power_le {x y : ℝ} (n : ℕ) (hx : 0≤x) (hy : 0≤y) :
    x^(n+1)≤y^(n+1) ↔ x≤y := pow_le_pow_iff_left₀ hx hy (Nat.succ_ne_zero n)

theorem sqrt_lt_bound {x y : ℝ} (hx : 0≤x) : Real.sqrt x<y ↔ 0<y ∧ x<y^2 := by
  constructor
  · intro h
    have hy := (Real.sqrt_nonneg x).trans_lt h
    exact ⟨hy, (Real.sqrt_lt hx hy.le).mp h⟩
  · rintro ⟨hy, h⟩
    exact (Real.sqrt_lt hx hy.le).mpr h

theorem lt_sqrt_bound (x y : ℝ) : y<Real.sqrt x ↔ y<0 ∨ y^2<x := by
  by_cases hy : y<0
  · simp [hy, hy.trans_le (Real.sqrt_nonneg x)]
  · simpa [hy] using (Real.lt_sqrt (le_of_not_gt hy))

theorem le_sqrt_bound {x y : ℝ} (hx : 0≤x) : y≤Real.sqrt x ↔ y≤0 ∨ y^2≤x := by
  by_cases hy : y≤0
  · simp [hy, hy.trans (Real.sqrt_nonneg x)]
  · simpa [hy] using (Real.le_sqrt (le_of_lt (lt_of_not_ge hy)) hx)

theorem quadratic_lt_pos {l r x a b d : ℝ}
    (hp : l-r=a*((x+b)^2-d)) (ha : 0<a) :
    l<r ↔ -b<x+Real.sqrt d ∧ b+x<Real.sqrt d := by
  rw [← sub_lt_zero, hp, mul_neg_iff]
  simp only [not_lt_of_ge ha.le, ha, false_and, and_false, true_and, and_true, false_or, or_false, sub_neg]
  rw [Real.sq_lt]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

theorem quadratic_le_pos {l r x a b d : ℝ}
    (hp : l-r=a*((x+b)^2-d)) (ha : 0<a) (hd : 0≤d) :
    l≤r ↔ -b≤x+Real.sqrt d ∧ b+x≤Real.sqrt d := by
  rw [← sub_nonpos, hp, mul_nonpos_iff]
  simp only [not_le_of_gt ha, ha.le, false_and, and_false, true_and, and_true, false_or, or_false, sub_nonpos]
  rw [Real.sq_le hd]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> linarith

theorem quadratic_lt_neg {l r x a b d : ℝ}
    (hp : l-r=a*((x+b)^2-d)) (ha : a<0) (hd : 0≤d) :
    l<r ↔ x+Real.sqrt d < -b ∨ Real.sqrt d<b+x := by
  have h := quadratic_le_pos (l := r) (r := l) (x := x) (a := -a) (b := b) (d := d)
    (by linarith) (neg_pos.mpr ha) hd
  simpa only [not_le, not_and_or] using not_congr h

theorem quadratic_le_neg {l r x a b d : ℝ}
    (hp : l-r=a*((x+b)^2-d)) (ha : a<0) :
    l≤r ↔ x+Real.sqrt d≤-b ∨ Real.sqrt d≤b+x := by
  have h := quadratic_lt_pos (l := r) (r := l) (x := x) (a := -a) (b := b) (d := d)
    (by linarith) (neg_pos.mpr ha)
  simpa only [not_lt, not_and_or] using not_congr h

end QSym.Order
