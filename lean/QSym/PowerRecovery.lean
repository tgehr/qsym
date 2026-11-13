import QSym.Functions

namespace QSym.PowerRecovery

theorem nested {x : ℝ} (hx : 0≤x) (y z : ℝ) : (x^y)^z=x^(y*z) :=
  (Real.rpow_mul hx y z).symm

theorem sqrt_base {x : ℝ} (hx : 0≤x) (y : ℝ) : (Real.sqrt x)^y=x^(y/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

theorem sqrt_power {x : ℝ} (hx : 0≤x) (y : ℝ) : Real.sqrt (x^y)=x^(y/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

theorem natural_outer {x : ℝ} (hx : 0≤x) (y : ℝ) (n : ℕ) : (x^y)^n=x^(y*(n : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem natural_inner {x : ℝ} (hx : 0≤x) (y : ℝ) (n : ℕ) : (x^n)^y=x^((n : ℝ)*y) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem complex_natural_outer (z w : ℂ) (n : ℕ) : (z^w)^n=z^(w*(n : ℂ)) :=
  (Complex.cpow_mul_nat z w n).symm

theorem complex_nested (z w u : ℂ) (h₁ : -Real.pi<(Complex.log z*w).im)
    (h₂ : (Complex.log z*w).im≤Real.pi) : (z^w)^u=z^(w*u) :=
  (Complex.cpow_mul u h₁ h₂).symm

theorem quotient {x y : ℝ} (hx : 0≤x) (hy : 0≤y) (t : ℝ) : x^t/y^t=(x/y)^t :=
  (Real.div_rpow hx hy t).symm

theorem subtract {x : ℝ} (hx : 0<x) (y z : ℝ) : x^y/x^z=x^(y-z) :=
  (Real.rpow_sub hx y z).symm

theorem complex_subtract {x : ℂ} (hx : x≠0) (y z : ℂ) : x^y/x^z=x^(y-z) :=
  (Complex.cpow_sub y z hx).symm

theorem inverse_base {x : ℝ} (hx : 0≤x) (y : ℝ) : (x⁻¹)^y=(x^y)⁻¹ :=
  Real.inv_rpow hx y

theorem domain_nonnegative (x y : ℝ) (hx : 0≤x) :
    (0<x ∨ x=0 ∧ 0≤y ∨ x<0 ∧ ∃ n : ℤ, y=n) ↔ x≠0 ∨ 0≤y := by
  rcases eq_or_lt_of_le hx with h|h
  · simp [← h]
  · simp [h, ne_of_gt h, not_lt.mpr h.le]

theorem nested_domain (x y z : ℝ) (hx : 0≤x) (hy : Functions.powerR.domain x y)
    (hz : Functions.powerR.domain (x^y) z) : Functions.powerR.domain x (y*z) := by
  rcases hy with hp|⟨rfl,hy⟩|⟨hn,_⟩
  · exact Or.inl hp
  · by_cases h : y=0
    · simp [h, Functions.powerR]
    · have hz : 0≤z := by simpa [Functions.powerR, Real.zero_rpow h] using hz
      exact Or.inr (Or.inl ⟨rfl, mul_nonneg hy hz⟩)
  · exact (not_lt_of_ge hx hn).elim

theorem half_domain (x y : ℝ) (hx : 0≤x) (hy : Functions.powerR.domain x y) :
    Functions.powerR.domain x (y/2) := by
  rcases hy with hp|⟨rfl,hy⟩|⟨hn,_⟩
  · exact Or.inl hp
  · exact Or.inr (Or.inl ⟨rfl, by positivity⟩)
  · exact (not_lt_of_ge hx hn).elim

theorem sqrt_domain (x y : ℝ) (hx : 0≤x) (hy : Functions.powerR.domain (Real.sqrt x) y) :
    Functions.powerR.domain x (y/2) := by
  rcases eq_or_lt_of_le hx with h|h
  · subst x
    have hy : 0≤y := by simpa [Functions.powerR] using hy
    exact Or.inr (Or.inl ⟨rfl, by positivity⟩)
  · exact Or.inl h

theorem natural_domain (x y : ℝ) (n : ℕ) (hx : 0≤x) (hy : Functions.powerR.domain x y) :
    Functions.powerR.domain x (y*((n : ℝ)+1)) := by
  rcases hy with hp|⟨rfl,hy⟩|⟨hn,_⟩
  · exact Or.inl hp
  · exact Or.inr (Or.inl ⟨rfl, by positivity⟩)
  · exact (not_lt_of_ge hx hn).elim

theorem inner_domain (x y : ℝ) (n : ℕ) (hx : 0≤x) (hy : Functions.powerR.domain (x^(n+1)) y) :
    Functions.powerR.domain x (((n : ℝ)+1)*y) := by
  rcases eq_or_lt_of_le hx with h|h
  · subst x
    have hy : 0≤y := by simpa [Functions.powerR] using hy
    exact Or.inr (Or.inl ⟨rfl, by positivity⟩)
  · exact Or.inl h

theorem quotient_domain (x y t : ℝ) (hx : 0≤x) (hy : 0<y) (ht : Functions.powerR.domain x t) :
    Functions.powerR.domain (x/y) t := by
  rcases ht with hp|⟨rfl,ht⟩|⟨hn,_⟩
  · exact Or.inl (div_pos hp hy)
  · simp [Functions.powerR, ht]
  · exact (not_lt_of_ge hx hn).elim

theorem nested_domain_nonnegative (x y z : ℝ) (hx : 0≤x) (hy : x≠0 ∨ 0≤y)
    (hz : Functions.powerR.domain (x^y) z) : x≠0 ∨ 0≤y*z := by
  exact (domain_nonnegative x (y*z) hx).mp
    (nested_domain x y z hx ((domain_nonnegative x y hx).mpr hy) hz)

theorem even_inner (x y : ℝ) (n : ℕ) : (x^(n+n+2))^y=|x|^(((n : ℝ)+(n : ℝ)+2)*y) := by
  have he : Even (n+n+2) := ⟨n+1, by omega⟩
  have h : |x|^(n+n+2)=x^(n+n+2) := by
    rw [← abs_pow, abs_of_nonneg (he.pow_nonneg x)]
  rw [← h, natural_inner (abs_nonneg x)]
  push_cast
  rfl

theorem natural_outer_valid (x y : ℝ) (n : ℕ) (h : Functions.powerR.domain x y) :
    (x^y)^(n+1)=x^(y*((n : ℝ)+1)) := by
  rcases h with hx|⟨rfl,hy⟩|⟨hx,k,rfl⟩
  · simpa using natural_outer hx.le y (n+1)
  · simpa using natural_outer (by norm_num : (0:ℝ)≤0) y (n+1)
  · have he : (k : ℝ)*((n : ℝ)+1)=((k*(n+1) : ℤ) : ℝ) := by push_cast; ring
    rw [he, Real.rpow_intCast, Real.rpow_intCast, zpow_mul]
    norm_cast

theorem natural_outer_domain (x y : ℝ) (n : ℕ) (h : Functions.powerR.domain x y) :
    Functions.powerR.domain x (y*((n : ℝ)+1)) := by
  rcases h with hx|⟨rfl,hy⟩|⟨hx,k,rfl⟩
  · exact Or.inl hx
  · exact Or.inr (Or.inl ⟨rfl, by positivity⟩)
  · exact Or.inr (Or.inr ⟨hx, k*(n+1), by push_cast; ring⟩)

theorem domain_widen (x y : ℝ) (p : Prop) (hx : 0≤x) (hy : x≠0 ∨ 0≤y) :
    0<x ∨ x=0 ∧ 0≤y ∨ p := by
  by_cases h : x=0
  · simp_all
  · exact Or.inl (lt_of_le_of_ne hx (Ne.symm h))

theorem inner_domain_normal (x y : ℝ) (n : ℕ) (hx : 0≤x)
    (hy : 0<x*x^n ∨ x=0 ∧ 0≤y ∨ x*x^n<0 ∧ ∃ k : ℤ, y=k) :
    x≠0 ∨ 0≤y+y*(n : ℝ) := by
  by_cases h : x=0
  · subst x
    have hy : 0≤y := by simpa using hy
    right; positivity
  · exact Or.inl h

theorem natural_outer_normal (x y : ℝ) (n : ℕ) (hy : Functions.powerR.domain x y) :
    (0<x ∨ x=0 ∧ 0≤y ∨ x<0 ∧ ∃ k : ℤ, y+y*(n : ℝ)=k) ∧
      x^(y+y*(n : ℝ))=x^y*(x^y)^n := by
  have h := natural_outer_domain x y n hy
  have hval := (natural_outer_valid x y n hy).symm
  have hn : (0 : ℝ)<(n : ℝ)+1 := by positivity
  constructor
  · rcases hy with hp|⟨rfl,hy⟩|⟨hx,k,hk⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inl ⟨rfl,hy⟩)
    · exact Or.inr (Or.inr ⟨hx,k*(n+1),by rw [hk]; push_cast; ring⟩)
  · simpa [mul_add, add_comm, pow_succ'] using hval

theorem nonzero_bounds (x : ℝ) (h₁ : 0≤x) (h₂ : x≤0) (h₃ : x≠0) : False :=
  h₃ (le_antisymm h₂ h₁)

theorem subtract_product (x y z : ℝ) (hx : 0<x) : x^z*x^(y-z)=x^y := by
  rw [Real.rpow_sub hx]
  exact mul_div_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hx z))

theorem even_domain_normal (x y : ℝ) (n : ℕ)
    (hy : 0<x^2*x^(n*2) ∨ x=0 ∧ 0≤y ∨ x^2*x^(n*2)<0 ∧ ∃ k : ℤ, y=k) :
    x≠0 ∨ x=0 ∧ 0≤y*2+y*(n : ℝ)*2 ∨ |x|<0 ∧ ∃ k : ℤ, y*2+y*(n : ℝ)*2=k := by
  by_cases h : x=0
  · subst x
    have hy : 0≤y := by simpa using hy
    exact Or.inr (Or.inl ⟨rfl, by positivity⟩)
  · exact Or.inl h

theorem negative_integral (x y : ℝ) (hx : x<0) (hy : Functions.powerR.domain x y) :
    ∃ k : ℤ, y=k := by
  simpa [Functions.powerR, hx, ne_of_lt hx, not_lt.mpr hx.le] using hy

theorem subtract_valid (x y z : ℝ) (hy : Functions.powerR.domain x y)
    (hz : Functions.powerR.domain x z) (hn : x^z≠0) : x^y/x^z=x^(y-z) := by
  by_cases hx : x=0
  · subst x
    have hz : z=0 := by by_contra h; exact hn (Real.zero_rpow h)
    simp [hz]
  · rcases lt_or_gt_of_ne hx with hx|hx
    · obtain ⟨k,rfl⟩ := negative_integral x y hx hy
      obtain ⟨l,rfl⟩ := negative_integral x z hx hz
      simpa only [← Int.cast_sub, Real.rpow_intCast] using (zpow_sub₀ (ne_of_lt hx) k l).symm
    · exact subtract hx y z

theorem subtract_domain (x y z : ℝ) (hy : Functions.powerR.domain x y)
    (hz : Functions.powerR.domain x z) (hn : x^z≠0) : Functions.powerR.domain x (y-z) := by
  by_cases hx : x=0
  · subst x
    have hz : z=0 := by by_contra h; exact hn (Real.zero_rpow h)
    simpa [hz] using hy
  · rcases lt_or_gt_of_ne hx with hx|hx
    · obtain ⟨k,rfl⟩ := negative_integral x y hx hy
      obtain ⟨l,rfl⟩ := negative_integral x z hx hz
      exact Or.inr (Or.inr ⟨hx,k-l,by push_cast; rfl⟩)
    · exact Or.inl hx

theorem subtract_product_valid (x y z : ℝ) (hy : Functions.powerR.domain x y)
    (hz : Functions.powerR.domain x z) (hn : x^z≠0) : x^z*x^(y-z)=x^y := by
  rw [← subtract_valid x y z hy hz hn]
  exact mul_div_cancel₀ _ hn

theorem complex_subtract_valid (x y z : ℂ) (hn : x^z≠0) : x^y/x^z=x^(y-z) := by
  by_cases hx : x=0
  · subst x
    have hz : z=0 := by by_contra h; exact hn (Complex.zero_cpow h)
    simp [hz]
  · exact complex_subtract hx y z

theorem complex_subtract_domain (x y z : ℂ) (hy : Functions.powerC.domain x y)
    (hn : x^z≠0) : Functions.powerC.domain x (y-z) := by
  by_cases hx : x=0
  · subst x
    have hz : z=0 := by by_contra h; exact hn (Complex.zero_cpow h)
    simpa [hz] using hy
  · exact Or.inl hx

theorem quotient_product (x y t : ℝ) (hx : 0<x) (hy : 0<y) : y^t*(x/y)^t=x^t := by
  rw [Real.div_rpow hx.le hy.le]
  exact mul_div_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hy t))

theorem subtract_normal (x y z : ℝ) (hy : Functions.powerR.domain x y)
    (hz : Functions.powerR.domain x z) (hn : x^z≠0) :
    (0<x ∨ x=0 ∧ z≤y ∨ x<0 ∧ ∃ k : ℤ, y-z=k) ∧ x^z*x^(y-z)=x^y := by
  simpa [Functions.powerR, sub_nonneg] using
    And.intro (subtract_domain x y z hy hz hn) (subtract_product_valid x y z hy hz hn)

theorem complex_subtract_normal (x y z : ℂ) (hy : Functions.powerC.domain x y)
    (hz : x=0 → z=0) :
    (x≠0 ∨ y=z ∨ z.re<y.re ∧ y.im=z.im) ∧ x^(y-z)=x^y/x^z := by
  have hn : x^z≠0 := by simpa using hz
  simpa [Functions.powerC, sub_eq_zero, sub_pos] using
    And.intro (complex_subtract_domain x y z hy hn) (complex_subtract_valid x y z hn).symm

end QSym.PowerRecovery
