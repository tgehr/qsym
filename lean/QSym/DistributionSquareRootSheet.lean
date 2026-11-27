import QSym.DistributionQuadraticFibre

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates
open Classical

/-- A partial affine function of one real square root. Multiplication remains
strict, so even a zero coefficient retains the domain of the root. -/
structure RootSheet (f : ℝ → Option ℝ) (c k a b : ℚ) : Prop where
  equation : ∀ y, f y = (Functions.sqrtR.apply (some ((a:ℝ)*y+b))).map
    (fun r => (c:ℝ)+(k:ℝ)*r)

namespace RootSheet

theorem root {g : ℝ → Option ℝ} {a b : ℚ} (hg : StepSource.Affine g a b) :
    RootSheet (fun y => Functions.sqrtR.apply (g y)) 0 1 a b := by
  constructor
  intro y
  rw [hg.equation y]
  cases Functions.sqrtR.apply (some ((a:ℝ)*y+b)) <;> simp

theorem add_left {f c k a b} (hf : RootSheet f c k a b) (q : ℚ) {v : Option ℝ}
    (hv : v = some (q:ℝ)) : RootSheet (fun y => Value.add v (f y)) (q+c) k a b := by
  subst v; constructor; intro y; rw [hf.equation y]
  cases Functions.sqrtR.apply (some ((a:ℝ)*y+b)) <;> simp [Value.add, add_assoc]

theorem add_right {f c k a b} (hf : RootSheet f c k a b) (q : ℚ) {v : Option ℝ}
    (hv : v = some (q:ℝ)) : RootSheet (fun y => Value.add (f y) v) (c+q) k a b := by
  subst v; constructor; intro y; rw [hf.equation y]
  cases Functions.sqrtR.apply (some ((a:ℝ)*y+b)) <;> simp [Value.add]; ring

theorem mul_left {f c k a b} (hf : RootSheet f c k a b) (q : ℚ) {v : Option ℝ}
    (hv : v = some (q:ℝ)) : RootSheet (fun y => Value.mul v (f y)) (q*c) (q*k) a b := by
  subst v; constructor; intro y; rw [hf.equation y]
  cases Functions.sqrtR.apply (some ((a:ℝ)*y+b)) <;> simp [Value.mul]; ring

theorem mul_right {f c k a b} (hf : RootSheet f c k a b) (q : ℚ) {v : Option ℝ}
    (hv : v = some (q:ℝ)) : RootSheet (fun y => Value.mul (f y) v) (c*q) (k*q) a b := by
  subst v; constructor; intro y; rw [hf.equation y]
  cases Functions.sqrtR.apply (some ((a:ℝ)*y+b)) <;> simp [Value.mul]; ring

abbrev pair (l r : ℝ → Option ℝ) :=
  Tensor.consValue (some l) (Tensor.consValue (some r) Tensor.nilValue)

/-- Recover the forward quadratic directly from two displayed sheets. Their
common endpoint appears only once in the inverse relation. Either ordering
of the two coordinates gives the same result. -/
theorem image {l r : ℝ → Option ℝ} {c k a b : ℚ}
    (hl : RootSheet l c (-k) a b) (hr : RootSheet r c k a b)
    (hk : k ≠ 0) (ha : a ≠ 0) :
    value (pair l r) = realPushforwardOnValue (some fun _ => some true)
      (some fun x => some (((x-(c:ℝ))^2-(k:ℝ)^2*b)/((k:ℝ)^2*a))) := by
  let C : ℝ := c
  let K : ℝ := k
  let A : ℝ := a
  let B : ℝ := b
  have hk' : K ≠ 0 := by change (k:ℝ) ≠ 0; exact_mod_cast hk
  have ha' : A ≠ 0 := by change (a:ℝ) ≠ 0; exact_mod_cast ha
  have den : K^2*A ≠ 0 := mul_ne_zero (pow_ne_zero _ hk') ha'
  let gs : Fin 2 → ℝ → Option ℝ := Fin.cases l (Fin.cases r Fin.elim0)
  change value (some gs) = _
  symm
  apply image_of_cover_gap (gap := (-1-B)/A)
  · have neg : A*((-1-B)/A)+B < 0 := by field_simp [ha']
    have noRoot : Functions.sqrtR.apply (some (A*((-1-B)/A)+B)) = none := by
      simp [Functions.sqrtR, Function1.apply, not_le.mpr neg]
    intro i; fin_cases i
    · exact (hl.equation _).trans (congrArg (Option.map _) noRoot)
    · exact (hr.equation _).trans (congrArg (Option.map _) noRoot)
  · intro x y
    have both : (∃ i, gs i y = some x) ↔ l y = some x ∨ r y = some x := by
      constructor
      · rintro ⟨i, hi⟩; fin_cases i <;> tauto
      · exact fun h => h.elim (fun p => ⟨0,p⟩) (fun p => ⟨1,p⟩)
    rw [both, hl.equation y, hr.equation y, Option.some.injEq, Rat.cast_neg]
    change _ ↔ ((x-C)^2-K^2*B)/(K^2*A) = y
    by_cases hn : 0 ≤ A*y+B
    · have root : Functions.sqrtR.apply (some (A*y+B)) = some (√(A*y+B)) := by
        simp [Functions.sqrtR, Function1.apply, hn]
      rw [root]
      change some (C+(-K)*√(A*y+B)) = some x ∨ some (C+K*√(A*y+B)) = some x ↔ _
      simp only [Option.some.injEq]
      have sq : (K*√(A*y+B))^2 = K^2*(A*y+B) := by rw [mul_pow, Real.sq_sqrt hn]
      constructor
      · rintro (hx | hx) <;> rw [← hx] <;> apply (div_eq_iff den).2
        all_goals calc
          _ = (K*√(A*y+B))^2-K^2*B := by ring
          _ = _ := by rw [sq]; ring
      · intro h
        have e := (div_eq_iff den).1 h
        have eq : (x-C)^2 = (K*√(A*y+B))^2 := by
          rw [sq]
          linear_combination e
        rcases (sq_eq_sq_iff_eq_or_eq_neg.mp eq) with z | z
        · right; linear_combination -z
        · left; linear_combination -z
    · have root : Functions.sqrtR.apply (some (A*y+B)) = none := by simp [Functions.sqrtR, Function1.apply, hn]
      rw [root]
      change (none = some x ∨ none = some x) ↔ _
      simp only [reduceCtorEq, or_self, false_iff]
      intro h
      have e := (div_eq_iff den).1 h
      have hn' := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hk') (lt_of_not_ge hn)
      nlinarith only [e,hn',sq_nonneg (x-C)]

/-- Observe the displayed coordinates directly, including their common
critical endpoint. The affine Jacobian and its argument use checked rationals. -/
theorem density (c k a b t u j : ℚ) (hk : k ≠ 0) (ha : a ≠ 0)
    (ht : t = k^2*a) (hu : u = k^2*b) (hj : j = |t|)
    {l r : ℝ → Option ℝ} (hl : RootSheet l c (-k) a b) (hr : RootSheet r c k a b)
    {scale offset gain : Option ℝ} (hs : scale = some (t:ℝ)) (ho : offset = some (u:ℝ))
    (hg : gain = some (j:ℝ)) (y : Option ℝ) :
    densityAtValue (value (pair l r)) y =
      unrestrictedSquareDensity gain (Value.add (Value.mul scale y) offset) := by
  subst scale; subst offset; subst gain; subst j; subst t; subst u
  rw [image hl hr hk ha, Rat.cast_abs]
  have hn : (k:ℝ)^2 * a ≠ 0 := by exact_mod_cast mul_ne_zero (pow_ne_zero 2 hk) ha
  have arg : Value.add (Value.mul (some ((k:ℝ)^2*a)) y) (some ((k:ℝ)^2*b)) =
      y.map (fun z => (k:ℝ)^2*a*z+(k:ℝ)^2*b) := by cases y <;> rfl
  simp only [Rat.cast_mul, Rat.cast_pow, arg]
  exact Quadratic.density c _ _ hn y

end RootSheet
end QSym.Distribution.GraphFibre.Coordinates
