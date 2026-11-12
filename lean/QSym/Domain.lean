import QSym.RefinementBase

namespace QSym.Domain
open Value

def Correct {α : Type} (x : Option α) (d : Option Bool) : Prop := d = some x.isSome

theorem leaf {α : Type} (x : α) : Correct (some x) (some true) := rfl

theorem transport {α β : Type} {x : Option α} {y : Option β} {d : Option Bool}
    (h : Defined y ↔ Defined x) (hx : Correct x d) : Correct y d := by
  cases x <;> cases y <;> simp_all [Correct, Defined]

theorem strict2 {α β γ : Type} {x : Option α} {y : Option β} {z : Option γ}
    {dx dy : Option Bool} (h : Defined z ↔ Defined x ∧ Defined y)
    (hx : Correct x dx) (hy : Correct y dy) : Correct z (Value.and dx dy) := by
  cases x <;> cases y <;> cases z <;> simp_all [Correct, Defined, Value.and]

theorem inverse {α : Type} [Zero α] [Inv α] {x : Option α} {d : Option Bool}
    (hx : Correct x d) : Correct (Value.inv x) (Value.and d (Value.nonzero x)) := by
  classical
  cases x with
  | none => simp_all [Correct, Value.inv, Value.and]
  | some x =>
    by_cases h : x=0 <;> simp_all [Correct, Value.inv, Value.nonzero, Value.and]

theorem mask {α : Type} [Zero α] {p : Option Bool} {x : Option α} {dp dx : Option Bool}
    (hp : Correct p dp) (hx : Correct x dx) :
    Correct (Value.mask p x) (Value.and dp (Value.or (Value.not p) dx)) := by
  cases p with
  | none => simp_all [Correct, Value.mask, Value.and]
  | some p => cases p <;> cases x <;> simp_all [Correct, Value.mask, Value.and, Value.or, Value.not]

theorem and {p q dp dq : Option Bool} (hp : Correct p dp) (hq : Correct q dq) :
    Correct (Value.and p q) (Value.and dp (Value.or (Value.not p) dq)) := by
  cases p with
  | none => simp_all [Correct, Value.and]
  | some p => cases p <;> cases q <;> simp_all [Correct, Value.and, Value.or, Value.not]

theorem or {p q dp dq : Option Bool} (hp : Correct p dp) (hq : Correct q dq) :
    Correct (Value.or p q) (Value.and dp (Value.or p dq)) := by
  cases p with
  | none => simp_all [Correct, Value.or, Value.and]
  | some p => cases p <;> cases q <;> simp_all [Correct, Value.and, Value.or]

theorem total1 {α β : Type} (f : Function1 α β) (ht : ∀ v, f.domain v)
    {x : Option α} {d : Option Bool} (hx : Correct x d) : Correct (f.apply x) d := by
  classical
  cases x <;> simpa [Correct, Function1.apply, ht] using hx

theorem total2 {α β γ : Type} (f : Function2 α β γ) (ht : ∀ a b, f.domain a b)
    {x : Option α} {y : Option β} {dx dy : Option Bool} (hx : Correct x dx) (hy : Correct y dy) :
    Correct (f.apply x y) (Value.and dx dy) := by
  classical
  cases x <;> cases y <;> simp_all [Correct, Function2.apply, ht, Value.and]

noncomputable def Test1 {α β} (f : Function1 α β) (x : Option α) (p : Option Bool) : Prop := by
  classical
  exact ∀ v, x=some v → p=some (decide (f.domain v))
noncomputable def Test2 {α β γ} (f : Function2 α β γ) (x : Option α) (y : Option β) (p : Option Bool) : Prop := by
  classical
  exact ∀ a b, x=some a → y=some b → p=some (decide (f.domain a b))

theorem partial1 {α β : Type} (f : Function1 α β) {x : Option α} {d p : Option Bool}
    (hp : Test1 f x p) (hx : Correct x d) : Correct (f.apply x) (Value.and d p) := by
  classical
  cases x with
  | none => simp_all [Correct, Function1.apply, Value.and]
  | some v =>
    have h := hp v rfl
    by_cases hd : f.domain v <;> simp_all [Correct, Function1.apply, Value.and]

theorem partial2 {α β γ : Type} (f : Function2 α β γ) {x : Option α} {y : Option β} {dx dy p : Option Bool}
    (hp : Test2 f x y p) (hx : Correct x dx) (hy : Correct y dy) :
    Correct (f.apply x y) (Value.and (Value.and dx dy) p) := by
  classical
  cases x with
  | none => simp_all [Correct, Function2.apply, Value.and]
  | some a =>
    cases y with
    | none => simp_all [Correct, Function2.apply, Value.and]
    | some b =>
      have h := hp a b rfl rfl
      by_cases hd : f.domain a b <;> simp_all [Correct, Function2.apply, Value.and]

theorem simplify {α : Type} {x : Option α} {d r : Option Bool}
    (h : Correct x d) (hr : Refines d r) : Correct x r := by
  exact hr x.isSome h

theorem Correct.total {α : Type} {x : Option α} {d : Option Bool} (h : Correct x d) : Defined d := ⟨_, h⟩

theorem Correct.iff {α : Type} {x : Option α} {d : Option Bool} (h : Correct x d) :
    Defined x ↔ d=some true := by
  cases x <;> simp_all [Correct, Defined]

theorem integer_test (x : ℝ) : (x = (⌊x⌋ : ℤ)) ↔ ∃ n : ℤ, x=n := by
  constructor
  · exact fun h => ⟨⌊x⌋, h⟩
  · rintro ⟨n, rfl⟩; simp

theorem gamma_test (x : ℝ) : (0<x ∨ ¬x=(⌊x⌋ : ℤ)) ↔ ∀ n : ℕ, x ≠ -(n : ℝ) := by
  rw [integer_test]
  constructor
  · rintro (h | h) n hn
    · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · exact h ⟨-(n : ℤ), by simpa using hn⟩
  · intro h
    by_cases hx : 0<x
    · exact Or.inl hx
    · right
      rintro ⟨n, rfl⟩
      have hn : n≤0 := by exact_mod_cast le_of_not_gt hx
      have he : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (neg_nonneg.mpr hn)
      apply h (-n).toNat
      have : (((-n).toNat : ℕ) : ℝ) = -(n : ℝ) := by exact_mod_cast he
      linarith

theorem complex_gamma_test (z : ℂ) :
    (z.im≠0 ∨ 0<z.re ∨ ¬z.re=(⌊z.re⌋ : ℤ)) ↔ ∀ n : ℕ, z ≠ -(n : ℂ) := by
  rw [gamma_test]
  constructor
  · rintro (hi | hr) n h
    · apply hi; simp [h]
    · apply hr n; simp [h]
  · intro h
    by_cases hi : z.im=0
    · right; intro n hr; apply h n
      apply Complex.ext <;> simp [hr, hi]
    · exact Or.inl hi

theorem and_some (p q : Bool) : Value.and (some p) (some q) = some (p && q) := by cases p <;> rfl
theorem or_some (p q : Bool) : Value.or (some p) (some q) = some (p || q) := by cases p <;> rfl

noncomputable def real (n : ℤ) : Option ℝ := some (n : ℝ)
noncomputable def complex (r i : ℤ) : Option ℂ := some ((r : ℂ) + (i : ℂ) * Complex.I)

noncomputable def poles (x : Option ℝ) :=
  Value.or (Value.lt (real 0) x) (Value.not (Functions.isIntR.apply x))

macro "domain_test" : tactic => `(tactic| (
  classical
  first | unfold Test1 | unfold Test2
  intros
  subst_vars
  simp [Function1.apply, Function2.apply, Value.nonzero, Value.lt, Value.le, Value.not,
    Value.add, and_some, or_some, real, complex, poles, Functions.invQ, Functions.sqrtR,
    Functions.logR, Functions.log2R, Functions.log10R, Functions.logC, Functions.argC,
    Functions.tanR, Functions.tanC, Functions.tanhC, Functions.cosR, Functions.cosC, Functions.coshC,
    Functions.asinR, Functions.acosR, Functions.atanhR, Functions.acoshR, Functions.atanC, Functions.atanhC,
    Functions.powQZ, Functions.powRZ, Functions.powCZ, Functions.powerR, Functions.powerC,
    Functions.atan2R, Functions.makeQ, Functions.nonzeroZ, Functions.nonzeroQ, Functions.leZ,
    Functions.reC, Functions.imC, Functions.isIntR, integer_test,
    sub_eq_add_neg, add_comm]
  all_goals simp only [← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  all_goals try simp [← sub_eq_add_neg, sub_eq_zero, add_eq_zero_iff_eq_neg]
))

theorem test_subN (x y : Option ℕ) : Test2 Functions.subN x y (Functions.leN.apply y x) := by
  classical
  intro a b hx hy
  simp [hx, hy, Function2.apply, Functions.subN, Functions.leN]

theorem test_invQ (x : Option ℚ) : Test1 Functions.invQ x (Functions.nonzeroQ.apply x) := by domain_test
theorem test_sqrtR (x : Option ℝ) : Test1 Functions.sqrtR x (Value.le (real 0) x) := by domain_test
theorem test_logR (x : Option ℝ) : Test1 Functions.logR x (Value.lt (real 0) x) := by domain_test
theorem test_log2R (x : Option ℝ) : Test1 Functions.log2R x (Value.lt (real 0) x) := by domain_test
theorem test_log10R (x : Option ℝ) : Test1 Functions.log10R x (Value.lt (real 0) x) := by domain_test
theorem test_logC (x : Option ℂ) : Test1 Functions.logC x (Value.nonzero x) := by domain_test
theorem test_argC (x : Option ℂ) : Test1 Functions.argC x (Value.nonzero x) := by domain_test
theorem test_tanR (x : Option ℝ) : Test1 Functions.tanR x (Value.nonzero (Functions.cosR.apply x)) := by domain_test
theorem test_tanC (x : Option ℂ) : Test1 Functions.tanC x (Value.nonzero (Functions.cosC.apply x)) := by domain_test
theorem test_tanhC (x : Option ℂ) : Test1 Functions.tanhC x (Value.nonzero (Functions.coshC.apply x)) := by domain_test
theorem test_asinR (x : Option ℝ) : Test1 Functions.asinR x
    (Value.and (Value.le (real (-1)) x) (Value.le x (real 1))) := by domain_test
theorem test_acosR (x : Option ℝ) : Test1 Functions.acosR x
    (Value.and (Value.le (real (-1)) x) (Value.le x (real 1))) := by domain_test
theorem test_acoshR (x : Option ℝ) : Test1 Functions.acoshR x (Value.le (real 1) x) := by domain_test
theorem test_atanhR (x : Option ℝ) : Test1 Functions.atanhR x
    (Value.and (Value.lt (real (-1)) x) (Value.lt x (real 1))) := by domain_test
theorem test_atanC (x : Option ℂ) : Test1 Functions.atanC x
    (Value.and (Value.nonzero (Value.add x (complex 0 (-1))))
      (Value.nonzero (Value.add x (complex 0 1)))) := by domain_test
theorem test_atanhC (x : Option ℂ) : Test1 Functions.atanhC x
    (Value.and (Value.nonzero (Value.add x (complex (-1) 0)))
      (Value.nonzero (Value.add x (complex 1 0)))) := by domain_test
theorem test_powQZ (x : Option ℚ) (y : Option ℤ) : Test2 Functions.powQZ x y
    (Value.or (Functions.nonzeroQ.apply x) (Functions.leZ.apply (some 0) y)) := by domain_test
theorem test_powRZ (x : Option ℝ) (y : Option ℤ) : Test2 Functions.powRZ x y
    (Value.or (Value.nonzero x) (Functions.leZ.apply (some 0) y)) := by domain_test
theorem test_powCZ (x : Option ℂ) (y : Option ℤ) : Test2 Functions.powCZ x y
    (Value.or (Value.nonzero x) (Functions.leZ.apply (some 0) y)) := by domain_test
theorem real_power_domain (x y : ℝ) :
    ((0≤x ∨ ∃ n : ℤ, y=n) ∧ (x≠0 ∨ 0≤y)) ↔ Functions.powerR.domain x y := by
  unfold Functions.powerR
  by_cases hx : x=0
  · simp [hx]
  · by_cases hp : 0<x
    · simp [hx, hp, le_of_lt hp]
    · have hn : x<0 := lt_of_le_of_ne (le_of_not_gt hp) hx
      simp [hx, hp, hn, not_le.mpr hn]

theorem test_powerR (x y : Option ℝ) : Test2 Functions.powerR x y
    (Value.and (Value.or (Value.le (real 0) x) (Functions.isIntR.apply y))
      (Value.or (Value.nonzero x) (Value.le (real 0) y))) := by
  domain_test
  exact real_power_domain _ _

theorem complex_power_domain (x y : ℂ) :
    (x≠0 ∨ (0≤y.re ∧ y.im=0)) ↔ Functions.powerC.domain x y := by
  unfold Functions.powerC
  by_cases hx : x=0
  · simp only [hx, ne_eq, not_true_eq_false, false_or]
    constructor
    · rintro ⟨hr, hi⟩
      rcases eq_or_lt_of_le hr with he | he
      · left; apply Complex.ext <;> simp [← he, hi]
      · exact Or.inr ⟨he, hi⟩
    · rintro (rfl | ⟨hr, hi⟩)
      · simp
      · exact ⟨le_of_lt hr, hi⟩
  · simp [hx]

theorem test_powerC (x y : Option ℂ) : Test2 Functions.powerC x y
    (Value.or (Value.nonzero x) (Value.and (Value.le (real 0) (Functions.reC.apply y))
      (Value.not (Value.nonzero (Functions.imC.apply y))))) := by
  domain_test
  exact complex_power_domain _ _
theorem test_atan2R (x y : Option ℝ) : Test2 Functions.atan2R x y
    (Value.or (Value.nonzero y) (Value.nonzero x)) := by domain_test
theorem test_makeQ (x y : Option ℤ) : Test2 Functions.makeQ x y (Functions.nonzeroZ.apply y) := by domain_test
theorem poles_some (x : ℝ) : poles (some x) = some (decide (0<x ∨ ¬x=(⌊x⌋ : ℤ))) := by
  classical
  simp [poles, real, Value.lt, Value.not, Function1.apply, Functions.isIntR, or_some]

theorem test_gammaR (x : Option ℝ) : Test1 Functions.gammaR x (poles x) := by
  classical
  intro v h; subst x
  change poles (some v) = some (decide (∀ n : ℕ, v ≠ -(n : ℝ)))
  rw [← gamma_test]
  rw [poles_some]
  congr 1
  exact decide_eq_decide.mpr Iff.rfl

theorem test_gammaC (x : Option ℂ) : Test1 Functions.gammaC x
    (Value.or (Value.nonzero (Functions.imC.apply x)) (poles (Functions.reC.apply x))) := by
  classical
  intro v h; subst x
  change _ = some (decide (∀ n : ℕ, v ≠ -(n : ℂ)))
  rw [← complex_gamma_test]
  simp [Function1.apply, Functions.imC, Functions.reC, Value.nonzero, poles_some,
    or_some]

theorem test_lgammaR (x : Option ℝ) : Test1 Functions.lgammaR x
    (Value.and (poles x) (Value.nonzero (Functions.gammaR.apply x))) := by
  classical
  intro v h; subst x
  dsimp only [Functions.lgammaR]
  rw [← gamma_test, poles_some]
  by_cases hd : 0<v ∨ ¬v=(⌊v⌋ : ℤ)
  · have hg := (gamma_test v).mp hd
    simp [hd, Value.and, Value.nonzero, Function1.apply, Functions.gammaR, hg]
  · simp [hd, Value.and]

end QSym.Domain
