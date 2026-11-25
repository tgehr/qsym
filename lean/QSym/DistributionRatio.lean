import QSym.DistributionGaussianSymbolic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
A polynomial over a power of the axis, between two bounds. Such a quotient is
undefined at zero and, where a negative power is left, not integrable next
to it. So it is observed exactly between bounds on one side of zero, and
its antiderivative has a polynomial, a polynomial over a power of the axis
and a logarithm of the absolute value.
-/

namespace QSym.Distribution.StepSource

open MeasureTheory Set Filter Topology

/-- The value is a polynomial over a power of the axis away from zero, and
undefined at zero. -/
structure RatioOn (v : ℝ → Option ℝ) (p : List ℚ) (N : ℕ) : Prop where
  equation : ∀ x : ℝ, x ≠ 0 → v x = some (polyEval p x * (x⁻¹) ^ N)
  undefined : v 0 = none

/-- A monomial `c·xⁿ`. -/
def polyMonomial (c : ℚ) : ℕ → List ℚ
  | 0 => [c]
  | n + 1 => 0 :: polyMonomial c n

theorem polyEval_monomial (c : ℚ) (n : ℕ) (x : ℝ) :
    polyEval (polyMonomial c n) x = c * x ^ n := by
  induction n with
  | zero => simp [polyMonomial, polyEval]
  | succ n ih =>
    simp only [polyMonomial, polyEval, ih]
    push_cast
    ring

/-- The polynomial is the monomial `c·xⁿ` with `c ≠ 0` and `0 < n`. -/
def monomialCheck (q : List ℚ) (c : ℚ) (n : ℕ) : Bool :=
  polyZero (polyAdd q (polyScale (-1) (polyMonomial c n))) && decide (c ≠ 0) && decide (0 < n)

/-- The inverse of such a monomial. -/
theorem ratio_inv {f : ℝ → Option ℝ} {q : List ℚ} (hf : PolynomialOn (fun _ => True) f q)
    (c : ℚ) (n : ℕ) (h : monomialCheck q c n = true) :
    RatioOn (fun x => Value.inv (f x)) [c⁻¹] n := by
  simp only [monomialCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hq, hc⟩, hn⟩ := h
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hval : ∀ x : ℝ, f x = some ((c : ℝ) * x ^ n) := fun x => by
    rw [hf.equation x trivial]
    have h0 := polyEval_zero hq x
    rw [polyEval_add, polyEval_scale, polyEval_monomial] at h0
    push_cast at h0
    congr 1
    linarith
  refine ⟨fun x hx => ?_, ?_⟩
  · show Value.inv (f x) = _
    rw [hval x]
    have hne : (c : ℝ) * x ^ n ≠ 0 := mul_ne_zero hcR (pow_ne_zero n hx)
    have hinv : Value.inv (some ((c : ℝ) * x ^ n)) = some (((c : ℝ) * x ^ n)⁻¹) := by
      simp [Value.inv, hne]
    rw [hinv]
    simp only [polyEval, Option.some.injEq]
    push_cast
    rw [mul_inv, inv_pow]
    ring
  · show Value.inv (f 0) = none
    rw [hval 0, zero_pow (Nat.pos_iff_ne_zero.mp hn), mul_zero]
    simp [Value.inv]

/-- Under a polynomial factor, on either side. -/
theorem ratio_mul_left {f g : ℝ → Option ℝ} {q p : List ℚ} {N : ℕ}
    (hf : PolynomialOn (fun _ => True) f q) (hg : RatioOn g p N) :
    RatioOn (fun x => Value.mul (f x) (g x)) (polyMul q p) N :=
  ⟨fun x hx => by
    show Value.mul (f x) (g x) = _
    rw [hf.equation x trivial, hg.equation x hx, polyEval_mul]
    simp only [Value.mul, Option.some.injEq]
    ring, by
    show Value.mul (f 0) (g 0) = none
    rw [hf.equation 0 trivial, hg.undefined]
    rfl⟩

theorem ratio_mul_right {f g : ℝ → Option ℝ} {q p : List ℚ} {N : ℕ}
    (hg : RatioOn g p N) (hf : PolynomialOn (fun _ => True) f q) :
    RatioOn (fun x => Value.mul (g x) (f x)) (polyMul p q) N :=
  ⟨fun x hx => by
    show Value.mul (g x) (f x) = _
    rw [hf.equation x trivial, hg.equation x hx, polyEval_mul]
    simp only [Value.mul, Option.some.injEq]
    ring, by
    show Value.mul (g 0) (f 0) = none
    rw [hg.undefined]
    rfl⟩

/-- The product of two quotients. -/
theorem ratio_mul {f g : ℝ → Option ℝ} {p q : List ℚ} {n m : ℕ}
    (hf : RatioOn f p n) (hg : RatioOn g q m) :
    RatioOn (fun x => Value.mul (f x) (g x)) (polyMul p q) (n + m) :=
  ⟨fun x hx => by
    show Value.mul (f x) (g x) = _
    rw [hf.equation x hx, hg.equation x hx, polyEval_mul, pow_add]
    simp only [Value.mul, Option.some.injEq]
    ring, by
    show Value.mul (f 0) (g 0) = none
    rw [hf.undefined]
    rfl⟩

/-- The sum with a polynomial, on either side. -/
theorem ratio_add_left {f g : ℝ → Option ℝ} {q p : List ℚ} {N : ℕ}
    (hf : PolynomialOn (fun _ => True) f q) (hg : RatioOn g p N) :
    RatioOn (fun x => Value.add (f x) (g x)) (polyAdd (polyMul q (polyMonomial 1 N)) p) N :=
  ⟨fun x hx => by
    show Value.add (f x) (g x) = _
    rw [hf.equation x trivial, hg.equation x hx, polyEval_add, polyEval_mul, polyEval_monomial]
    simp only [Value.add, Option.some.injEq]
    have h1 : x ^ N * (x⁻¹) ^ N = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
    push_cast
    linear_combination (-(polyEval q x)) * h1, by
    show Value.add (f 0) (g 0) = none
    rw [hf.equation 0 trivial, hg.undefined]
    rfl⟩

theorem ratio_add_right {f g : ℝ → Option ℝ} {q p : List ℚ} {N : ℕ}
    (hg : RatioOn g p N) (hf : PolynomialOn (fun _ => True) f q) :
    RatioOn (fun x => Value.add (g x) (f x)) (polyAdd p (polyMul q (polyMonomial 1 N))) N :=
  ⟨fun x hx => by
    show Value.add (g x) (f x) = _
    rw [hf.equation x trivial, hg.equation x hx, polyEval_add, polyEval_mul, polyEval_monomial]
    simp only [Value.add, Option.some.injEq]
    have h1 : x ^ N * (x⁻¹) ^ N = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
    push_cast
    linear_combination (-(polyEval q x)) * h1, by
    show Value.add (g 0) (f 0) = none
    rw [hg.undefined]
    rfl⟩

/-- The sum of two quotients, over the product of the two powers. -/
theorem ratio_add {f g : ℝ → Option ℝ} {p q : List ℚ} {n m : ℕ}
    (hf : RatioOn f p n) (hg : RatioOn g q m) :
    RatioOn (fun x => Value.add (f x) (g x))
      (polyAdd (polyMul p (polyMonomial 1 m)) (polyMul q (polyMonomial 1 n))) (n + m) :=
  ⟨fun x hx => by
    show Value.add (f x) (g x) = _
    rw [hf.equation x hx, hg.equation x hx, polyEval_add, polyEval_mul, polyEval_mul,
      polyEval_monomial, polyEval_monomial, pow_add]
    simp only [Value.add, Option.some.injEq]
    have hn : x ^ n * (x⁻¹) ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
    have hm : x ^ m * (x⁻¹) ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
    push_cast
    linear_combination (-(polyEval p x * (x⁻¹) ^ n)) * hm - (polyEval q x * (x⁻¹) ^ m) * hn, by
    show Value.add (f 0) (g 0) = none
    rw [hf.undefined]
    rfl⟩

/-! Next to zero the quotient is not integrable where a negative power is
left: times a power of the axis it is the lowest coefficient over the axis
plus a polynomial, and the inverse is not integrable there. -/

/-- On a bounded set away from zero on which the inverse is not integrable, a
quotient that is integrable has no negative power left. -/
theorem ratio_not_integrableOn {s : Set ℝ} (hs : MeasurableSet s) (hb : Bornology.IsBounded s)
    (h0 : (0 : ℝ) ∉ s) (hinv : ¬ IntegrableOn (fun x : ℝ => x⁻¹) s volume) :
    ∀ (N : ℕ) (p : List ℚ), IntegrableOn (fun x : ℝ => polyEval p x * (x⁻¹) ^ N) s volume →
      polyZero (p.take N) = true := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℝ)
  have hsub : s ⊆ Icc (-R) R := by
    intro x hx
    have := hR hx
    rw [Real.closedBall_eq_Icc] at this
    simpa using this
  have hcont : ∀ g : ℝ → ℝ, Continuous g → IntegrableOn g s volume := fun g hg =>
    (hg.continuousOn.integrableOn_Icc (a := -R) (b := R)).mono_set hsub
  intro N
  induction N with
  | zero => intro p _; simp [polyZero]
  | succ N ih =>
    intro p hi
    cases p with
    | nil => simp [polyZero]
    | cons c q =>
      have hx0 : ∀ x ∈ s, x ≠ 0 := fun x hx h => h0 (h ▸ hx)
      have hmul : IntegrableOn
          (fun x : ℝ => x ^ N * (polyEval (c :: q) x * (x⁻¹) ^ (N + 1))) s volume := by
        refine Integrable.bdd_mul' (c := |R| ^ N) hi
          ((continuous_pow N).aestronglyMeasurable) ?_
        refine (ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx => ?_)
        have hxR : |x| ≤ |R| := by
          have h1 := hsub hx
          rw [abs_le]
          constructor
          · linarith [h1.1, neg_abs_le R, le_abs_self R]
          · linarith [h1.2, le_abs_self R]
        rw [norm_pow, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg x) hxR N
      have hsum : IntegrableOn (fun x : ℝ => (c : ℝ) * x⁻¹ + polyEval q x) s volume := by
        refine hmul.congr_fun (fun x hx => ?_) hs
        have hne := hx0 x hx
        have h1 : x ^ N * (x⁻¹) ^ N = 1 := by rw [← mul_pow, mul_inv_cancel₀ hne, one_pow]
        have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hne
        simp only [polyEval, pow_succ]
        linear_combination ((c : ℝ) * x⁻¹ + polyEval q x * (x * x⁻¹)) * h1 + polyEval q x * h2
      have hcinv : IntegrableOn (fun x : ℝ => (c : ℝ) * x⁻¹) s volume := by
        have hdiff : IntegrableOn (fun x : ℝ => (c : ℝ) * x⁻¹ + polyEval q x - polyEval q x) s
            volume := hsum.sub (hcont _ (polyEval_continuous q))
        refine hdiff.congr_fun (fun x _ => ?_) hs
        ring
      have hc0 : c = 0 := by
        rcases eq_or_ne c 0 with h | hne
        · exact h
        · have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hne
          have hscaled : IntegrableOn (fun x : ℝ => (c : ℝ)⁻¹ * ((c : ℝ) * x⁻¹)) s volume :=
            hcinv.const_mul _
          exact absurd (hscaled.congr_fun (fun x _ => by
            show (c : ℝ)⁻¹ * ((c : ℝ) * x⁻¹) = x⁻¹
            rw [← mul_assoc, inv_mul_cancel₀ hcR, one_mul]) hs) hinv
      subst hc0
      have hq : IntegrableOn (fun x : ℝ => polyEval q x * (x⁻¹) ^ N) s volume := by
        refine hi.congr_fun (fun x hx => ?_) hs
        have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ (hx0 x hx)
        simp only [polyEval, pow_succ, Rat.cast_zero, zero_add]
        linear_combination (polyEval q x * (x⁻¹) ^ N) * h2
      have := ih q hq
      simpa [polyZero, List.take] using this

private theorem inv_not_integrableOn_Ioo_right {u : ℝ} (hu : 0 < u) :
    ¬ IntegrableOn (fun x : ℝ => x⁻¹) (Ioo 0 u) volume := by
  intro hi
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le hu.le).2 hi
  rcases intervalIntegrable_inv_iff.1 h with h1 | h1
  · exact hu.ne h1
  · exact h1 (left_mem_uIcc)

private theorem inv_not_integrableOn_Ioo_left {l : ℝ} (hl : l < 0) :
    ¬ IntegrableOn (fun x : ℝ => x⁻¹) (Ioo l 0) volume := by
  intro hi
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le hl.le).2 hi
  rcases intervalIntegrable_inv_iff.1 h with h1 | h1
  · exact hl.ne h1
  · exact h1 (right_mem_uIcc)

/-! The antiderivative `A(x) + C(x)/x^M + κ·log|x|`. -/

/-- The checks of an antiderivative: a negative power is left, and
`x^(M+1)·A' + x·C' - M·C + κ·x^M = p·x^(M+1-N)`, which says that the
derivative is the quotient. -/
def ratioCheck (p : List ℚ) (N M : ℕ) (A C : List ℚ) (κ : ℚ) : Bool :=
  decide (0 < N) && decide (0 < M) && decide (N ≤ M + 1) && !polyZero (p.take N) &&
    polyZero (polyAdd
      (polyAdd (polyAdd (polyMul (polyMonomial 1 (M + 1)) (polyDerivative A))
        (polyMul [0, 1] (polyDerivative C)))
        (polyAdd (polyScale (-(M : ℚ)) C) (polyMonomial κ M)))
      (polyScale (-1) (polyMul p (polyMonomial 1 (M + 1 - N)))))

theorem ratio_hasDerivAt {p : List ℚ} {N M : ℕ} {A C : List ℚ} {κ : ℚ}
    (h : ratioCheck p N M A C κ = true) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => polyEval A t + polyEval C t * (t ^ M)⁻¹ + κ * Real.log t)
      (polyEval p x * (x⁻¹) ^ N) x := by
  simp only [ratioCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨_, hM⟩, hNM⟩, _⟩, hz⟩ := h
  have hid := polyEval_zero hz x
  simp only [polyEval_add, polyEval_mul, polyEval_scale, polyEval_monomial, polyEval] at hid
  push_cast at hid
  have hpow : HasDerivAt (fun t : ℝ => (t ^ M)⁻¹) (-(M * x ^ (M - 1)) / (x ^ M) ^ 2) x :=
    (hasDerivAt_pow M x).inv (pow_ne_zero M hx)
  have hF := ((polyEval_hasDerivAt A x).add ((polyEval_hasDerivAt C x).mul hpow)).add
    ((Real.hasDerivAt_log hx).const_mul (κ : ℝ))
  refine hF.congr_deriv ?_
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hM)
  have hX : x ^ (M' + 1 + 1) ≠ 0 := pow_ne_zero _ hx
  have hN : (x⁻¹) ^ N * x ^ (M' + 1 + 1) = x ^ (M' + 1 + 1 - N) := by
    have hsplit : x ^ (M' + 1 + 1) = x ^ (M' + 1 + 1 - N) * x ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hNM]
    rw [hsplit, inv_pow]
    field_simp
  apply mul_right_cancel₀ hX
  have hgoal : polyEval p x * (x⁻¹) ^ N * x ^ (M' + 1 + 1) =
      polyEval p x * x ^ (M' + 1 + 1 - N) := by rw [mul_assoc, hN]
  rw [hgoal]
  simp only [Nat.add_sub_cancel]
  have hy : (x ^ (M' + 1))⁻¹ * x ^ (M' + 1) = 1 := inv_mul_cancel₀ (pow_ne_zero _ hx)
  have hyx : (x ^ (M' + 1))⁻¹ * x ^ (M' + 1 + 1) = x := by
    rw [pow_succ x (M' + 1), ← mul_assoc, hy, one_mul]
  have hxX : x⁻¹ * x ^ (M' + 1 + 1) = x ^ (M' + 1) := by
    rw [pow_succ x (M' + 1), mul_comm (x ^ (M' + 1)) x, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  have hdiv : -(((M' + 1 : ℕ) : ℝ) * x ^ M') / (x ^ (M' + 1)) ^ 2 * x ^ (M' + 1 + 1) =
      -((M' : ℝ) + 1) := by
    field_simp
    ring
  push_cast at hid hdiv ⊢
  linear_combination hid + polyEval (polyDerivative C) x * hyx + polyEval C x * hdiv +
    (κ : ℝ) * hxX

/-- The antiderivative at a bound: a polynomial, another over a power of the
bound, and a constant times the logarithm of its absolute value. -/
noncomputable def ratioPrimitive (M : ℕ) (pa pc k o : Option ℝ) : Option ℝ :=
  Value.add (Value.add pa (Value.mul pc (Value.inv (curvaturePower o M))))
    (Value.mul k (Functions.logR.apply (Value.abs o)))

private theorem row_sum {c p : Option ℝ} {Q : List ℚ} {qs : List (Option ℝ)}
    (hq : RowTerms none c Q 0 [] qs) (hp : Sums qs p) (t : ℝ) (hc : c = some t) :
    p = some (polyEval Q t) := by
  rw [hp.value, hq.value t hc (by simp)]
  simp [factorReal, listSum, Value.add]

private theorem ratioPrimitive_some {M : ℕ} {A C : List ℚ} {κ : ℚ} {pa pc k o : Option ℝ}
    {msa msc : List (Option ℝ)} (ha : RowTerms none o A 0 [] msa) (hsa : Sums msa pa)
    (hc : RowTerms none o C 0 [] msc) (hsc : Sums msc pc)
    (hk : k = some (Numeric.denote (s := .real) κ)) {t : ℝ} (ho : o = some t) (ht : t ≠ 0) :
    ratioPrimitive M pa pc k o =
      some (polyEval A t + polyEval C t * (t ^ M)⁻¹ + κ * Real.log t) := by
  subst ho
  rw [ratioPrimitive, row_sum ha hsa t rfl, row_sum hc hsc t rfl, hk, curvaturePower_some]
  have hpos : 0 < |t| := abs_pos.2 ht
  simp [Value.add, Value.mul, Value.inv, Value.abs, Function1.apply, Functions.logR, hpos,
    pow_ne_zero M ht, Numeric.denote, Real.log_abs]

private theorem compare_some (s : Bool) (l u : ℝ) :
    compare s (some l) (some u) = some (decide (if s = true then l < u else l ≤ u)) := by
  cases s <;> simp [compare, Value.lt, Value.le]

/-- Between two bounds: under the mask of their comparison, the difference of
the antiderivative under the guard that both are on one side of zero. Where
zero is between them the quotient is undefined there, or it is next to them
and the quotient not integrable. -/
theorem ratio_between (swap sl su : Bool) {a b : Option ℝ} {v : ℝ → Option ℝ} {p : List ℚ}
    {N : ℕ} (M : ℕ) (A C : List ℚ) (κ : ℚ) (hv : RatioOn v p N)
    (hc : ratioCheck p N M A C κ = true) {z m k ab aa cb ca : Option ℝ}
    {msab msaa mscb msca : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) κ))
    (hab : RowTerms none b A 0 [] msab) (hsab : Sums msab ab)
    (hcb : RowTerms none b C 0 [] mscb) (hscb : Sums mscb cb)
    (haa : RowTerms none a A 0 [] msaa) (hsaa : Sums msaa aa)
    (hca : RowTerms none a C 0 [] msca) (hsca : Sums msca ca) :
    partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x) (v x)) =
      Value.mask (compare (sl || su) a b) (Binding.guardValue
        (Value.or (Value.lt z a) (Value.lt b z))
        (Value.add (ratioPrimitive M ab cb k b) (Value.mul m (ratioPrimitive M aa ca k a)))) := by
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hMinus : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  subst hZ hMinus
  have missing : ∀ (f : ℝ → Option ℝ) (y : ℝ), f y = none → partialIntegral volume f = none := by
    intro f y hy
    apply if_neg
    intro hd
    obtain ⟨r, hr⟩ := hd.1 y
    rw [hy] at hr
    cases hr
  cases a with
  | none =>
    have hn : compare (sl || su) none b = none := by cases sl <;> cases su <;> rfl
    rw [hn]
    cases b with
    | none =>
      exact missing _ 0 (by cases swap <;> cases sl <;> cases su <;> rfl)
    | some u =>
      refine missing _ (u - 1) ?_
      cases swap <;> cases sl <;> cases su <;>
        simp [intervalGuard, compare, Value.and, Value.lt, Value.le, Value.mask]
  | some l =>
    cases b with
    | none =>
      have hn : compare (sl || su) (some l) none = none := by cases sl <;> cases su <;> rfl
      rw [hn]
      refine missing _ (l + 1) ?_
      cases swap <;> cases sl <;> cases su <;>
        simp [intervalGuard, compare, Value.and, Value.lt, Value.le, Value.mask]
    | some u =>
      have hf : Masked (fun x => Value.mask (intervalGuard swap sl su (some l) (some u) x) (v x))
          (intervalGuard swap sl su (some l) (some u)) v := ⟨fun _ => rfl⟩
      rw [compare_some]
      by_cases hT : (if (sl || su) = true then l < u else l ≤ u)
      · have hlu : l ≤ u := by
          split_ifs at hT
          · exact hT.le
          · exact hT
        have hmask : ∀ X : Option ℝ, Value.mask (some (decide
            (if (sl || su) = true then l < u else l ≤ u))) X = X := fun X => by
          rw [decide_eq_true hT]
          rfl
        rw [hmask]
        have hbound : ∀ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
            (if su = true then x < u else x ≤ u)) → l ≤ x ∧ x ≤ u := fun x hx => by
          obtain ⟨h1, h2⟩ := hx
          constructor
          · split_ifs at h1
            · exact h1.le
            · exact h1
          · split_ifs at h2
            · exact h2.le
            · exact h2
        by_cases hside : 0 < l ∨ u < 0
        · -- Both bounds on one side of zero: the quotient is continuous between them.
          have hne : ∀ x : ℝ, l ≤ x → x ≤ u → x ≠ 0 := fun x h1 h2 h0 => by
            rcases hside with h | h <;> linarith
          have hg : ∀ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
              (if su = true then x < u else x ≤ u)) →
              v x = some (polyEval p x * (x⁻¹) ^ N) := fun x hx =>
            hv.equation x (hne x (hbound x hx).1 (hbound x hx).2)
          have hcont : ContinuousOn (fun x : ℝ => polyEval p x * (x⁻¹) ^ N) (Icc l u) := by
            refine (polyEval_continuous p).continuousOn.mul (ContinuousOn.pow ?_ N)
            exact continuousOn_inv₀.mono fun x hx => hne x hx.1 hx.2
          have hint : IntegrableOn (fun x : ℝ => polyEval p x * (x⁻¹) ^ N) (Ioo l u) volume :=
            hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
          rw [(interval_observation_value swap sl su l u hf hg).1 hint,
            ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlu,
            intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun x hx => ratio_hasDerivAt hc (by
                rw [uIcc_of_le hlu] at hx
                exact hne x hx.1 hx.2))
              ((hcont.mono (by rw [uIcc_of_le hlu])).intervalIntegrable),
            ratioPrimitive_some hab hsab hcb hscb hk rfl (hne u hlu le_rfl),
            ratioPrimitive_some haa hsaa hca hsca hk rfl (hne l le_rfl hlu)]
          have hguard : Value.or (Value.lt (some (0 : ℝ)) (some l)) (Value.lt (some u) (some 0)) =
              some true := by
            rcases hside with h | h
            · simp [Value.or, Value.lt, h]
            · by_cases h' : 0 < l <;> simp [Value.or, Value.lt, h, h']
          rw [hguard]
          simp only [Binding.guardValue, Value.add, Value.mul, Option.some.injEq]
          simp
          ring
        · -- Zero is between the bounds or next to them.
          have hguard : Value.or (Value.lt (some (0 : ℝ)) (some l)) (Value.lt (some u) (some 0)) =
              some false := by
            simp only [not_or, not_lt] at hside
            simp [Value.or, Value.lt, not_lt.2 hside.1, not_lt.2 hside.2]
          rw [hguard]
          show _ = none
          simp only [not_or, not_lt] at hside
          obtain ⟨hl0, hu0⟩ := hside
          by_cases hzero : (if sl = true then l < 0 else l ≤ 0) ∧
              (if su = true then (0 : ℝ) < u else 0 ≤ u)
          · exact interval_observation_missing swap sl su l u hf hzero hv.undefined
          · have hnz : polyZero (p.take N) = false := by
              simp only [ratioCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
              exact hc.1.2
            have hends : (l = 0 ∧ sl = true ∧ 0 < u) ∨ (u = 0 ∧ su = true ∧ l < 0) := by
              cases sl with
              | false =>
                cases su with
                | false =>
                  have hz' : ¬(l ≤ 0 ∧ 0 ≤ u) := hzero
                  exact absurd ⟨hl0, hu0⟩ hz'
                | true =>
                  have hz' : ¬(l ≤ 0 ∧ 0 < u) := hzero
                  have hlt : l < u := hT
                  have hu' : u = 0 := le_antisymm (not_lt.1 fun h => hz' ⟨hl0, h⟩) hu0
                  exact Or.inr ⟨hu', rfl, hu' ▸ hlt⟩
              | true =>
                have hlt : l < u := hT
                cases su with
                | false =>
                  have hz' : ¬(l < 0 ∧ 0 ≤ u) := hzero
                  have hl' : l = 0 := le_antisymm hl0 (not_lt.1 fun h => hz' ⟨h, hu0⟩)
                  exact Or.inl ⟨hl', rfl, hl' ▸ hlt⟩
                | true =>
                  have hz' : ¬(l < 0 ∧ 0 < u) := hzero
                  rcases eq_or_lt_of_le hl0 with hl' | hl'
                  · exact Or.inl ⟨hl', rfl, hl' ▸ hlt⟩
                  · have hu' : u = 0 := le_antisymm (not_lt.1 fun h => hz' ⟨hl', h⟩) hu0
                    exact Or.inr ⟨hu', rfl, hl'⟩
            rcases hends with ⟨rfl, hsl, hpos⟩ | ⟨rfl, hsu, hneg⟩
            · have hg : ∀ x : ℝ, ((if sl = true then (0 : ℝ) < x else 0 ≤ x) ∧
                  (if su = true then x < u else x ≤ u)) →
                  v x = some (polyEval p x * (x⁻¹) ^ N) := fun x hx => by
                have hx0 : 0 < x := by simpa [hsl] using hx.1
                exact hv.equation x hx0.ne'
              refine (interval_observation_value swap sl su 0 u hf hg).2 fun hi => ?_
              have := ratio_not_integrableOn measurableSet_Ioo (Metric.isBounded_Ioo _ _)
                (fun h : (0 : ℝ) ∈ Ioo 0 u => lt_irrefl _ h.1)
                (inv_not_integrableOn_Ioo_right hpos) N p hi
              rw [this] at hnz
              cases hnz
            · have hg : ∀ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
                  (if su = true then x < (0 : ℝ) else x ≤ 0)) →
                  v x = some (polyEval p x * (x⁻¹) ^ N) := fun x hx => by
                have hx0 : x < 0 := by simpa [hsu] using hx.2
                exact hv.equation x hx0.ne
              refine (interval_observation_value swap sl su l 0 hf hg).2 fun hi => ?_
              have := ratio_not_integrableOn measurableSet_Ioo (Metric.isBounded_Ioo _ _)
                (fun h : (0 : ℝ) ∈ Ioo l 0 => lt_irrefl _ h.2)
                (inv_not_integrableOn_Ioo_left hneg) N p hi
              rw [this] at hnz
              cases hnz
      · rw [interval_observation_empty swap sl su l u hf hT, decide_eq_false hT]
        rfl

end QSym.Distribution.StepSource
