import QSym.DistributionGaussianSymbolic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
A polynomial over a power of the axis, between two bounds and beyond one.
Such a quotient is undefined at zero and, where a negative power is left, not
integrable next to it. So it is observed exactly between bounds on one side
of zero, and its antiderivative has a polynomial, a polynomial over a power
of the axis and a logarithm of the absolute value. Beyond one bound on that
side it is observed where it has no power above the inverse square. Then
the same under a factor that does not mention the axis, and around another
point of the axis.
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

/-- The axis is not zero: the domain of a quotient. -/
theorem axis_nonzero (x : ℝ) (hx : x ≠ 0) : Value.nonzero (some x) = some true := by
  simp [Value.nonzero, hx]

/-- Under the guard of its domain a quotient is the same quotient: the guard
holds away from zero, and at zero the quotient is undefined anyway. -/
theorem ratio_guard {v : ℝ → Option ℝ} {p : List ℚ} {N : ℕ} {q : ℝ → Option Bool}
    (hv : RatioOn v p N) (hq : ∀ x : ℝ, x ≠ 0 → q x = some true) :
    RatioOn (fun x => Binding.guardValue (q x) (v x)) p N :=
  ⟨fun x hx => by
    show Binding.guardValue (q x) (v x) = _
    rw [hq x hx, hv.equation x hx]
    rfl, by
    show Binding.guardValue (q 0) (v 0) = none
    rw [hv.undefined]
    simp [Binding.guardValue]⟩

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
`x^N·(x^(M+1)·A' + x·C' - M·C + κ·x^M) = p·x^(M+1)`, which says that the
derivative is the quotient. -/
def ratioCheck (p : List ℚ) (N M : ℕ) (A C : List ℚ) (κ : ℚ) : Bool :=
  decide (0 < N) && decide (0 < M) && !polyZero (p.take N) &&
    polyZero (polyAdd
      (polyMul (polyMonomial 1 N)
        (polyAdd (polyAdd (polyMul (polyMonomial 1 (M + 1)) (polyDerivative A))
          (polyMul [0, 1] (polyDerivative C)))
          (polyAdd (polyScale (-(M : ℚ)) C) (polyMonomial κ M))))
      (polyScale (-1) (polyMul p (polyMonomial 1 (M + 1)))))

theorem ratio_hasDerivAt {p : List ℚ} {N M : ℕ} {A C : List ℚ} {κ : ℚ}
    (h : ratioCheck p N M A C κ = true) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => polyEval A t + polyEval C t * (t ^ M)⁻¹ + κ * Real.log t)
      (polyEval p x * (x⁻¹) ^ N) x := by
  simp only [ratioCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hM⟩, _⟩, hz⟩ := h
  have hid := polyEval_zero hz x
  simp only [polyEval_add, polyEval_mul, polyEval_scale, polyEval_monomial, polyEval] at hid
  push_cast at hid
  have hpow : HasDerivAt (fun t : ℝ => (t ^ M)⁻¹) (-(M * x ^ (M - 1)) / (x ^ M) ^ 2) x :=
    (hasDerivAt_pow M x).inv (pow_ne_zero M hx)
  have hF := ((polyEval_hasDerivAt A x).add ((polyEval_hasDerivAt C x).mul hpow)).add
    ((Real.hasDerivAt_log hx).const_mul (κ : ℝ))
  refine hF.congr_deriv ?_
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hM)
  have hX : x ^ (M' + 1 + 1) * x ^ N ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hx)
  apply mul_right_cancel₀ hX
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
  have hNW : (x⁻¹) ^ N * x ^ N = 1 := by rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  push_cast at hid hdiv ⊢
  linear_combination hid + (polyEval (polyDerivative C) x * x ^ N) * hyx +
    (polyEval C x * x ^ N) * hdiv + ((κ : ℝ) * x ^ N) * hxX -
    (polyEval p x * x ^ (M' + 1 + 1)) * hNW

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

/-! Beyond one bound. A quotient with no power above the inverse square is
integrable out to infinity on one side of zero, and its antiderivative
`C(x)/x^M`, with `C` of degree below `M`, vanishes there. Every other
quotient is not integrable out to infinity. -/

/-- Coefficients that are zero from a degree on can be dropped. -/
theorem polyEval_take {n : ℕ} : ∀ {p : List ℚ}, polyZero (p.drop n) = true → ∀ x : ℝ,
    polyEval p x = polyEval (p.take n) x := by
  induction n with
  | zero =>
    intro p h x
    simpa [polyEval] using polyEval_zero h x
  | succ n ih =>
    intro p h x
    cases p with
    | nil => rfl
    | cons c q =>
      simp only [List.drop_succ_cons] at h
      simp only [List.take_succ_cons, polyEval, ih h x]

private theorem inv_pow_integrableOn_Ioi {l : ℝ} (hl : 0 < l) {K : ℕ} (hK : 2 ≤ K) :
    IntegrableOn (fun x : ℝ => (x⁻¹) ^ K) (Ioi l) volume := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have h := integrableOn_Ioi_rpow_of_lt (a := -(K : ℝ)) (by linarith) hl
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hl.trans hx
  show x ^ (-(K : ℝ)) = (x⁻¹) ^ K
  rw [Real.rpow_neg hx0.le, Real.rpow_natCast, inv_pow]

private theorem inv_pow_integrableOn_Iio {u : ℝ} (hu : u < 0) {K : ℕ} (hK : 2 ≤ K) :
    IntegrableOn (fun x : ℝ => (x⁻¹) ^ K) (Iio u) volume := by
  have h : IntegrableOn (fun x : ℝ => ((-x)⁻¹) ^ K) (Iio u) volume :=
    (inv_pow_integrableOn_Ioi (l := -u) (by linarith) hK).comp_neg_Iio
  have he : (fun x : ℝ => (x⁻¹) ^ K) = fun x => (-1 : ℝ) ^ K * ((-x)⁻¹) ^ K := by
    funext x
    rw [inv_neg, neg_pow x⁻¹ K, ← mul_assoc, ← mul_pow]
    norm_num
  rw [he]
  exact h.const_mul _

/-- On a set away from zero on which every inverse power from the square on
is integrable, so is a polynomial of degree below `K - 1` over the power
`K`. -/
private theorem tail_integrableOn {s : Set ℝ} (hs : MeasurableSet s) (h0 : ∀ x ∈ s, x ≠ 0)
    (hpow : ∀ K : ℕ, 2 ≤ K → IntegrableOn (fun x : ℝ => (x⁻¹) ^ K) s volume) :
    ∀ (q : List ℚ) (K : ℕ), q.length + 1 ≤ K →
      IntegrableOn (fun x : ℝ => polyEval q x * (x⁻¹) ^ K) s volume := by
  intro q
  induction q with
  | nil =>
    intro K _
    simp only [polyEval, zero_mul]
    exact integrableOn_zero
  | cons c q ih =>
    intro K hK
    simp only [List.length_cons] at hK
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hq := ih K' (by omega)
    have hc := (hpow (K' + 1) (by omega)).const_mul (c : ℝ)
    have hsum : IntegrableOn
        (fun x : ℝ => (c : ℝ) * (x⁻¹) ^ (K' + 1) + polyEval q x * (x⁻¹) ^ K') s volume :=
      hc.add hq
    refine hsum.congr_fun (fun x hx => ?_) hs
    have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ (h0 x hx)
    simp only [polyEval, pow_succ]
    linear_combination (-(polyEval q x * (x⁻¹) ^ K')) * h2

/-- A polynomial of degree below `M` over the power `M` vanishes where the
inverse does. -/
private theorem tail_tendsto {l : Filter ℝ} (hinv : Tendsto (fun x : ℝ => x⁻¹) l (𝓝 0))
    (hne : ∀ᶠ x in l, x ≠ 0) :
    ∀ (C : List ℚ) (M : ℕ), C.length ≤ M →
      Tendsto (fun x : ℝ => polyEval C x * (x ^ M)⁻¹) l (𝓝 0) := by
  intro C
  induction C with
  | nil =>
    intro M _
    simp only [polyEval, zero_mul]
    exact tendsto_const_nhds
  | cons c q ih =>
    intro M hM
    simp only [List.length_cons] at hM
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have hq := ih M' (by omega)
    have hc : Tendsto (fun x : ℝ => (c : ℝ) * (x ^ (M' + 1))⁻¹) l (𝓝 0) := by
      simpa using (hinv.pow (M' + 1)).const_mul (c : ℝ)
    have hsum := hc.add hq
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hne] with x hx
    have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
    simp only [polyEval, pow_succ, mul_inv]
    linear_combination (-(polyEval q x * (x ^ M')⁻¹)) * h2

/-- The checks of an antiderivative beyond one bound: there is no polynomial
and no logarithm in it, the quotient has no power above the inverse square,
and `C` is of degree below `M`. -/
def ratioTailCheck (p : List ℚ) (N M : ℕ) (C : List ℚ) : Bool :=
  ratioCheck p N M [0] C 0 && polyZero (p.drop (N - 1)) && decide (C.length ≤ M)

private theorem ratioTail_hasDerivAt {p : List ℚ} {N M : ℕ} {C : List ℚ}
    (h : ratioCheck p N M [0] C 0 = true) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => polyEval C t * (t ^ M)⁻¹) (polyEval p x * (x⁻¹) ^ N) x := by
  have hD := ratio_hasDerivAt h hx
  have he : (fun t : ℝ => polyEval [0] t + polyEval C t * (t ^ M)⁻¹ +
      ((0 : ℚ) : ℝ) * Real.log t) = fun t => polyEval C t * (t ^ M)⁻¹ := by
    funext t
    simp [polyEval]
  rwa [he] at hD

private theorem ratioTail_integrableOn {p : List ℚ} {N M : ℕ} {C : List ℚ}
    (h : ratioCheck p N M [0] C 0 = true) (hdrop : polyZero (p.drop (N - 1)) = true)
    {s : Set ℝ} (hs : MeasurableSet s) (h0 : ∀ x ∈ s, x ≠ 0)
    (hpow : ∀ K : ℕ, 2 ≤ K → IntegrableOn (fun x : ℝ => (x⁻¹) ^ K) s volume) :
    IntegrableOn (fun x : ℝ => polyEval p x * (x⁻¹) ^ N) s volume := by
  simp only [ratioCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have hN : 0 < N := h.1.1.1
  have hi := tail_integrableOn hs h0 hpow (p.take (N - 1)) N (by
    have := List.length_take_le (N - 1) p
    omega)
  have he : (fun x : ℝ => polyEval p x * (x⁻¹) ^ N) =
      fun x => polyEval (p.take (N - 1)) x * (x⁻¹) ^ N := by
    funext x
    rw [polyEval_take hdrop x]
  rw [he]
  exact hi

private theorem ratio_nonzero {p : List ℚ} {N M : ℕ} {A C : List ℚ} {κ : ℚ}
    (h : ratioCheck p N M A C κ = true) : polyZero (p.take N) = false := by
  simp only [ratioCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.2

/-- Above a bound: `guard(0 < a, -C(a)/a^M)`. A bound that is not positive
has zero in the guard, where the quotient is undefined, or next to it, where
it is not integrable. -/
theorem ratio_above (strict : Bool) {a : Option ℝ} {v : ℝ → Option ℝ} {p : List ℚ} {N : ℕ}
    (M : ℕ) (C : List ℚ) (hv : RatioOn v p N) (hc : ratioTailCheck p N M C = true)
    {z m ca : Option ℝ} {msca : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hca : RowTerms none a C 0 [] msca) (hsca : Sums msca ca) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) =
      Binding.guardValue (Value.lt z a)
        (Value.mul m (Value.mul ca (Value.inv (curvaturePower a M)))) := by
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hMinus : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  subst hZ hMinus
  simp only [ratioTailCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hr, hdrop⟩, hlen⟩ := hc
  cases a with
  | none =>
    have hn : partialIntegral volume
        (fun x => Value.mask (compare strict none (some x)) (v x)) = none := by
      apply if_neg
      intro hd
      obtain ⟨r, hr'⟩ := hd.1 0
      cases strict <;> cases hr'
    rw [hn]
    rfl
  | some l =>
    by_cases hl : 0 < l
    · have hne : ∀ x : ℝ, l ≤ x → x ≠ 0 := fun x hx => (hl.trans_le hx).ne'
      have hg : ∀ x : ℝ, (if strict = true then l < x else l ≤ x) →
          v x = some (polyEval p x * (x⁻¹) ^ N) := fun x hx =>
        hv.equation x (hne x (by
          split_ifs at hx
          · exact hx.le
          · exact hx))
      have hint := ratioTail_integrableOn hr hdrop (s := Ioi l) measurableSet_Ioi
        (fun x hx => hne x (le_of_lt hx)) fun K hK => inv_pow_integrableOn_Ioi hl hK
      rw [(above_observation_value strict l hg).1 hint,
        integral_Ioi_of_hasDerivAt_of_tendsto'
          (fun x hx => ratioTail_hasDerivAt hr (hne x hx)) hint
          (tail_tendsto tendsto_inv_atTop_zero (eventually_ne_atTop 0) C M hlen),
        row_sum hca hsca l rfl, curvaturePower_some]
      have hinv : Value.inv (some (l ^ M)) = some ((l ^ M)⁻¹) := by
        simp [Value.inv, pow_ne_zero M hl.ne']
      rw [hinv]
      simp [Binding.guardValue, Value.lt, hl, Value.mul]
    · have hguard : Binding.guardValue (Value.lt (some (0 : ℝ)) (some l))
          (Value.mul (some (-1 : ℝ)) (Value.mul ca (Value.inv (curvaturePower (some l) M)))) =
          none := by
        simp [Binding.guardValue, Value.lt, hl]
      rw [hguard]
      by_cases h0 : (if strict = true then l < 0 else l ≤ 0)
      · apply if_neg
        intro hd
        obtain ⟨r, hr'⟩ := hd.1 0
        have hr'' : Value.mask (compare strict (some l) (some 0)) (v 0) = some r := hr'
        rw [compare_some, decide_eq_true h0, hv.undefined] at hr''
        cases hr''
      · have hstrict : strict = true ∧ l = 0 := by
          cases strict with
          | false => exact absurd (not_lt.1 hl) h0
          | true =>
            have h0' : ¬ l < 0 := h0
            exact ⟨rfl, le_antisymm (not_lt.1 hl) (not_lt.1 h0')⟩
        obtain ⟨rfl, rfl⟩ := hstrict
        have hg : ∀ x : ℝ, (if true = true then (0 : ℝ) < x else 0 ≤ x) →
            v x = some (polyEval p x * (x⁻¹) ^ N) := fun x hx => by
          have hx0 : (0 : ℝ) < x := hx
          exact hv.equation x hx0.ne'
        refine (above_observation_value true 0 hg).2 fun hi => ?_
        have := ratio_not_integrableOn measurableSet_Ioo (Metric.isBounded_Ioo _ _)
          (fun h : (0 : ℝ) ∈ Ioo 0 1 => lt_irrefl _ h.1)
          (inv_not_integrableOn_Ioo_right one_pos) N p (hi.mono_set Ioo_subset_Ioi_self)
        rw [ratio_nonzero hr] at this
        cases this

/-- Below a bound: `guard(b < 0, C(b)/b^M)`. -/
theorem ratio_below (strict : Bool) {b : Option ℝ} {v : ℝ → Option ℝ} {p : List ℚ} {N : ℕ}
    (M : ℕ) (C : List ℚ) (hv : RatioOn v p N) (hc : ratioTailCheck p N M C = true)
    {z cb : Option ℝ} {mscb : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hcb : RowTerms none b C 0 [] mscb) (hscb : Sums mscb cb) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) =
      Binding.guardValue (Value.lt b z) (Value.mul cb (Value.inv (curvaturePower b M))) := by
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  subst hZ
  simp only [ratioTailCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hr, hdrop⟩, hlen⟩ := hc
  cases b with
  | none =>
    have hn : partialIntegral volume
        (fun x => Value.mask (compare strict (some x) none) (v x)) = none := by
      apply if_neg
      intro hd
      obtain ⟨r, hr'⟩ := hd.1 0
      cases strict <;> cases hr'
    rw [hn]
    rfl
  | some u =>
    by_cases hu : u < 0
    · have hne : ∀ x : ℝ, x ≤ u → x ≠ 0 := fun x hx => (lt_of_le_of_lt hx hu).ne
      have hg : ∀ x : ℝ, (if strict = true then x < u else x ≤ u) →
          v x = some (polyEval p x * (x⁻¹) ^ N) := fun x hx =>
        hv.equation x (hne x (by
          split_ifs at hx
          · exact hx.le
          · exact hx))
      have hint := ratioTail_integrableOn hr hdrop (s := Iio u) measurableSet_Iio
        (fun x hx => hne x (le_of_lt hx)) fun K hK => inv_pow_integrableOn_Iio hu hK
      rw [(below_observation_value strict u hg).1 hint, ← integral_Iic_eq_integral_Iio,
        integral_Iic_of_hasDerivAt_of_tendsto'
          (fun x hx => ratioTail_hasDerivAt hr (hne x hx))
          (integrableOn_Iic_iff_integrableOn_Iio.2 hint)
          (tail_tendsto tendsto_inv_atBot_zero (eventually_ne_atBot 0) C M hlen),
        row_sum hcb hscb u rfl, curvaturePower_some]
      have hinv : Value.inv (some (u ^ M)) = some ((u ^ M)⁻¹) := by
        simp [Value.inv, pow_ne_zero M hu.ne]
      rw [hinv]
      simp [Binding.guardValue, Value.lt, hu, Value.mul]
    · have hguard : Binding.guardValue (Value.lt (some u) (some (0 : ℝ)))
          (Value.mul cb (Value.inv (curvaturePower (some u) M))) = none := by
        simp [Binding.guardValue, Value.lt, hu]
      rw [hguard]
      by_cases h0 : (if strict = true then (0 : ℝ) < u else 0 ≤ u)
      · apply if_neg
        intro hd
        obtain ⟨r, hr'⟩ := hd.1 0
        have hr'' : Value.mask (compare strict (some 0) (some u)) (v 0) = some r := hr'
        rw [compare_some, decide_eq_true h0, hv.undefined] at hr''
        cases hr''
      · have hstrict : strict = true ∧ u = 0 := by
          cases strict with
          | false => exact absurd (not_lt.1 hu) h0
          | true =>
            have h0' : ¬ (0 : ℝ) < u := h0
            exact ⟨rfl, le_antisymm (not_lt.1 h0') (not_lt.1 hu)⟩
        obtain ⟨rfl, rfl⟩ := hstrict
        have hg : ∀ x : ℝ, (if true = true then x < (0 : ℝ) else x ≤ 0) →
            v x = some (polyEval p x * (x⁻¹) ^ N) := fun x hx => by
          have hx0 : x < (0 : ℝ) := hx
          exact hv.equation x hx0.ne
        refine (below_observation_value true 0 hg).2 fun hi => ?_
        have := ratio_not_integrableOn measurableSet_Ioo (Metric.isBounded_Ioo _ _)
          (fun h : (0 : ℝ) ∈ Ioo (-1) 0 => lt_irrefl _ h.2)
          (inv_not_integrableOn_Ioo_left (by norm_num : (-1 : ℝ) < 0)) N p
          (hi.mono_set Ioo_subset_Iio_self)
        rw [ratio_nonzero hr] at this
        cases this

/-! A factor that does not mention the axis, anywhere in a product with the
quotient. A partial integral is not linear: under a factor of zero the
product is zero wherever the quotient is defined, also where the quotient is
not integrable, and under a factor that is undefined it is undefined. So
the factor does not simply come out. -/

/-- A polynomial over a power of the axis under an optional factor that does
not depend on it. With `pole` the value is undefined at zero, and the
equation is for the other points. -/
structure Fraction (v : ℝ → Option ℝ) (S : Option (Option ℝ)) (p : List ℚ) (N : ℕ)
    (pole : Bool) : Prop where
  equation : ∀ x : ℝ, (pole = true → x ≠ 0) →
    v x = scaleBy S (some (polyEval p x * (x⁻¹) ^ N))
  undefined : pole = true → v 0 = none

theorem Fraction.polynomial {f : ℝ → Option ℝ} {q : List ℚ}
    (hf : PolynomialOn (fun _ => True) f q) : Fraction f none q 0 false :=
  ⟨fun x _ => by
    rw [hf.equation x trivial]
    simp [scaleBy], fun h => by cases h⟩

theorem Fraction.ratio {f : ℝ → Option ℝ} {p : List ℚ} {N : ℕ} (hf : RatioOn f p N) :
    Fraction f none p N true :=
  ⟨fun x hx => by
    rw [hf.equation x (hx rfl)]
    rfl, fun _ => hf.undefined⟩

/-- A factor that does not depend on the axis. -/
theorem Fraction.scale (c : Option ℝ) : Fraction (fun _ => c) (some c) [1] 0 false :=
  ⟨fun x _ => by cases c <;> simp [scaleBy, Value.mul, polyEval], fun h => by cases h⟩

/-- Products: the factors multiply in their order, and so do the quotients. -/
theorem Fraction.mul {f g : ℝ → Option ℝ} {S T : Option (Option ℝ)} {p q : List ℚ} {n m : ℕ}
    {b b' : Bool} (hf : Fraction f S p n b) (hg : Fraction g T q m b') :
    Fraction (fun x => Value.mul (f x) (g x)) (joinScale S T) (polyMul p q) (n + m)
      (b || b') :=
  ⟨fun x hx => by
    show Value.mul (f x) (g x) = _
    rw [hf.equation x (fun h => hx (by simp [h])), hg.equation x (fun h => hx (by simp [h])),
      polyEval_mul, pow_add]
    rcases S with _ | _ | s <;> rcases T with _ | _ | t <;>
      simp [scaleBy, joinScale, Value.mul] <;> ring, fun h => by
    show Value.mul (f 0) (g 0) = none
    cases b with
    | true =>
      rw [hf.undefined rfl]
      rfl
    | false =>
      rw [hg.undefined (by simpa using h)]
      cases f 0 <;> rfl⟩

/-- Under the guard of its domain it is the same. -/
theorem Fraction.guard {v : ℝ → Option ℝ} {S : Option (Option ℝ)} {p : List ℚ} {N : ℕ}
    {q : ℝ → Option Bool} (hv : Fraction v S p N true)
    (hq : ∀ x : ℝ, x ≠ 0 → q x = some true) :
    Fraction (fun x => Binding.guardValue (q x) (v x)) S p N true :=
  ⟨fun x hx => by
    show Binding.guardValue (q x) (v x) = _
    rw [hq x (hx rfl), hv.equation x hx]
    rfl, fun _ => by
    show Binding.guardValue (q 0) (v 0) = none
    rw [hv.undefined rfl]
    simp [Binding.guardValue]⟩

/-- Under a factor the value is the factor times a quotient, strictly. -/
private theorem Fraction.split {v : ℝ → Option ℝ} {c : Option ℝ} {p : List ℚ} {N : ℕ}
    (hv : Fraction v (some c) p N true) :
    ∃ r : ℝ → Option ℝ, RatioOn r p N ∧ ∀ x, v x = Value.mul c (r x) := by
  classical
  refine ⟨fun x => if x = 0 then none else some (polyEval p x * (x⁻¹) ^ N),
    ⟨fun x hx => by simp [hx], by simp⟩, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    rw [hv.undefined rfl]
    cases c <;> simp [Value.mul]
  · rw [hv.equation x (fun _ => hx)]
    simp [scaleBy, hx]

/-- A real factor that is not zero comes out of a partial integral. -/
theorem partialIntegral_const_mul {γ : ℝ} (hγ : γ ≠ 0) (f : ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mul (some γ) (f x)) =
      Value.mul (some γ) (partialIntegral volume f) := by
  have hget : (fun x => (Value.mul (some γ) (f x)).getD 0) = fun x => γ * (f x).getD 0 := by
    funext x
    cases f x <;> simp [Value.mul]
  have hdef : (∀ x, Value.Defined (Value.mul (some γ) (f x))) ↔ ∀ x, Value.Defined (f x) := by
    constructor
    · intro h x
      obtain ⟨t, ht⟩ := h x
      cases hfx : f x with
      | none =>
        rw [hfx] at ht
        cases ht
      | some s => exact ⟨s, rfl⟩
    · intro h x
      obtain ⟨t, ht⟩ := h x
      exact ⟨γ * t, by rw [ht]; rfl⟩
  by_cases h : (∀ x, Value.Defined (f x)) ∧ Integrable (fun x => (f x).getD 0) volume
  · have hi : Integrable (fun x => (Value.mul (some γ) (f x)).getD 0) volume := by
      rw [hget]
      exact h.2.const_mul γ
    rw [partialIntegral_valid volume f h.1 h.2, partialIntegral_valid volume _ (hdef.2 h.1) hi,
      hget, integral_const_mul]
    rfl
  · have h' : ¬((∀ x, Value.Defined (Value.mul (some γ) (f x))) ∧
        Integrable (fun x => (Value.mul (some γ) (f x)).getD 0) volume) := by
      rintro ⟨h1, h2⟩
      refine h ⟨hdef.1 h1, ?_⟩
      rw [hget] at h2
      refine (h2.const_mul γ⁻¹).congr (Eventually.of_forall fun x => ?_)
      show γ⁻¹ * (γ * (f x).getD 0) = (f x).getD 0
      rw [← mul_assoc, inv_mul_cancel₀ hγ, one_mul]
    rw [show partialIntegral volume f = none from if_neg h,
      show partialIntegral volume (fun x => Value.mul (some γ) (f x)) = none from if_neg h']
    rfl

/-- The observation of a masked value under a factor: under one that is
undefined the value is undefined wherever the mask holds; under zero it is
zero wherever the value is defined; and any other factor comes out. -/
theorem scaled_observation (g : ℝ → Option Bool) (r : ℝ → Option ℝ) (c : Option ℝ) :
    partialIntegral volume (fun x => Value.mask (g x) (Value.mul c (r x))) =
      match c with
      | none => partialIntegral volume (fun x => Value.mask (g x) (none : Option ℝ))
      | some γ => if γ = 0 then
          partialIntegral volume (fun x => Value.mask (g x) ((r x).map fun _ => (0 : ℝ)))
        else Value.mul (some γ) (partialIntegral volume (fun x => Value.mask (g x) (r x))) := by
  cases c with
  | none => rfl
  | some γ =>
    by_cases hγ : γ = 0
    · subst hγ
      have h0 : ∀ x, Value.mul (some (0 : ℝ)) (r x) = (r x).map fun _ => (0 : ℝ) := fun x => by
        cases r x <;> simp [Value.mul]
      simp only [h0, if_true]
    · have hm : ∀ x, Value.mask (g x) (Value.mul (some γ) (r x)) =
          Value.mul (some γ) (Value.mask (g x) (r x)) := fun x => by
        rcases g x with _ | _ | _ <;> simp [Value.mask, Value.mul]
      simp only [hm, if_neg hγ]
      exact partialIntegral_const_mul hγ _

theorem compare_undefined (s : Bool) {a b : Option ℝ} (h : a = none ∨ b = none) :
    compare s a b = none := by
  rcases h with rfl | rfl
  · cases s <;> rfl
  · cases s <;> cases a <;> rfl

/-- With a bound that is undefined the guard between them is undefined
somewhere. -/
private theorem between_bound_undefined (swap sl su : Bool) {a b : Option ℝ}
    (h : a = none ∨ b = none) (w : ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x) (w x)) = none := by
  have missing : ∀ (f : ℝ → Option ℝ) (y : ℝ), f y = none → partialIntegral volume f = none := by
    intro f y hy
    apply if_neg
    intro hd
    obtain ⟨t, ht⟩ := hd.1 y
    rw [hy] at ht
    cases ht
  cases a with
  | none =>
    cases b with
    | none => exact missing _ 0 (by cases swap <;> cases sl <;> cases su <;> rfl)
    | some u =>
      refine missing _ (u - 1) ?_
      cases swap <;> cases sl <;> cases su <;>
        simp [intervalGuard, compare, Value.and, Value.lt, Value.le, Value.mask]
  | some l =>
    cases b with
    | none =>
      refine missing _ (l + 1) ?_
      cases swap <;> cases sl <;> cases su <;>
        simp [intervalGuard, compare, Value.and, Value.lt, Value.le, Value.mask]
    | some u => rcases h with h | h <;> cases h

private theorem side_some (l u : ℝ) :
    Value.or (Value.lt (some (0 : ℝ)) (some l)) (Value.lt (some u) (some (0 : ℝ))) =
      some (decide (0 < l ∨ u < 0)) := by
  by_cases h1 : 0 < l <;> by_cases h2 : u < 0 <;> simp [Value.or, Value.lt, h1, h2]

/-- Zero is not in the guard: it is beyond a bound, or at one that is
strict. -/
private theorem outside_some (sl su : Bool) (l u : ℝ) :
    Value.or (compare (!sl) (some (0 : ℝ)) (some l)) (compare (!su) (some u) (some (0 : ℝ))) =
      some (decide ¬((if sl = true then l < 0 else l ≤ 0) ∧
        (if su = true then (0 : ℝ) < u else 0 ≤ u))) := by
  cases sl <;> cases su <;>
    simp only [compare, Bool.not_true, Bool.not_false, Value.lt, Value.le, Option.bind_eq_bind,
      Option.some_bind, Option.pure_def, if_true, Bool.false_eq_true, if_false]
  · by_cases h1 : 0 < l <;> by_cases h2 : u < 0 <;> simp [Value.or, h1, h2]
  · by_cases h1 : 0 < l <;> by_cases h2 : u ≤ 0 <;> simp [Value.or, h1, h2]
  · by_cases h1 : 0 ≤ l <;> by_cases h2 : u < 0 <;> simp [Value.or, h1, h2]
  · by_cases h1 : 0 ≤ l <;> by_cases h2 : u ≤ 0 <;> simp [Value.or, h1, h2]

/-- Without a value the guard between two bounds leaves the zero function
where it holds nowhere, and nothing otherwise. -/
theorem between_undefined (swap sl su : Bool) (a b : Option ℝ) :
    partialIntegral volume
        (fun x => Value.mask (intervalGuard swap sl su a b x) (none : Option ℝ)) =
      Value.mask (compare (sl || su) a b) none := by
  by_cases h : a = none ∨ b = none
  · rw [between_bound_undefined swap sl su h, compare_undefined _ h]
    rfl
  · obtain ⟨l, rfl⟩ := Option.ne_none_iff_exists'.1 fun ha => h (Or.inl ha)
    obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 fun hb => h (Or.inr hb)
    have hf : Masked
        (fun x => Value.mask (intervalGuard swap sl su (some l) (some u) x) (none : Option ℝ))
        (intervalGuard swap sl su (some l) (some u)) (fun _ => none) := ⟨fun _ => rfl⟩
    rw [compare_some]
    by_cases hT : (if (sl || su) = true then l < u else l ≤ u)
    · rw [interval_observation_undefined swap sl su l u hf (fun _ => rfl) hT, decide_eq_true hT]
      rfl
    · rw [interval_observation_empty swap sl su l u hf hT, decide_eq_false hT]
      rfl

/-- Under a factor of zero a quotient is zero wherever it is defined: it is
observed as zero where zero is not in the guard, and not at all otherwise. -/
private theorem between_zero (swap sl su : Bool) (a b : Option ℝ) {r : ℝ → Option ℝ}
    {p : List ℚ} {N : ℕ} (hr : RatioOn r p N) :
    partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x)
        ((r x).map fun _ => (0 : ℝ))) =
      Value.mask (compare (sl || su) a b) (Binding.guardValue
        (Value.or (compare (!sl) (some 0) a) (compare (!su) b (some 0))) (some 0)) := by
  by_cases h : a = none ∨ b = none
  · rw [between_bound_undefined swap sl su h, compare_undefined _ h]
    rfl
  · obtain ⟨l, rfl⟩ := Option.ne_none_iff_exists'.1 fun ha => h (Or.inl ha)
    obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 fun hb => h (Or.inr hb)
    have hf : Masked (fun x => Value.mask (intervalGuard swap sl su (some l) (some u) x)
        ((r x).map fun _ => (0 : ℝ))) (intervalGuard swap sl su (some l) (some u))
        (fun x => (r x).map fun _ => (0 : ℝ)) := ⟨fun _ => rfl⟩
    rw [outside_some, compare_some]
    by_cases hT : (if (sl || su) = true then l < u else l ≤ u)
    · rw [decide_eq_true hT]
      by_cases hzero : (if sl = true then l < 0 else l ≤ 0) ∧
          (if su = true then (0 : ℝ) < u else 0 ≤ u)
      · rw [interval_observation_missing swap sl su l u hf hzero (by
          show (r 0).map _ = none
          rw [hr.undefined]
          rfl), decide_eq_false (not_not.2 hzero)]
        rfl
      · have hg : ∀ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
            (if su = true then x < u else x ≤ u)) →
            (r x).map (fun _ => (0 : ℝ)) = some ((fun _ : ℝ => (0 : ℝ)) x) := fun x hx => by
          have hx0 : x ≠ 0 := fun h0 => by
            subst h0
            exact hzero hx
          rw [hr.equation x hx0]
          rfl
        rw [(interval_observation_value swap sl su l u hf hg).1 integrableOn_zero,
          decide_eq_true hzero]
        simp [Value.mask, Binding.guardValue]
    · rw [interval_observation_empty swap sl su l u hf hT, decide_eq_false hT]
      rfl

private theorem above_none (strict : Bool) (a : Option ℝ) :
    partialIntegral volume
      (fun x => Value.mask (compare strict a (some x)) (none : Option ℝ)) = none := by
  apply if_neg
  intro hd
  cases a with
  | none =>
    obtain ⟨t, ht⟩ := hd.1 0
    cases strict <;> cases ht
  | some l =>
    obtain ⟨t, ht⟩ := hd.1 (l + 1)
    have ht' : Value.mask (compare strict (some l) (some (l + 1))) (none : Option ℝ) = some t := ht
    have hlt : (if strict = true then l < l + 1 else l ≤ l + 1) := by split_ifs <;> linarith
    rw [compare_some, decide_eq_true hlt] at ht'
    cases ht'

private theorem below_none (strict : Bool) (b : Option ℝ) :
    partialIntegral volume
      (fun x => Value.mask (compare strict (some x) b) (none : Option ℝ)) = none := by
  apply if_neg
  intro hd
  cases b with
  | none =>
    obtain ⟨t, ht⟩ := hd.1 0
    cases strict <;> cases ht
  | some u =>
    obtain ⟨t, ht⟩ := hd.1 (u - 1)
    have ht' : Value.mask (compare strict (some (u - 1)) (some u)) (none : Option ℝ) = some t := ht
    have hlt : (if strict = true then u - 1 < u else u - 1 ≤ u) := by split_ifs <;> linarith
    rw [compare_some, decide_eq_true hlt] at ht'
    cases ht'

/-- Above a bound, under a factor of zero. -/
private theorem above_zero (strict : Bool) (a : Option ℝ) {r : ℝ → Option ℝ} {p : List ℚ}
    {N : ℕ} (hr : RatioOn r p N) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x))
        ((r x).map fun _ => (0 : ℝ))) =
      Binding.guardValue (compare (!strict) (some 0) a) (some 0) := by
  cases a with
  | none =>
    have hn : partialIntegral volume (fun x => Value.mask (compare strict none (some x))
        ((r x).map fun _ => (0 : ℝ))) = none := by
      apply if_neg
      intro hd
      obtain ⟨t, ht⟩ := hd.1 0
      cases strict <;> cases ht
    rw [hn, compare_undefined _ (Or.inr rfl)]
    rfl
  | some l =>
    rw [compare_some]
    by_cases h0 : (if strict = true then l < 0 else l ≤ 0)
    · have hn : partialIntegral volume (fun x => Value.mask (compare strict (some l) (some x))
          ((r x).map fun _ => (0 : ℝ))) = none := by
        apply if_neg
        intro hd
        obtain ⟨t, ht⟩ := hd.1 0
        have ht' : Value.mask (compare strict (some l) (some 0))
            ((r 0).map fun _ => (0 : ℝ)) = some t := ht
        rw [compare_some, decide_eq_true h0, hr.undefined] at ht'
        cases ht'
      have hout : ¬(if (!strict) = true then (0 : ℝ) < l else 0 ≤ l) := by
        cases strict
        · exact not_lt.2 h0
        · exact not_le.2 h0
      rw [hn, decide_eq_false hout]
      rfl
    · have hg : ∀ x : ℝ, (if strict = true then l < x else l ≤ x) →
          (r x).map (fun _ => (0 : ℝ)) = some ((fun _ : ℝ => (0 : ℝ)) x) := fun x hx => by
        have hx0 : x ≠ 0 := fun hx0 => by
          subst hx0
          exact h0 hx
        rw [hr.equation x hx0]
        rfl
      have hout : (if (!strict) = true then (0 : ℝ) < l else 0 ≤ l) := by
        cases strict
        · exact not_le.1 h0
        · exact not_lt.1 h0
      rw [(above_observation_value strict l hg).1 integrableOn_zero, decide_eq_true hout]
      simp [Binding.guardValue]

/-- Below a bound, under a factor of zero. -/
private theorem below_zero (strict : Bool) (b : Option ℝ) {r : ℝ → Option ℝ} {p : List ℚ}
    {N : ℕ} (hr : RatioOn r p N) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b)
        ((r x).map fun _ => (0 : ℝ))) =
      Binding.guardValue (compare (!strict) b (some 0)) (some 0) := by
  cases b with
  | none =>
    have hn : partialIntegral volume (fun x => Value.mask (compare strict (some x) none)
        ((r x).map fun _ => (0 : ℝ))) = none := by
      apply if_neg
      intro hd
      obtain ⟨t, ht⟩ := hd.1 0
      cases strict <;> cases ht
    rw [hn, compare_undefined _ (Or.inl rfl)]
    rfl
  | some u =>
    rw [compare_some]
    by_cases h0 : (if strict = true then (0 : ℝ) < u else 0 ≤ u)
    · have hn : partialIntegral volume (fun x => Value.mask (compare strict (some x) (some u))
          ((r x).map fun _ => (0 : ℝ))) = none := by
        apply if_neg
        intro hd
        obtain ⟨t, ht⟩ := hd.1 0
        have ht' : Value.mask (compare strict (some 0) (some u))
            ((r 0).map fun _ => (0 : ℝ)) = some t := ht
        rw [compare_some, decide_eq_true h0, hr.undefined] at ht'
        cases ht'
      have hout : ¬(if (!strict) = true then u < (0 : ℝ) else u ≤ 0) := by
        cases strict
        · exact not_lt.2 h0
        · exact not_le.2 h0
      rw [hn, decide_eq_false hout]
      rfl
    · have hg : ∀ x : ℝ, (if strict = true then x < u else x ≤ u) →
          (r x).map (fun _ => (0 : ℝ)) = some ((fun _ : ℝ => (0 : ℝ)) x) := fun x hx => by
        have hx0 : x ≠ 0 := fun hx0 => by
          subst hx0
          exact h0 hx
        rw [hr.equation x hx0]
        rfl
      have hout : (if (!strict) = true then u < (0 : ℝ) else u ≤ 0) := by
        cases strict
        · exact not_le.1 h0
        · exact not_lt.1 h0
      rw [(below_observation_value strict u hg).1 integrableOn_zero, decide_eq_true hout]
      simp [Binding.guardValue]

theorem mul_mask_guard (γ : ℝ) (t s : Option Bool) (D : Option ℝ) :
    Value.mul (some γ) (Value.mask t (Binding.guardValue s D)) =
      Value.mask t (Binding.guardValue s (Value.mul (some γ) D)) := by
  rcases t with _ | _ | _ <;> rcases s with _ | _ | _ <;>
    simp [Value.mask, Value.mul, Binding.guardValue]

private theorem mul_guard (γ : ℝ) (s : Option Bool) (D : Option ℝ) :
    Value.mul (some γ) (Binding.guardValue s D) =
      Binding.guardValue s (Value.mul (some γ) D) := by
  rcases s with _ | _ | _ <;> simp [Value.mul, Binding.guardValue]

private theorem or_false (s : Option Bool) : Value.or s (some false) = s := by
  rcases s with _ | _ | _ <;> rfl

private theorem guard_undefined_factor (G : Option Bool) (X : Option ℝ) :
    Binding.guardValue G (Value.mask (Value.nonzero (none : Option ℝ)) X) = none := by
  simp [Value.nonzero, Value.mask, Binding.guardValue]

private theorem nonzero_zero : Value.nonzero (some (0 : ℝ)) = some false := by
  simp [Value.nonzero]

private theorem nonzero_of_ne {γ : ℝ} (hγ : γ ≠ 0) : Value.nonzero (some γ) = some true := by
  simp [Value.nonzero, hγ]

/-- Between two bounds under a factor `c`: under the mask of their comparison
and that of the factor, the factor times the difference of the
antiderivative. The guard is that both bounds are on one side of zero, or
that the factor is zero and zero is not in the guard: then the product is
zero also next to zero. -/
theorem ratio_between_scaled (swap sl su : Bool) {a b c : Option ℝ} {v : ℝ → Option ℝ}
    {p : List ℚ} {N : ℕ} (M : ℕ) (A C : List ℚ) (κ : ℚ) (hv : Fraction v (some c) p N true)
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
        (Value.or (Value.or (Value.lt z a) (Value.lt b z))
          (Value.and (Value.not (Value.nonzero c))
            (Value.or (compare (!sl) z a) (compare (!su) b z))))
        (Value.mask (Value.nonzero c) (Value.mul c
          (Value.add (ratioPrimitive M ab cb k b) (Value.mul m (ratioPrimitive M aa ca k a)))))) := by
  obtain ⟨r, hr, hvr⟩ := hv.split
  have hI := ratio_between swap sl su M A C κ hr hc hz hm hk hab hsab hcb hscb haa hsaa hca hsca
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  subst hZ
  have hfun : (fun x => Value.mask (intervalGuard swap sl su a b x) (v x)) =
      fun x => Value.mask (intervalGuard swap sl su a b x) (Value.mul c (r x)) :=
    funext fun x => by rw [hvr x]
  rw [hfun, scaled_observation]
  cases c with
  | none =>
    show partialIntegral volume
      (fun x => Value.mask (intervalGuard swap sl su a b x) (none : Option ℝ)) = _
    rw [between_undefined, guard_undefined_factor]
  | some γ =>
    by_cases hγ : γ = 0
    · subst hγ
      show (if (0 : ℝ) = 0 then _ else _) = _
      rw [if_pos rfl, between_zero swap sl su a b hr, nonzero_zero]
      by_cases h : a = none ∨ b = none
      · rw [compare_undefined _ h]
        rfl
      · obtain ⟨l, rfl⟩ := Option.ne_none_iff_exists'.1 fun ha => h (Or.inl ha)
        obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 fun hb => h (Or.inr hb)
        show Value.mask _ (Binding.guardValue (Value.or (compare (!sl) (some 0) (some l))
            (compare (!su) (some u) (some 0))) (some 0)) =
          Value.mask _ (Binding.guardValue (Value.or
            (Value.or (Value.lt (some 0) (some l)) (Value.lt (some u) (some 0)))
            (Value.or (compare (!sl) (some 0) (some l)) (compare (!su) (some u) (some 0))))
            (some 0))
        rw [outside_some, side_some]
        have himp : (0 < l ∨ u < 0) → ¬((if sl = true then l < 0 else l ≤ 0) ∧
            (if su = true then (0 : ℝ) < u else 0 ≤ u)) := by
          rintro (h1 | h1) ⟨h2, h3⟩
          · split_ifs at h2 <;> linarith
          · split_ifs at h3 <;> linarith
        by_cases hP : 0 < l ∨ u < 0
        · rw [decide_eq_true hP, decide_eq_true (himp hP)]
          rfl
        · rw [decide_eq_false hP]
          rfl
    · show (if γ = 0 then _ else _) = _
      rw [if_neg hγ, hI, mul_mask_guard, nonzero_of_ne hγ]
      show _ = Value.mask _ (Binding.guardValue
        (Value.or (Value.or (Value.lt (some 0) a) (Value.lt b (some 0))) (some false))
        (Value.mul (some γ) _))
      rw [or_false]

/-- The same without the mask of the factor, where no bound is strict or
both are known to be on one side of zero: then zero is in the guard
wherever they are not. -/
theorem ratio_between_scaled_plain (swap sl su : Bool) {a b c : Option ℝ} {v : ℝ → Option ℝ}
    {p : List ℚ} {N : ℕ} (M : ℕ) (A C : List ℚ) (κ : ℚ) (hv : Fraction v (some c) p N true)
    (hc : ratioCheck p N M A C κ = true) {z m k ab aa cb ca : Option ℝ}
    {msab msaa mscb msca : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) κ))
    (hab : RowTerms none b A 0 [] msab) (hsab : Sums msab ab)
    (hcb : RowTerms none b C 0 [] mscb) (hscb : Sums mscb cb)
    (haa : RowTerms none a A 0 [] msaa) (hsaa : Sums msaa aa)
    (hca : RowTerms none a C 0 [] msca) (hsca : Sums msca ca)
    (hside : (sl || su) = false ∨ Value.or (Value.lt z a) (Value.lt b z) = some true) :
    partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x) (v x)) =
      Value.mask (compare (sl || su) a b) (Binding.guardValue
        (Value.or (Value.lt z a) (Value.lt b z))
        (Value.mul c
          (Value.add (ratioPrimitive M ab cb k b) (Value.mul m (ratioPrimitive M aa ca k a))))) := by
  rw [ratio_between_scaled swap sl su M A C κ hv hc hz hm hk hab hsab hcb hscb haa hsaa hca hsca]
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hMinus : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  subst hZ hMinus
  by_cases h : a = none ∨ b = none
  · rw [compare_undefined _ h]
    rfl
  obtain ⟨l, rfl⟩ := Option.ne_none_iff_exists'.1 fun ha => h (Or.inl ha)
  obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 fun hb => h (Or.inr hb)
  rw [side_some] at hside
  rw [outside_some, side_some, compare_some]
  by_cases hT : (if (sl || su) = true then l < u else l ≤ u)
  swap
  · rw [decide_eq_false hT]
    rfl
  rw [decide_eq_true hT]
  show Binding.guardValue _ _ = Binding.guardValue _ _
  have hlu : l ≤ u := by
    split_ifs at hT
    · exact hT.le
    · exact hT
  cases c with
  | none => simp [Value.nonzero, Value.mask, Value.mul, Binding.guardValue]
  | some γ =>
    by_cases hγ : γ = 0
    · subst hγ
      rw [nonzero_zero]
      by_cases hP : 0 < l ∨ u < 0
      · have hl0 : l ≠ 0 := by
          rcases hP with h1 | h1
          · exact h1.ne'
          · exact (lt_of_le_of_lt hlu h1).ne
        have hu0 : u ≠ 0 := by
          rcases hP with h1 | h1
          · exact (lt_of_lt_of_le h1 hlu).ne'
          · exact h1.ne
        rw [decide_eq_true hP, ratioPrimitive_some hab hsab hcb hscb hk rfl hu0,
          ratioPrimitive_some haa hsaa hca hsca hk rfl hl0]
        simp [Value.or, Value.mask, Value.mul, Value.add, Binding.guardValue]
      · have hQ : ¬¬((if sl = true then l < 0 else l ≤ 0) ∧
            (if su = true then (0 : ℝ) < u else 0 ≤ u)) := by
          rcases hside with hs | hs
          · obtain ⟨rfl, rfl⟩ : sl = false ∧ su = false := by simpa using hs
            simp only [not_or, not_lt] at hP
            exact not_not.2 ⟨hP.1, hP.2⟩
          · rw [decide_eq_false hP] at hs
            cases hs
        rw [decide_eq_false hP, decide_eq_false hQ]
        rfl
    · rw [nonzero_of_ne hγ]
      show Binding.guardValue (Value.or _ (some false)) _ = _
      rw [or_false]
      rfl

/-- Above a bound under a factor `c`: under the mask of the factor, the
factor times the value above. The guard is that the bound is positive, or
that the factor is zero and zero is not in the guard. -/
theorem ratio_above_scaled (strict : Bool) {a c : Option ℝ} {v : ℝ → Option ℝ} {p : List ℚ}
    {N : ℕ} (M : ℕ) (C : List ℚ) (hv : Fraction v (some c) p N true)
    (hc : ratioTailCheck p N M C = true) {z m ca : Option ℝ} {msca : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hca : RowTerms none a C 0 [] msca) (hsca : Sums msca ca) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) =
      Binding.guardValue
        (Value.or (Value.lt z a)
          (Value.and (Value.not (Value.nonzero c)) (compare (!strict) z a)))
        (Value.mask (Value.nonzero c) (Value.mul c
          (Value.mul m (Value.mul ca (Value.inv (curvaturePower a M)))))) := by
  obtain ⟨r, hr, hvr⟩ := hv.split
  have hI := ratio_above strict M C hr hc hz hm hca hsca
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  subst hZ
  have hfun : (fun x => Value.mask (compare strict a (some x)) (v x)) =
      fun x => Value.mask (compare strict a (some x)) (Value.mul c (r x)) :=
    funext fun x => by rw [hvr x]
  rw [hfun, scaled_observation]
  cases c with
  | none =>
    show partialIntegral volume
      (fun x => Value.mask (compare strict a (some x)) (none : Option ℝ)) = _
    rw [above_none, guard_undefined_factor]
  | some γ =>
    by_cases hγ : γ = 0
    · subst hγ
      show (if (0 : ℝ) = 0 then _ else _) = _
      rw [if_pos rfl, above_zero strict a hr, nonzero_zero]
      cases a with
      | none =>
        rw [compare_undefined _ (Or.inr rfl)]
        rfl
      | some l =>
        show Binding.guardValue (compare (!strict) (some 0) (some l)) (some 0) =
          Binding.guardValue (Value.or (Value.lt (some 0) (some l))
            (compare (!strict) (some 0) (some l))) (some 0)
        have hlt : Value.lt (some (0 : ℝ)) (some l) = some (decide (0 < l)) := rfl
        rw [compare_some, hlt]
        by_cases hP : 0 < l
        · have hT : (if (!strict) = true then (0 : ℝ) < l else 0 ≤ l) := by
            split_ifs
            · exact hP
            · exact hP.le
          rw [decide_eq_true hP, decide_eq_true hT]
          rfl
        · rw [decide_eq_false hP]
          rfl
    · show (if γ = 0 then _ else _) = _
      rw [if_neg hγ, hI, mul_guard, nonzero_of_ne hγ]
      show _ = Binding.guardValue (Value.or (Value.lt (some 0) a) (some false))
        (Value.mul (some γ) _)
      rw [or_false]

/-- The same without the mask of the factor, where the bound is not strict
or known to be positive. -/
theorem ratio_above_scaled_plain (strict : Bool) {a c : Option ℝ} {v : ℝ → Option ℝ}
    {p : List ℚ} {N : ℕ} (M : ℕ) (C : List ℚ) (hv : Fraction v (some c) p N true)
    (hc : ratioTailCheck p N M C = true) {z m ca : Option ℝ} {msca : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hca : RowTerms none a C 0 [] msca) (hsca : Sums msca ca)
    (hside : strict = false ∨ Value.lt z a = some true) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) =
      Binding.guardValue (Value.lt z a)
        (Value.mul c (Value.mul m (Value.mul ca (Value.inv (curvaturePower a M))))) := by
  rw [ratio_above_scaled strict M C hv hc hz hm hca hsca]
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hMinus : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  subst hZ hMinus
  cases a with
  | none => rfl
  | some l =>
    have hlt : Value.lt (some (0 : ℝ)) (some l) = some (decide (0 < l)) := rfl
    rw [hlt] at hside
    rw [compare_some, hlt]
    cases c with
    | none => simp [Value.nonzero, Value.mask, Value.mul, Binding.guardValue]
    | some γ =>
      by_cases hγ : γ = 0
      · subst hγ
        rw [nonzero_zero]
        by_cases hP : 0 < l
        · have hinv : Value.inv (some (l ^ M)) = some ((l ^ M)⁻¹) := by
            simp [Value.inv, pow_ne_zero M hP.ne']
          rw [decide_eq_true hP, row_sum hca hsca l rfl, curvaturePower_some, hinv]
          simp [Value.or, Value.mask, Value.mul, Binding.guardValue]
        · have hQ : ¬(if (!strict) = true then (0 : ℝ) < l else 0 ≤ l) := by
            rcases hside with rfl | hs
            · exact hP
            · rw [decide_eq_false hP] at hs
              cases hs
          rw [decide_eq_false hP, decide_eq_false hQ]
          rfl
      · rw [nonzero_of_ne hγ]
        show Binding.guardValue (Value.or _ (some false)) _ = _
        rw [or_false]
        rfl

/-- Below a bound under a factor `c`. -/
theorem ratio_below_scaled (strict : Bool) {b c : Option ℝ} {v : ℝ → Option ℝ} {p : List ℚ}
    {N : ℕ} (M : ℕ) (C : List ℚ) (hv : Fraction v (some c) p N true)
    (hc : ratioTailCheck p N M C = true) {z cb : Option ℝ} {mscb : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hcb : RowTerms none b C 0 [] mscb) (hscb : Sums mscb cb) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) =
      Binding.guardValue
        (Value.or (Value.lt b z)
          (Value.and (Value.not (Value.nonzero c)) (compare (!strict) b z)))
        (Value.mask (Value.nonzero c) (Value.mul c
          (Value.mul cb (Value.inv (curvaturePower b M))))) := by
  obtain ⟨r, hr, hvr⟩ := hv.split
  have hI := ratio_below strict M C hr hc hz hcb hscb
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  subst hZ
  have hfun : (fun x => Value.mask (compare strict (some x) b) (v x)) =
      fun x => Value.mask (compare strict (some x) b) (Value.mul c (r x)) :=
    funext fun x => by rw [hvr x]
  rw [hfun, scaled_observation]
  cases c with
  | none =>
    show partialIntegral volume
      (fun x => Value.mask (compare strict (some x) b) (none : Option ℝ)) = _
    rw [below_none, guard_undefined_factor]
  | some γ =>
    by_cases hγ : γ = 0
    · subst hγ
      show (if (0 : ℝ) = 0 then _ else _) = _
      rw [if_pos rfl, below_zero strict b hr, nonzero_zero]
      cases b with
      | none =>
        rw [compare_undefined _ (Or.inl rfl)]
        rfl
      | some u =>
        show Binding.guardValue (compare (!strict) (some u) (some 0)) (some 0) =
          Binding.guardValue (Value.or (Value.lt (some u) (some 0))
            (compare (!strict) (some u) (some 0))) (some 0)
        have hlt : Value.lt (some u) (some (0 : ℝ)) = some (decide (u < 0)) := rfl
        rw [compare_some, hlt]
        by_cases hP : u < 0
        · have hT : (if (!strict) = true then u < (0 : ℝ) else u ≤ 0) := by
            split_ifs
            · exact hP
            · exact hP.le
          rw [decide_eq_true hP, decide_eq_true hT]
          rfl
        · rw [decide_eq_false hP]
          rfl
    · show (if γ = 0 then _ else _) = _
      rw [if_neg hγ, hI, mul_guard, nonzero_of_ne hγ]
      show _ = Binding.guardValue (Value.or (Value.lt b (some 0)) (some false))
        (Value.mul (some γ) _)
      rw [or_false]

/-- The same without the mask of the factor, where the bound is not strict
or known to be negative. -/
theorem ratio_below_scaled_plain (strict : Bool) {b c : Option ℝ} {v : ℝ → Option ℝ}
    {p : List ℚ} {N : ℕ} (M : ℕ) (C : List ℚ) (hv : Fraction v (some c) p N true)
    (hc : ratioTailCheck p N M C = true) {z cb : Option ℝ} {mscb : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hcb : RowTerms none b C 0 [] mscb) (hscb : Sums mscb cb)
    (hside : strict = false ∨ Value.lt b z = some true) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) =
      Binding.guardValue (Value.lt b z)
        (Value.mul c (Value.mul cb (Value.inv (curvaturePower b M)))) := by
  rw [ratio_below_scaled strict M C hv hc hz hcb hscb]
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  subst hZ
  cases b with
  | none => rfl
  | some u =>
    have hlt : Value.lt (some u) (some (0 : ℝ)) = some (decide (u < 0)) := rfl
    rw [hlt] at hside
    rw [compare_some, hlt]
    cases c with
    | none => simp [Value.nonzero, Value.mask, Value.mul, Binding.guardValue]
    | some γ =>
      by_cases hγ : γ = 0
      · subst hγ
        rw [nonzero_zero]
        by_cases hP : u < 0
        · have hinv : Value.inv (some (u ^ M)) = some ((u ^ M)⁻¹) := by
            simp [Value.inv, pow_ne_zero M hP.ne]
          rw [decide_eq_true hP, row_sum hcb hscb u rfl, curvaturePower_some, hinv]
          simp [Value.or, Value.mask, Value.mul, Binding.guardValue]
        · have hQ : ¬(if (!strict) = true then u < (0 : ℝ) else u ≤ 0) := by
            rcases hside with rfl | hs
            · exact hP
            · rw [decide_eq_false hP] at hs
              cases hs
          rw [decide_eq_false hP, decide_eq_false hQ]
          rfl
      · rw [nonzero_of_ne hγ]
        show Binding.guardValue (Value.or _ (some false)) _ = _
        rw [or_false]
        rfl

/-- The guard of a conjunction is the guard of each, in either order: only
where both hold is the value there. -/
theorem guard_and_left (n q : Option Bool) (y : Option ℝ) :
    Binding.guardValue (Value.and n q) y = Binding.guardValue q (Binding.guardValue n y) := by
  rcases n with _ | _ | _ <;> rcases q with _ | _ | _ <;> rfl

theorem guard_and_right (n q : Option Bool) (y : Option ℝ) :
    Binding.guardValue (Value.and q n) y = Binding.guardValue q (Binding.guardValue n y) := by
  rcases n with _ | _ | _ <;> rcases q with _ | _ | _ <;> rfl

/-- Between two bounds, a value under a strict guard that does not mention
the axis: inside the mask of the bounds the observation is under that guard.
Where the guard fails the value is undefined wherever the mask holds. -/
theorem between_guard_integral (swap sl su : Bool) {a b : Option ℝ} (q : Option Bool)
    {v : ℝ → Option ℝ} {X : Option ℝ}
    (h : partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x) (v x)) =
      Value.mask (compare (sl || su) a b) X) :
    partialIntegral volume
        (fun x => Value.mask (intervalGuard swap sl su a b x) (Binding.guardValue q (v x))) =
      Value.mask (compare (sl || su) a b) (Binding.guardValue q X) := by
  by_cases hq : q = some true
  · subst hq
    exact h
  · have hv : ∀ x, Binding.guardValue q (v x) = none := fun x => by
      simp [Binding.guardValue, hq]
    have hout : Binding.guardValue q X = none := by simp [Binding.guardValue, hq]
    simp only [hv, hout]
    exact between_undefined swap sl su a b

/-! A summand that does not mention the axis. Between two bounds it adds its
multiple by their distance: the bounds are a bounded set, so the sum is
integrable exactly where the value is, and it is defined exactly where both
are. -/

/-- The sum of partial values in either order. -/
theorem value_add_comm (x y : Option ℝ) : Value.add x y = Value.add y x := by
  cases x <;> cases y <;> simp [Value.add, add_comm]

/-- A summand in front comes out of a guard of the other summand. -/
theorem guard_add_first (g : Option Bool) (y κ : Option ℝ) :
    Binding.guardValue g (Value.add κ y) = Value.add (Binding.guardValue g y) κ := by
  rcases g with _ | _ | _ <;> cases κ <;> cases y <;> simp [Binding.guardValue, Value.add, add_comm]

/-- Between two bounds, a value that is another one plus a term `κ` that does
not mention the axis: inside the mask of the bounds, the observation of the
other value plus `κ` times the distance of the bounds. -/
theorem between_add_constant (swap sl su : Bool) {a b m : Option ℝ} {v : ℝ → Option ℝ}
    (w : ℝ → Option ℝ) (κ : Option ℝ) {X : Option ℝ}
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hv : ∀ x, v x = Value.add (w x) κ)
    (h : partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x) (w x)) =
      Value.mask (compare (sl || su) a b) X) :
    partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x) (v x)) =
      Value.mask (compare (sl || su) a b)
        (Value.add X (Value.mul κ (Value.add b (Value.mul m a)))) := by
  have hMinus : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  subst hMinus
  by_cases hab : a = none ∨ b = none
  · rw [between_bound_undefined swap sl su hab, compare_undefined _ hab]
    rfl
  obtain ⟨l, rfl⟩ := Option.ne_none_iff_exists'.1 fun ha => hab (Or.inl ha)
  obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 fun hb => hab (Or.inr hb)
  have hf : Masked (fun x => Value.mask (intervalGuard swap sl su (some l) (some u) x) (w x))
      (intervalGuard swap sl su (some l) (some u)) w := ⟨fun _ => rfl⟩
  have hf' : Masked (fun x => Value.mask (intervalGuard swap sl su (some l) (some u) x) (v x))
      (intervalGuard swap sl su (some l) (some u)) v := ⟨fun _ => rfl⟩
  rw [compare_some] at h ⊢
  by_cases hT : (if (sl || su) = true then l < u else l ≤ u)
  swap
  · rw [interval_observation_empty swap sl su l u hf' hT, decide_eq_false hT]
    rfl
  rw [decide_eq_true hT] at h ⊢
  have hX : partialIntegral volume
      (fun x => Value.mask (intervalGuard swap sl su (some l) (some u) x) (w x)) = X := h
  show _ = Value.add X _
  have hlu : l ≤ u := by
    split_ifs at hT
    · exact hT.le
    · exact hT
  cases κ with
  | none =>
    rw [interval_observation_undefined swap sl su l u hf' (fun x => by
      rw [hv x]
      cases w x <;> rfl) hT]
    cases X <;> rfl
  | some k =>
    by_cases hdef : ∀ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
        (if su = true then x < u else x ≤ u)) → ∃ t, w x = some t
    · have hg : ∀ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
          (if su = true then x < u else x ≤ u)) → w x = some ((fun y => (w y).getD 0) x) :=
        fun x hx => by
          obtain ⟨t, ht⟩ := hdef x hx
          show w x = some ((w x).getD 0)
          rw [ht]
          rfl
      have hg' : ∀ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
          (if su = true then x < u else x ≤ u)) →
          v x = some ((fun y => (w y).getD 0 + k) x) := fun x hx => by
        rw [hv x, hg x hx]
        rfl
      have hconst : IntegrableOn (fun _ : ℝ => k) (Ioo l u) volume :=
        integrableOn_const.2 (Or.inr measure_Ioo_lt_top)
      by_cases hI : IntegrableOn (fun y => (w y).getD 0) (Ioo l u) volume
      · rw [(interval_observation_value swap sl su l u hf hg).1 hI] at hX
        have hvol : volume.real (Ioo l u) = u - l := by
          simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.2 hlu)]
        rw [(interval_observation_value swap sl su l u hf' hg').1 (hI.add hconst), ← hX,
          integral_add hI hconst, setIntegral_const, hvol]
        simp only [Value.add, Value.mul, smul_eq_mul, Option.some.injEq]
        ring
      · rw [(interval_observation_value swap sl su l u hf hg).2 hI] at hX
        have hI' : ¬ IntegrableOn (fun y => (w y).getD 0 + k) (Ioo l u) volume := fun h' =>
          hI (by
            have hd : IntegrableOn (fun y => (w y).getD 0 + k - k) (Ioo l u) volume :=
              h'.sub hconst
            refine hd.congr_fun (fun x _ => ?_) measurableSet_Ioo
            simp)
        rw [(interval_observation_value swap sl su l u hf' hg').2 hI', ← hX]
        rfl
    · simp only [not_forall, not_exists] at hdef
      obtain ⟨x, hx, hnone⟩ := hdef
      have hwx : w x = none := by
        cases hw : w x with
        | none => rfl
        | some t => exact absurd hw (hnone t)
      rw [interval_observation_missing swap sl su l u hf hx hwx] at hX
      rw [interval_observation_missing swap sl su l u hf' hx (by rw [hv x, hwx]; rfl), ← hX]
      rfl

/-! Closed bounds on one side of zero, by a comparison of rationals. -/

theorem side_closed {a b z : Option ℝ} {qa qb : ℚ}
    (ha : a = some (Numeric.denote (s := .real) qa))
    (hb : b = some (Numeric.denote (s := .real) qb))
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (h : decide (0 < qa ∨ qb < 0) = true) :
    Value.or (Value.lt z a) (Value.lt b z) = some true := by
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  subst ha hb hZ
  have hq := of_decide_eq_true h
  have hr : (0 : ℝ) < (qa : ℝ) ∨ ((qb : ℝ)) < 0 := by
    rcases hq with h1 | h1
    · exact Or.inl (by exact_mod_cast h1)
    · exact Or.inr (by exact_mod_cast h1)
  show Value.or (Value.lt (some (0 : ℝ)) (some (qa : ℝ))) (Value.lt (some (qb : ℝ)) (some 0)) = _
  rw [side_some, decide_eq_true hr]

theorem above_closed {a z : Option ℝ} {qa : ℚ} (ha : a = some (Numeric.denote (s := .real) qa))
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) (h : decide (0 < qa) = true) :
    Value.lt z a = some true := by
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  subst ha hZ
  have hr : (0 : ℝ) < (qa : ℝ) := by exact_mod_cast of_decide_eq_true h
  show Value.lt (some (0 : ℝ)) (some (qa : ℝ)) = _
  simp [Value.lt, hr]

theorem below_closed {b z : Option ℝ} {qb : ℚ} (hb : b = some (Numeric.denote (s := .real) qb))
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) (h : decide (qb < 0) = true) :
    Value.lt b z = some true := by
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  subst hb hZ
  have hr : (qb : ℝ) < 0 := by exact_mod_cast of_decide_eq_true h
  show Value.lt (some (qb : ℝ)) (some (0 : ℝ)) = _
  simp [Value.lt, hr]

/-! A quotient around another point of the axis: the inverse of
`c·(x - s)^n`, with polynomials. Moved along the axis by `s` it is a
quotient around zero, between the bounds moved along with it, and the
Lebesgue measure does not notice. -/

/-- A polynomial moved along the axis. -/
theorem polynomial_translate (s : ℚ) {f : ℝ → Option ℝ} {q : List ℚ}
    (hf : PolynomialOn (fun _ => True) f q) :
    PolynomialOn (fun _ => True) (fun y => f (y + s)) (polyTranslate s q) :=
  ⟨fun y _ => by rw [hf.equation (y + s) trivial, polyEval_translate]⟩

/-- A partial integral over the line does not change when the integrand is
moved along it. -/
theorem partialIntegral_translate (s : ℝ) (f : ℝ → Option ℝ) :
    partialIntegral volume (fun y => f (y + s)) = partialIntegral volume f := by
  have hdef : (∀ y, Value.Defined (f (y + s))) ↔ ∀ x, Value.Defined (f x) :=
    ⟨fun h x => by simpa using h (x - s), fun h y => h (y + s)⟩
  have hint : Integrable (fun y => (f (y + s)).getD 0) volume ↔
      Integrable (fun x => (f x).getD 0) volume :=
    ⟨fun h => by simpa using h.comp_add_right (-s), fun h => h.comp_add_right s⟩
  by_cases h : (∀ x, Value.Defined (f x)) ∧ Integrable (fun x => (f x).getD 0) volume
  · rw [partialIntegral_valid volume f h.1 h.2,
      partialIntegral_valid volume _ (hdef.2 h.1) (hint.2 h.2)]
    congr 1
    exact integral_add_right_eq_self (fun x => (f x).getD 0) s
  · rw [show partialIntegral volume f = none from if_neg h,
      show partialIntegral volume (fun y => f (y + s)) = none from
        if_neg fun h' => h ⟨hdef.1 h'.1, hint.1 h'.2⟩]

private theorem compare_shift (t : Bool) (a b : Option ℝ) (σ : ℝ) :
    compare t (Value.add a (some σ)) (Value.add b (some σ)) = compare t a b := by
  cases a <;> cases b <;> cases t <;> simp [compare, Value.add, Value.lt, Value.le]

private theorem compare_shift_lower (t : Bool) (a : Option ℝ) (s y : ℝ) :
    compare t (Value.add a (some (-s))) (some y) = compare t a (some (y + s)) := by
  cases a with
  | none => cases t <;> rfl
  | some l =>
    have h1 : l + -s < y ↔ l < y + s := by constructor <;> intro h <;> linarith
    have h2 : l + -s ≤ y ↔ l ≤ y + s := by constructor <;> intro h <;> linarith
    cases t <;> simp [compare, Value.add, Value.lt, Value.le, h1, h2]

private theorem compare_shift_upper (t : Bool) (b : Option ℝ) (s y : ℝ) :
    compare t (some y) (Value.add b (some (-s))) = compare t (some (y + s)) b := by
  cases b with
  | none => cases t <;> rfl
  | some u =>
    have h1 : y < u + -s ↔ y + s < u := by constructor <;> intro h <;> linarith
    have h2 : y ≤ u + -s ↔ y + s ≤ u := by constructor <;> intro h <;> linarith
    cases t <;> simp [compare, Value.add, Value.lt, Value.le, h1, h2]

private theorem guard_shift (swap sl su : Bool) (a b : Option ℝ) (s y : ℝ) :
    intervalGuard swap sl su (Value.add a (some (-s))) (Value.add b (some (-s))) y =
      intervalGuard swap sl su a b (y + s) := by
  cases swap <;> simp only [intervalGuard, compare_shift_lower, compare_shift_upper]

private theorem denote_neg (s : ℚ) : Numeric.denote (s := .real) (-s) = -(s : ℝ) := by
  simp [Numeric.denote]

/-- A value around a point `s` between two bounds: the value moved to zero
between the bounds moved along with it. -/
theorem shift_between (swap sl su : Bool) {a b σ : Option ℝ} {v : ℝ → Option ℝ} (s : ℚ)
    {X : Option ℝ} (hσ : σ = some (Numeric.denote (s := .real) (-s)))
    (h : partialIntegral volume (fun y => Value.mask
        (intervalGuard swap sl su (Value.add a σ) (Value.add b σ) y) (v (y + s))) =
      Value.mask (compare (sl || su) (Value.add a σ) (Value.add b σ)) X) :
    partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x) (v x)) =
      Value.mask (compare (sl || su) a b) X := by
  rw [hσ, denote_neg] at h
  rw [← partialIntegral_translate (s : ℝ), ← compare_shift (sl || su) a b (-(s : ℝ)), ← h]
  simp only [guard_shift]

/-- Above one bound, and below one. -/
theorem shift_above (strict : Bool) {a σ : Option ℝ} {v : ℝ → Option ℝ} (s : ℚ) {X : Option ℝ}
    (hσ : σ = some (Numeric.denote (s := .real) (-s)))
    (h : partialIntegral volume
        (fun y => Value.mask (compare strict (Value.add a σ) (some y)) (v (y + s))) = X) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) = X := by
  rw [hσ, denote_neg] at h
  rw [← partialIntegral_translate (s : ℝ), ← h]
  simp only [compare_shift_lower]

theorem shift_below (strict : Bool) {b σ : Option ℝ} {v : ℝ → Option ℝ} (s : ℚ) {X : Option ℝ}
    (hσ : σ = some (Numeric.denote (s := .real) (-s)))
    (h : partialIntegral volume
        (fun y => Value.mask (compare strict (some y) (Value.add b σ)) (v (y + s))) = X) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) = X := by
  rw [hσ, denote_neg] at h
  rw [← partialIntegral_translate (s : ℝ), ← h]
  simp only [compare_shift_upper]

/-- The domain of a quotient around `s`, moved to zero. -/
theorem shifted_nonzero (s : ℚ) {c : Option ℝ}
    (hc : c = some (Numeric.denote (s := .real) (-s))) (y : ℝ) (hy : y ≠ 0) :
    Value.nonzero (Value.add (some (y + s)) c) = some true := by
  rw [hc, denote_neg]
  simp [Value.nonzero, Value.add, hy]

end QSym.Distribution.StepSource
