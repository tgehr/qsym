import QSym.LimitStep
import QSym.LimitQuotient
import QSym.DistributionInterval

/-! Limits at infinity of polynomials times exponentials of polynomials with
rational coefficients. Where the exponent descends to `-∞` the exponential
dominates every polynomial. A factor may be a piecewise polynomial: only its
polynomial beyond the last cut matters, and where that is zero the product
vanishes whatever the exponential does. -/
namespace QSym.Limit
open Filter Topology Polynomial
open QSym.Distribution.StepSource

private def polyReflect : List ℚ → List ℚ
  | [] => []
  | c :: p => c :: polyScale (-1) (polyReflect p)

private theorem polyEval_reflect (p : List ℚ) (x : ℝ) :
    polyEval (polyReflect p) x = polyEval p (-x) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [polyReflect, polyEval, polyEval_scale, ih]
    push_cast
    ring

theorem expPolynomial_tendsto_atBot (p : List ℚ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => polyEval p x * Real.exp (r * x)) atBot (𝓝 0) := by
  have h := (expPolynomial_tendsto (polyReflect p) (show -r < 0 by linarith)).comp
    tendsto_neg_atBot_atTop
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, polyEval_reflect, neg_neg]
  congr 2
  ring

/-- A polynomial whose coefficient at its degree `b ≥ 1` is negative tends to
`-∞` at `+∞`; at `-∞` the sign of that coefficient counts with the parity
of the degree. -/
def descends (top : Bool) (s : List ℚ) (b : ℕ) : Bool :=
  decide (0 < b) && polyZero (s.drop (b + 1)) &&
    decide ((if top then 1 else (-1) ^ b) * s.getD b 0 < 0)

private theorem leading {s : List ℚ} {b : ℕ} (hs : polyZero (s.drop (b + 1)) = true)
    (hc : s.getD b 0 ≠ 0) :
    (toPoly s).natDegree = b ∧ (toPoly s).leadingCoeff = ((s.getD b 0 : ℚ) : ℝ) := by
  have hne : (toPoly s).coeff b ≠ 0 := by rw [coeff_toPoly]; exact_mod_cast hc
  have hn : (toPoly s).natDegree = b :=
    le_antisymm (natDegree_toPoly_le hs) (le_natDegree_of_ne_zero hne)
  exact ⟨hn, by rw [leadingCoeff, hn, coeff_toPoly]⟩

theorem descends_atTop {s : List ℚ} {b : ℕ} (h : descends true s b = true) :
    Tendsto (polyEval s) atTop atBot := by
  simp only [descends, Bool.and_eq_true, decide_eq_true_eq, if_true, one_mul] at h
  obtain ⟨⟨hb, hs⟩, hc⟩ := h
  obtain ⟨hn, hl⟩ := leading hs hc.ne
  have h0 : toPoly s ≠ 0 := fun h0 => by rw [h0] at hn; simp at hn; omega
  have ht := tendsto_atBot_of_leadingCoeff_nonpos (toPoly s)
    (by rw [degree_eq_natDegree h0, hn]; exact_mod_cast hb)
    (by rw [hl]; exact_mod_cast hc.le)
  exact ht.congr fun x => eval_toPoly s x

theorem descends_atBot {s : List ℚ} {b : ℕ} (h : descends false s b = true) :
    Tendsto (polyEval s) atBot atBot := by
  simp only [descends, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, if_false] at h
  obtain ⟨⟨hb, hs⟩, hc⟩ := h
  have hc0 : s.getD b 0 ≠ 0 := fun h0 => by rw [h0, mul_zero] at hc; exact lt_irrefl _ hc
  obtain ⟨hn, hl⟩ := leading hs hc0
  have h0 : toPoly s ≠ 0 := fun h0 => by rw [h0] at hn; simp at hn; omega
  have hr : ((toPoly s).comp (-X)).natDegree = b := by
    rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one, hn]
  have hr0 : (toPoly s).comp (-X) ≠ 0 := fun h1 => by rw [h1] at hr; simp at hr; omega
  have ht := tendsto_atBot_of_leadingCoeff_nonpos ((toPoly s).comp (-X))
    (by rw [degree_eq_natDegree hr0, hr]; exact_mod_cast hb)
    (by rw [comp_neg_X_leadingCoeff_eq, hn, hl]; exact_mod_cast hc.le)
  refine (ht.comp tendsto_neg_atBot_atTop).congr fun x => ?_
  simp [eval_comp, eval_toPoly]

/-- The polynomial times the exponential of a polynomial vanishes along the
filter. -/
def Vanishes (l : Filter ℝ) (p q : List ℚ) : Prop :=
  Tendsto (fun x => polyEval p x * Real.exp (polyEval q x)) l (𝓝 0)

private theorem vanishes_of_bound {l : Filter ℝ} {p q : List ℚ} (r : ℚ)
    (hs : Tendsto (polyEval (polyAdd q [0, -r])) l atBot)
    (hp : Tendsto (fun x => polyEval p x * Real.exp ((r : ℝ) * x)) l (𝓝 0)) :
    Vanishes l p q := by
  have hle : ∀ᶠ x in l, polyEval q x ≤ (r : ℝ) * x := by
    filter_upwards [hs.eventually_le_atBot 0] with x hx
    rw [polyEval_add] at hx
    simp only [polyEval, Rat.cast_neg, Rat.cast_zero, mul_zero, add_zero, _root_.zero_add] at hx
    linarith
  refine squeeze_zero_norm' ?_ (tendsto_norm_zero.comp hp)
  filter_upwards [hle] with x hx
  simp only [Function.comp_apply, norm_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hx) (abs_nonneg _)

/-- The exponent stays below `r·x` for a rate that decays at `+∞`: their
difference has degree `b` and descends. -/
theorem decays_atTop {p q : List ℚ} (r : ℚ) (b : ℕ)
    (h : (decide (r < 0) && descends true (polyAdd q [0, -r]) b) = true) :
    Vanishes atTop p q := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact vanishes_of_bound r (descends_atTop h.2)
    (expPolynomial_tendsto p (by exact_mod_cast h.1))

theorem decays_atBot {p q : List ℚ} (r : ℚ) (b : ℕ)
    (h : (decide (0 < r) && descends false (polyAdd q [0, -r]) b) = true) :
    Vanishes atBot p q := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact vanishes_of_bound r (descends_atBot h.2)
    (expPolynomial_tendsto_atBot p (by exact_mod_cast h.1))

/-- The zero polynomial vanishes whatever the exponential does. -/
theorem vanishes_zero {l : Filter ℝ} {p q : List ℚ} (hp : polyZero p = true) :
    Vanishes l p q := by
  have h : (fun x => polyEval p x * Real.exp (polyEval q x)) = fun _ => 0 := by
    funext x; rw [polyEval_zero hp, zero_mul]
  unfold Vanishes
  rw [h]
  exact tendsto_const_nhds

/-- Eventually along the filter a polynomial times the exponential of a
polynomial. -/
def EventualExp (l : Filter ℝ) (v : ℝ → Option ℝ) (p q : List ℚ) : Prop :=
  ∀ᶠ x in l, v x = some (polyEval p x * Real.exp (polyEval q x))

theorem EventualExp.polynomial {l : Filter ℝ} {v : ℝ → Option ℝ} {p : List ℚ}
    (h : PolynomialOn (fun _ => True) v p) : EventualExp l v p [] :=
  Eventually.of_forall fun x => by rw [h.equation x trivial]; simp [polyEval]

/-- A piecewise polynomial is a polynomial beyond its last cut. -/
theorem EventualExp.piece {l : Filter ℝ} {reg : Region} {v : ℝ → Option ℝ} {p : List ℚ}
    (ht : Tail l reg) (h : PolynomialOn reg.contains v p) : EventualExp l v p [] :=
  ht.mono fun x hx => by rw [h.equation x hx]; simp [polyEval]

theorem EventualExp.exp {l : Filter ℝ} {f : ℝ → Option ℝ} {q : List ℚ}
    (h : PolynomialOn (fun _ => True) f q) :
    EventualExp l (fun x => Functions.expR.apply (f x)) [1] q :=
  Eventually.of_forall fun x => by
    show Functions.expR.apply (f x) = _
    rw [h.equation x trivial]; simp [Function1.apply, Functions.expR, polyEval]

theorem EventualExp.mul {l : Filter ℝ} {v w : ℝ → Option ℝ} {p q p' q' : List ℚ}
    (hv : EventualExp l v p q) (hw : EventualExp l w p' q') :
    EventualExp l (fun x => Value.mul (v x) (w x)) (polyMul p p') (polyAdd q q') := by
  refine (hv.and hw).mono fun x hx => ?_
  show Value.mul (v x) (w x) = _
  rw [hx.1, hx.2]
  simp only [Value.mul, polyEval_mul, polyEval_add, Real.exp_add, Option.some.injEq]
  ring

/-- The same with a scale that does not mention the variable. -/
def EventualScaled (l : Filter ℝ) (v : ℝ → Option ℝ) (c : Option ℝ) (p q : List ℚ) : Prop :=
  ∀ᶠ x in l, v x = Value.mul c (some (polyEval p x * Real.exp (polyEval q x)))

theorem EventualScaled.constant (l : Filter ℝ) (c : Option ℝ) :
    EventualScaled l (fun _ => c) c [1] [] :=
  Eventually.of_forall fun _ => by cases c <;> simp [Value.mul, polyEval]

theorem EventualScaled.times {l : Filter ℝ} {v w : ℝ → Option ℝ} {c : Option ℝ}
    {p q p' q' : List ℚ} (hv : EventualScaled l v c p q) (hw : EventualExp l w p' q') :
    EventualScaled l (fun x => Value.mul (v x) (w x)) c (polyMul p p') (polyAdd q q') := by
  refine (hv.and hw).mono fun x hx => ?_
  show Value.mul (v x) (w x) = _
  rw [hx.1, hx.2]
  cases c <;> simp only [Value.mul, polyEval_mul, polyEval_add, Real.exp_add, Option.some.injEq]
  ring

theorem EventualScaled.after {l : Filter ℝ} {v w : ℝ → Option ℝ} {c : Option ℝ}
    {p q p' q' : List ℚ} (hw : EventualExp l w p' q') (hv : EventualScaled l v c p q) :
    EventualScaled l (fun x => Value.mul (w x) (v x)) c (polyMul p' p) (polyAdd q' q) := by
  refine (hv.and hw).mono fun x hx => ?_
  show Value.mul (w x) (v x) = _
  rw [hx.1, hx.2]
  cases c <;> simp only [Value.mul, polyEval_mul, polyEval_add, Real.exp_add, Option.some.injEq]
  ring

theorem EventualScaled.mul {l : Filter ℝ} {v w : ℝ → Option ℝ} {c d : Option ℝ}
    {p q p' q' : List ℚ} (hv : EventualScaled l v c p q) (hw : EventualScaled l w d p' q') :
    EventualScaled l (fun x => Value.mul (v x) (w x)) (Value.mul c d) (polyMul p p')
      (polyAdd q q') := by
  refine (hv.and hw).mono fun x hx => ?_
  show Value.mul (v x) (w x) = _
  rw [hx.1, hx.2]
  cases c <;> cases d <;>
    simp only [Value.mul, polyEval_mul, polyEval_add, Real.exp_add, Option.some.injEq]
  ring

private theorem zero_literal {z : Option ℝ}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : z = some 0 := by
  rw [hz]; simp [Numeric.denote]

/-- A polynomial times an exponential that vanishes tends to zero. -/
theorem Exact.decay {l : Filter ℝ} {v : ℝ → Option ℝ} {p q : List ℚ} {z : Option ℝ}
    (hv : EventualExp l v p q) (hd : Vanishes l p q)
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : Exact l v z := by
  rw [zero_literal hz]
  exact ⟨_, hv, hd⟩

/-- Under a scale that does not mention the variable the limit is the scale
times zero: it is zero where the scale is defined and undefined with it. -/
theorem Exact.scaled_decay {l : Filter ℝ} {v : ℝ → Option ℝ} {c : Option ℝ} {p q : List ℚ}
    {z : Option ℝ} (hv : EventualScaled l v c p q) (hd : Vanishes l p q)
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : Exact l v (Value.mul c z) := by
  rw [zero_literal hz]
  cases c with
  | none => exact hv
  | some c =>
    refine ⟨fun x => c * (polyEval p x * Real.exp (polyEval q x)), hv, ?_⟩
    simpa using hd.const_mul c

end QSym.Limit
