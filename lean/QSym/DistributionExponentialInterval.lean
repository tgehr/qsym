import QSym.LimitExponential

/-! Between two bounds and above one bound: a polynomial times the
exponential of a polynomial with rational coefficients, where an
antiderivative has the same shape. `R·exp(E)` is one of `p·exp(E)` exactly
when `R' + E'·R = p`. Above a bound the exponent descends, so that the
antiderivative vanishes at infinity. -/
namespace QSym.Distribution.StepSource
open MeasureTheory Set Filter Topology Asymptotics QSym.Limit

/-- `R·exp(E')` is an antiderivative of `p·exp(E)`: the exponents agree and
`R' + E''·R = p` for the derivative `E''` of `E'`, up to trailing zeros. -/
def curvePrimitive (R p E E' : List ℚ) : Bool :=
  polyZero (polyAdd E (polyScale (-1) E')) &&
    polyZero (polyAdd (polyAdd (polyDerivative R) (polyMul (polyDerivative E') R))
      (polyScale (-1) p))

theorem curve_continuous (p E : List ℚ) :
    Continuous fun x : ℝ => polyEval p x * Real.exp (polyEval E x) :=
  (polyEval_continuous p).mul (Real.continuous_exp.comp (polyEval_continuous E))

private theorem curve_exponent {R p E E' : List ℚ} (h : curvePrimitive R p E E' = true) (x : ℝ) :
    polyEval E x = polyEval E' x := by
  simp only [curvePrimitive, Bool.and_eq_true] at h
  have hz := polyEval_zero h.1 x
  rw [polyEval_add, polyEval_scale] at hz
  push_cast at hz
  linarith

theorem curvePrimitive_deriv {R p E E' : List ℚ} (h : curvePrimitive R p E E' = true) (x : ℝ) :
    HasDerivAt (fun y => polyEval R y * Real.exp (polyEval E' y))
      (polyEval p x * Real.exp (polyEval E x)) x := by
  rw [curve_exponent h x]
  simp only [curvePrimitive, Bool.and_eq_true] at h
  have hz := polyEval_zero h.2 x
  rw [polyEval_add, polyEval_add, polyEval_mul, polyEval_scale] at hz
  have he : polyEval (polyDerivative R) x + polyEval (polyDerivative E') x * polyEval R x =
      polyEval p x := by
    push_cast at hz; linarith
  have hd := (polyEval_hasDerivAt R x).mul ((polyEval_hasDerivAt E' x).exp)
  convert hd using 1
  rw [← he]
  ring

/-- Between two bounds. -/
theorem IntervalTerms.curve {a b m : Option ℝ} {v : ℝ → Option ℝ} {G : Option ℝ → Option ℝ}
    {p R E E' : List ℚ} (hv : EventualExp ⊤ v p E)
    (hG : EventualExp ⊤ (fun t => G (some t)) R E') (hd : curvePrimitive R p E E' = true) :
    IntervalTerms a b m v (Value.add (G b) (Value.mul m (G a))) :=
  .primitive (Filter.eventually_top.1 hv) (Filter.eventually_top.1 hG) (curve_continuous p E)
    (curvePrimitive_deriv hd)

/-- The same under a scale that does not mention the axis. -/
theorem IntervalTerms.scaledCurve {a b m : Option ℝ} {v : ℝ → Option ℝ}
    {G : Option ℝ → Option ℝ} {c : Option ℝ} {p R E E' : List ℚ} (hv : EventualScaled ⊤ v c p E)
    (hG : EventualExp ⊤ (fun t => G (some t)) R E') (hd : curvePrimitive R p E E' = true) :
    IntervalTerms a b m v (Value.mul c (Value.add (G b) (Value.mul m (G a)))) :=
  .scaledPrimitive (Filter.eventually_top.1 hv) (Filter.eventually_top.1 hG)
    (curve_continuous p E) (curvePrimitive_deriv hd)

/-- The checks above a bound: the antiderivative, and an exponent that stays
below a decaying linear rate `r`, their difference descending with degree
`n`. -/
def curveDecay (R p E E' : List ℚ) (r : ℚ) (n : ℕ) : Bool :=
  curvePrimitive R p E E' && (decide (r < 0) && descends true (polyAdd E' [0, -r]) n)

/-- Such an exponent leaves the product integrable above every bound. -/
theorem curve_integrableOn (p : List ℚ) {E : List ℚ} {r : ℚ} {n : ℕ}
    (h : (decide (r < 0) && descends true (polyAdd E [0, -r]) n) = true) (l : ℝ) :
    IntegrableOn (fun x : ℝ => polyEval p x * Real.exp (polyEval E x)) (Ioi l) volume := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hr : ((r : ℚ) : ℝ) < 0 := by exact_mod_cast h.1
  have hle : ∀ᶠ x in atTop, polyEval E x ≤ (r : ℝ) * x := by
    filter_upwards [(descends_atTop h.2).eventually_le_atBot 0] with x hx
    rw [polyEval_add] at hx
    simp only [polyEval, Rat.cast_neg, Rat.cast_zero, mul_zero, add_zero, _root_.zero_add] at hx
    linarith
  have hb : (fun x : ℝ => polyEval p x * Real.exp (polyEval E x)) =O[atTop]
      fun x => polyEval p x * Real.exp ((r : ℝ) * x) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hle] with x hx
    rw [one_mul, norm_mul, norm_mul, Real.norm_eq_abs (Real.exp _), Real.norm_eq_abs (Real.exp _),
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hx) (norm_nonneg _)
  exact integrable_of_isBigO_exp_neg (show (0 : ℝ) < -(r : ℝ) / 2 by linarith)
    (curve_continuous p E).continuousOn (hb.trans (expPolynomial_isBigO p hr))

private theorem curve_halfline {R p E E' : List ℚ} {r : ℚ} {n : ℕ}
    (h : curveDecay R p E E' r n = true) :
    (∀ l, IntegrableOn (fun x : ℝ => polyEval p x * Real.exp (polyEval E x)) (Ioi l) volume) ∧
      (∀ x, HasDerivAt (fun y => polyEval R y * Real.exp (polyEval E' y))
        (polyEval p x * Real.exp (polyEval E x)) x) ∧
      Tendsto (fun y => polyEval R y * Real.exp (polyEval E' y)) atTop (𝓝 0) := by
  simp only [curveDecay, Bool.and_eq_true] at h
  obtain ⟨hp, hr⟩ := h
  have hr' : (decide (r < 0) && descends true (polyAdd E' [0, -r]) n) = true := by
    simp only [Bool.and_eq_true]; exact hr
  have he : (fun x : ℝ => polyEval p x * Real.exp (polyEval E x)) =
      fun x => polyEval p x * Real.exp (polyEval E' x) := by
    funext x; rw [curve_exponent hp x]
  exact ⟨fun l => by rw [he]; exact curve_integrableOn p hr' l, curvePrimitive_deriv hp,
    decays_atTop r n hr'⟩

/-- Above one bound. -/
theorem HalfLineTerms.curve {a m : Option ℝ} {v : ℝ → Option ℝ} {G : Option ℝ → Option ℝ}
    {p R E E' : List ℚ} (r : ℚ) (n : ℕ) (hv : EventualExp ⊤ v p E)
    (hG : EventualExp ⊤ (fun t => G (some t)) R E') (h0 : G none = none)
    (hd : curveDecay R p E E' r n = true) :
    HalfLineTerms a m v (Value.mul m (G a)) :=
  have h := curve_halfline hd
  .primitive (Filter.eventually_top.1 hv) (Filter.eventually_top.1 hG) h0 h.1 h.2.1 h.2.2

/-- The same under a scale that does not mention the axis. -/
theorem HalfLineTerms.scaledCurve {a m : Option ℝ} {v : ℝ → Option ℝ}
    {G : Option ℝ → Option ℝ} {c : Option ℝ} {p R E E' : List ℚ} (r : ℚ) (n : ℕ)
    (hv : EventualScaled ⊤ v c p E) (hG : EventualExp ⊤ (fun t => G (some t)) R E')
    (h0 : G none = none) (hd : curveDecay R p E E' r n = true) :
    HalfLineTerms a m v (Value.mul c (Value.mul m (G a))) :=
  have h := curve_halfline hd
  .scaledPrimitive (Filter.eventually_top.1 hv) (Filter.eventually_top.1 hG) h0 h.1 h.2.1 h.2.2

end QSym.Distribution.StepSource
