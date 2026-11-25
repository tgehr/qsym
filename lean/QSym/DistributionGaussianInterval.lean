import QSym.DistributionGaussian
import QSym.DistributionExponentialInterval

/-! A half-line that starts or ends at the vertex of a Gaussian. The
exponential of the quadratic has half its integral on either side of its
vertex, and the polynomial is a constant up to a derivative that vanishes at
infinity: the rest of the integral is the value of that antiderivative at the
vertex. -/
namespace QSym.Distribution.StepSource
open MeasureTheory Set Filter Topology QSym.Limit

/-- Above its vertex the exponential of a quadratic with negative curvature
has half its integral. -/
theorem gaussian_integral_Ioi {c0 c1 c2 v : ℝ} (h : c2 < 0) (hv : v * (2 * c2) = -c1) :
    ∫ x in Ioi v, Real.exp (c0 + c1 * x + c2 * x ^ 2) =
      Real.exp (c0 - c1 ^ 2 / (4 * c2)) * √(Real.pi / (-c2)) / 2 := by
  have hc : c2 ≠ 0 := h.ne
  have he : (Ioi v).indicator (fun x : ℝ => Real.exp (c0 + c1 * x + c2 * x ^ 2)) = fun x =>
      Real.exp (c0 - c1 ^ 2 / (4 * c2)) *
        (Ioi (0 : ℝ)).indicator (fun y : ℝ => Real.exp (- -c2 * y ^ 2)) (x - v) := by
    funext x
    by_cases hx : x ∈ Ioi v
    · have h0 : x - v ∈ Ioi (0 : ℝ) := Set.mem_Ioi.2 (sub_pos.2 (Set.mem_Ioi.1 hx))
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem h0, ← Real.exp_add]
      congr 1
      have h1 : c1 = -(v * (2 * c2)) := by linarith
      rw [h1]
      field_simp
      ring
    · have h0 : x - v ∉ Ioi (0 : ℝ) := fun h0 => hx (Set.mem_Ioi.2 (sub_pos.1 (Set.mem_Ioi.1 h0)))
      rw [Set.indicator_of_not_mem hx, Set.indicator_of_not_mem h0, mul_zero]
  rw [← integral_indicator measurableSet_Ioi, he, integral_const_mul,
    integral_sub_right_eq_self
      (fun y : ℝ => (Ioi (0 : ℝ)).indicator (fun y : ℝ => Real.exp (- -c2 * y ^ 2)) y) v,
    integral_indicator measurableSet_Ioi, integral_gaussian_Ioi]
  ring

/-- Below its vertex it has the other half. -/
theorem gaussian_integral_Iic {c0 c1 c2 v : ℝ} (h : c2 < 0) (hv : v * (2 * c2) = -c1) :
    ∫ x in Iic v, Real.exp (c0 + c1 * x + c2 * x ^ 2) =
      Real.exp (c0 - c1 ^ 2 / (4 * c2)) * √(Real.pi / (-c2)) / 2 := by
  have hs := integral_add_compl (measurableSet_Ioi (a := v)) (gaussian_integrable c0 c1 c2 h)
  rw [compl_Ioi, gaussian_integral_Ioi h hv, gaussian_integral c0 c1 c2 h] at hs
  linarith

private theorem quadratic_function {Q : List ℚ} {c0 c1 c2 : ℚ} (hq : quadratic Q c0 c1 c2 = true)
    (R : List ℚ) : (fun x : ℝ => polyEval R x * Real.exp (polyEval Q x)) =
      fun x => polyEval R x * Real.exp (polyEval [c0, c1, c2] x) := by
  funext x
  rw [quadratic_eval hq x]
  congr 2
  simp [polyEval]
  ring

private theorem quadratic_negative {Q : List ℚ} {c0 c1 c2 : ℚ} (hq : quadratic Q c0 c1 c2 = true) :
    c2 < 0 := by
  simp only [quadratic, Bool.and_eq_true, decide_eq_true_eq] at hq
  exact hq.1

private theorem quadratic_vanishes_atTop {Q : List ℚ} {c0 c1 c2 : ℚ}
    (hq : quadratic Q c0 c1 c2 = true) (R : List ℚ) :
    Tendsto (fun x : ℝ => polyEval R x * Real.exp (polyEval Q x)) atTop (𝓝 0) := by
  rw [quadratic_function hq R]
  exact decays_atTop (-1) 2 (by simp [descends, polyAdd, polyZero, quadratic_negative hq])

private theorem quadratic_vanishes_atBot {Q : List ℚ} {c0 c1 c2 : ℚ}
    (hq : quadratic Q c0 c1 c2 = true) (R : List ℚ) :
    Tendsto (fun x : ℝ => polyEval R x * Real.exp (polyEval Q x)) atBot (𝓝 0) := by
  rw [quadratic_function hq R]
  exact decays_atBot 1 2 (by simp [descends, polyAdd, polyZero, quadratic_negative hq])

/-- The integrals of a polynomial times the exponential of a quadratic above
and below the vertex `w` of the quadratic. -/
private theorem vertex_integrals {R P Q : List ℚ} {κ c0 c1 c2 γ δ w : ℚ}
    (h : gaussianCheck R P Q κ c0 c1 c2 γ δ = true) (hw : w * (2 * c2) = -c1) :
    Integrable (fun x : ℝ => polyEval P x * Real.exp (polyEval Q x)) ∧
      (∫ x in Ioi (w : ℝ), polyEval P x * Real.exp (polyEval Q x)) =
        κ / 2 * (Real.exp γ * √(Real.pi * δ)) - polyEval R w * Real.exp γ ∧
      (∫ x in Iic (w : ℝ), polyEval P x * Real.exp (polyEval Q x)) =
        κ / 2 * (Real.exp γ * √(Real.pi * δ)) + polyEval R w * Real.exp γ := by
  simp only [gaussianCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hq, hp⟩, hγ⟩, hδ⟩ := h
  have hc2 := quadratic_negative hq
  have hcR : ((c2 : ℚ) : ℝ) < 0 := by exact_mod_cast hc2
  have hc : ((c2 : ℚ) : ℝ) ≠ 0 := hcR.ne
  have hγR : (γ : ℝ) * (4 * c2) = 4 * c0 * c2 - c1 ^ 2 := by exact_mod_cast hγ
  have hδR : (δ : ℝ) * c2 = -1 := by exact_mod_cast hδ
  have hwR : (w : ℝ) * (2 * c2) = -c1 := by exact_mod_cast hw
  have hQ : ∀ x : ℝ, polyEval Q x = c0 + c1 * x + c2 * x ^ 2 := quadratic_eval hq
  have hE : (fun x : ℝ => Real.exp (polyEval Q x)) =
      fun x => Real.exp (c0 + c1 * x + c2 * x ^ 2) := by funext x; rw [hQ]
  have hPi := (gaussian_polynomial_integral hq hp).1
  have hEi : Integrable fun x : ℝ => Real.exp (polyEval Q x) := by
    rw [hE]; exact gaussian_integrable _ _ _ hcR
  have hDi : Integrable fun x : ℝ => (polyEval P x - κ) * Real.exp (polyEval Q x) := by
    have h := hPi.sub (hEi.const_mul (κ : ℝ))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hsplit : (fun x : ℝ => polyEval P x * Real.exp (polyEval Q x)) = fun x =>
      (polyEval P x - κ) * Real.exp (polyEval Q x) + κ * Real.exp (polyEval Q x) := by
    funext x; ring
  have hγ' : (c0 : ℝ) - c1 ^ 2 / (4 * c2) = γ := by
    field_simp
    linarith
  have hδ' : Real.pi / (-(c2 : ℝ)) = Real.pi * δ := by
    have : (δ : ℝ) = 1 / (-c2) := by
      rw [eq_div_iff (neg_ne_zero.2 hc)]
      linarith
    rw [this]; ring
  have hvertex : polyEval Q w = γ := by
    rw [hQ]
    apply mul_right_cancel₀ (show (4 * (c2 : ℝ)) ≠ 0 from mul_ne_zero four_ne_zero hc)
    rw [hγR]
    have h1 : (c1 : ℝ) = -(w * (2 * c2)) := by linarith
    rw [h1]
    ring
  have hup := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (w : ℝ))
    (fun x _ => gaussPrimitive_deriv hp x) hDi.integrableOn (quadratic_vanishes_atTop hq R)
  have hdown := integral_Iic_of_hasDerivAt_of_tendsto' (a := (w : ℝ))
    (fun x _ => gaussPrimitive_deriv hp x) hDi.integrableOn (quadratic_vanishes_atBot hq R)
  refine ⟨hPi, ?_, ?_⟩
  · rw [hsplit, integral_add hDi.integrableOn (hEi.const_mul _).integrableOn, hup,
      integral_const_mul, hE, gaussian_integral_Ioi hcR hwR, hvertex, hγ', hδ']
    ring
  · rw [hsplit, integral_add hDi.integrableOn (hEi.const_mul _).integrableOn, hdown,
      integral_const_mul, hE, gaussian_integral_Iic hcR hwR, hvertex, hγ', hδ']
    ring

/-- The checks of a half-line at the vertex of a Gaussian: those of the
Gaussian integral, the vertex `w`, half the constant, and the value of the
antiderivative at the vertex with the sign of its end. -/
def vertexCheck (upper : Bool) (R P Q : List ℚ) (κ c0 c1 c2 γ δ w half rest : ℚ) : Bool :=
  gaussianCheck R P Q κ c0 c1 c2 γ δ && decide (w * (2 * c2) = -c1) && decide (half * 2 = κ) &&
    decide (rest = (if upper then 1 else -1) * polyEvalQ R w)

/-- The integral on the side of the vertex that the half-line names. -/
noncomputable def vertexIntegral (upper : Bool) (P Q : List ℚ) (w : ℚ) : ℝ :=
  if upper then ∫ x in Iic (w : ℝ), polyEval P x * Real.exp (polyEval Q x)
  else ∫ x in Ioi (w : ℝ), polyEval P x * Real.exp (polyEval Q x)

private theorem vertex_value {upper : Bool} {R P Q : List ℚ} {κ c0 c1 c2 γ δ w half rest : ℚ}
    (h : vertexCheck upper R P Q κ c0 c1 c2 γ δ w half rest = true) {k1 k2 g d pi : Option ℝ}
    (hk1 : k1 = some (Numeric.denote (s := .real) half))
    (hk2 : k2 = some (Numeric.denote (s := .real) rest))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    Integrable (fun x : ℝ => polyEval P x * Real.exp (polyEval Q x)) ∧
      Value.add
          (Value.mul k1 (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))))
          (Value.mul k2 (Functions.expR.apply g)) =
        some (vertexIntegral upper P Q w) := by
  simp only [vertexCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, hw⟩, hh⟩, hr⟩ := h
  obtain ⟨hi, hup, hdown⟩ := vertex_integrals hc hw
  refine ⟨hi, ?_⟩
  simp only [gaussianCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hq, _⟩, _⟩, hδ⟩ := hc
  have hcR : ((c2 : ℚ) : ℝ) < 0 := by exact_mod_cast quadratic_negative hq
  have hδR : (δ : ℝ) * c2 = -1 := by exact_mod_cast hδ
  have hpos : 0 ≤ Real.pi * (δ : ℝ) := by
    have : (0 : ℝ) < δ := by nlinarith
    exact mul_nonneg Real.pi_pos.le this.le
  have hhalf : (half : ℝ) = κ / 2 := by
    have : (half : ℝ) * 2 = κ := by exact_mod_cast hh
    linarith
  have hrest : (rest : ℝ) = (if upper then 1 else -1) * polyEval R w := by
    rw [← polyEvalQ_cast R w, hr]
    cases upper <;> simp
  rw [hk1, hk2, hg, hd, hpi]
  cases upper
  · simp only [vertexIntegral, Bool.false_eq_true, if_false] at hrest ⊢
    rw [hup]
    simp [Value.mul, Value.add, Function1.apply, Functions.expR, Functions.sqrtR, Functions.pi,
      Numeric.denote, hpos, hhalf, hrest]
    ring
  · simp only [vertexIntegral, if_true] at hrest ⊢
    rw [hdown]
    simp [Value.mul, Value.add, Function1.apply, Functions.expR, Functions.sqrtR, Functions.pi,
      Numeric.denote, hpos, hhalf, hrest]

private theorem denote_injective {w : ℚ} {l : ℝ}
    (h : some (Numeric.denote (s := .real) w) = some l) : (w : ℝ) = l := by
  simpa [Numeric.denote] using h

/-- Above the vertex of a Gaussian. -/
theorem HalfLineTerms.gaussian {a m : Option ℝ} {v : ℝ → Option ℝ} {R P Q : List ℚ}
    (κ c0 c1 c2 γ δ w half rest : ℚ) (hv : EventualExp ⊤ v P Q)
    (ha : a = some (Numeric.denote (s := .real) w))
    (h : vertexCheck false R P Q κ c0 c1 c2 γ δ w half rest = true) {k1 k2 g d pi : Option ℝ}
    (hk1 : k1 = some (Numeric.denote (s := .real) half))
    (hk2 : k2 = some (Numeric.denote (s := .real) rest))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    HalfLineTerms a m v (Value.add
      (Value.mul k1 (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))))
      (Value.mul k2 (Functions.expR.apply g))) := by
  obtain ⟨hi, ho⟩ := vertex_value h hk1 hk2 hg hd hpi
  refine .value (Filter.eventually_top.1 hv) (fun l => hi.integrableOn) (fun hn => ?_)
    (fun l hl => ?_)
  · rw [ha] at hn; cases hn
  · rw [ha] at hl
    rw [ho, ← denote_injective hl]
    rfl

/-- The same under a scale that does not mention the axis. -/
theorem HalfLineTerms.scaledGaussian {a m : Option ℝ} {v : ℝ → Option ℝ} {c : Option ℝ}
    {R P Q : List ℚ} (κ c0 c1 c2 γ δ w half rest : ℚ) (hv : EventualScaled ⊤ v c P Q)
    (ha : a = some (Numeric.denote (s := .real) w))
    (h : vertexCheck false R P Q κ c0 c1 c2 γ δ w half rest = true) {k1 k2 g d pi : Option ℝ}
    (hk1 : k1 = some (Numeric.denote (s := .real) half))
    (hk2 : k2 = some (Numeric.denote (s := .real) rest))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    HalfLineTerms a m v (Value.mul c (Value.add
      (Value.mul k1 (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))))
      (Value.mul k2 (Functions.expR.apply g)))) := by
  obtain ⟨hi, ho⟩ := vertex_value h hk1 hk2 hg hd hpi
  refine .scaledValue (Filter.eventually_top.1 hv) (fun l => hi.integrableOn) (fun hn => ?_)
    (fun l hl => ?_)
  · rw [ha] at hn; cases hn
  · rw [ha] at hl
    rw [ho, ← denote_injective hl]
    rfl

/-- Below the vertex of a Gaussian. -/
theorem UpperTerms.gaussian {b : Option ℝ} {v : ℝ → Option ℝ} {R P Q : List ℚ}
    (κ c0 c1 c2 γ δ w half rest : ℚ) (hv : EventualExp ⊤ v P Q)
    (hb : b = some (Numeric.denote (s := .real) w))
    (h : vertexCheck true R P Q κ c0 c1 c2 γ δ w half rest = true) {k1 k2 g d pi : Option ℝ}
    (hk1 : k1 = some (Numeric.denote (s := .real) half))
    (hk2 : k2 = some (Numeric.denote (s := .real) rest))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    UpperTerms b v (Value.add
      (Value.mul k1 (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))))
      (Value.mul k2 (Functions.expR.apply g))) := by
  obtain ⟨hi, ho⟩ := vertex_value h hk1 hk2 hg hd hpi
  refine .value (Filter.eventually_top.1 hv) (fun u => hi.integrableOn) (fun hn => ?_)
    (fun u hu => ?_)
  · rw [hb] at hn; cases hn
  · rw [hb] at hu
    rw [ho, ← denote_injective hu]
    rfl

/-- The same under a scale that does not mention the axis. -/
theorem UpperTerms.scaledGaussian {b : Option ℝ} {v : ℝ → Option ℝ} {c : Option ℝ}
    {R P Q : List ℚ} (κ c0 c1 c2 γ δ w half rest : ℚ) (hv : EventualScaled ⊤ v c P Q)
    (hb : b = some (Numeric.denote (s := .real) w))
    (h : vertexCheck true R P Q κ c0 c1 c2 γ δ w half rest = true) {k1 k2 g d pi : Option ℝ}
    (hk1 : k1 = some (Numeric.denote (s := .real) half))
    (hk2 : k2 = some (Numeric.denote (s := .real) rest))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    UpperTerms b v (Value.mul c (Value.add
      (Value.mul k1 (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))))
      (Value.mul k2 (Functions.expR.apply g)))) := by
  obtain ⟨hi, ho⟩ := vertex_value h hk1 hk2 hg hd hpi
  refine .scaledValue (Filter.eventually_top.1 hv) (fun u => hi.integrableOn) (fun hn => ?_)
    (fun u hu => ?_)
  · rw [hb] at hn; cases hn
  · rw [hb] at hu
    rw [ho, ← denote_injective hu]
    rfl

/-! Other bounds. A polynomial times the exponential of a quadratic with
negative curvature has an antiderivative with the error function: the
polynomial is a constant `κ` up to a derivative, and the exponential of the
quadratic is `exp(γ)` times a Gaussian in `√σ·(x - w)`, around its vertex `w`
with `σ` the negated curvature. Between two bounds the antiderivative has the
error function itself. Beyond a single bound it has the complement, which
vanishes at infinity: above a bound negated, below one with the argument
reflected. -/

/-- The derivative of the error function. -/
theorem erf_hasDerivAt (x : ℝ) :
    HasDerivAt Functions.erfR.value (2 / √Real.pi * Real.exp (-x ^ 2)) x := by
  have hc : Continuous fun t : ℝ => Real.exp (-t ^ 2) := by fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_mul (2 / √Real.pi)

theorem erfc_hasDerivAt (x : ℝ) :
    HasDerivAt Functions.erfcR.value (-(2 / √Real.pi * Real.exp (-x ^ 2))) x :=
  (erf_hasDerivAt x).const_sub 1

/-- The complement of the error function vanishes at infinity. -/
theorem erfc_tendsto_atTop : Tendsto Functions.erfcR.value atTop (𝓝 0) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi 0) volume := by
    have h := (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn (s := Ioi (0 : ℝ))
    simpa using h
  have h := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi tendsto_id
  have hv : ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2) = √Real.pi / 2 := by
    have h1 := integral_gaussian_Ioi 1
    simpa using h1
  rw [hv] at h
  have h2 := (h.const_mul (2 / √Real.pi)).const_sub 1
  have hpi : 2 / √Real.pi * (√Real.pi / 2) = 1 := by
    have hne : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    field_simp
  rw [hpi, sub_self] at h2
  exact h2

theorem erf_apply (y : ℝ) : Functions.erfR.apply (some y) = some (Functions.erfR.value y) := by
  simp [Function1.apply, Functions.erfR]

theorem erfc_apply (y : ℝ) : Functions.erfcR.apply (some y) = some (Functions.erfcR.value y) := by
  simp [Function1.apply, Functions.erfcR]

/-- The checks of the antiderivative with the error function: those of the
Gaussian integral, the vertex `w`, half the constant, the negated curvature
`σ`, and the offset of the argument, `w` where it is reflected and `-w`
otherwise. -/
def erfCheck (reflected : Bool) (R P Q : List ℚ) (κ c0 c1 c2 γ δ w half σ offset : ℚ) : Bool :=
  gaussianCheck R P Q κ c0 c1 c2 γ δ && decide (w * (2 * c2) = -c1) && decide (half * 2 = κ) &&
    decide (σ = -c2) && decide (offset = (if reflected then w else -w))

/-- What the checks say of the real functions: the exponential of the
quadratic around its vertex, the constant in front of the error function,
and the antiderivative of the rest. -/
private theorem erf_facts {reflected : Bool} {R P Q : List ℚ}
    {κ c0 c1 c2 γ δ w half σ offset : ℚ}
    (h : erfCheck reflected R P Q κ c0 c1 c2 γ δ w half σ offset = true) :
    (0 : ℝ) < σ ∧ 0 ≤ Real.pi * (δ : ℝ) ∧
      (∀ t : ℝ, Real.exp γ * Real.exp (-(√(σ : ℝ) * (t - w)) ^ 2) = Real.exp (polyEval Q t)) ∧
      (half : ℝ) * √(Real.pi * δ) * (2 / √Real.pi * √(σ : ℝ)) = κ ∧
      quadratic Q c0 c1 c2 = true ∧ gaussPrimitive R P Q κ = true ∧
      (offset : ℝ) = (if reflected then (w : ℝ) else -w) := by
  simp only [erfCheck, gaussianCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hq, hp⟩, hγ⟩, hδ⟩, hw⟩, hh⟩, hσ⟩, ho⟩ := h
  have hc2 := quadratic_negative hq
  have hcR : ((c2 : ℚ) : ℝ) < 0 := by exact_mod_cast hc2
  have hc : ((c2 : ℚ) : ℝ) ≠ 0 := hcR.ne
  have hγR : (γ : ℝ) * (4 * c2) = 4 * c0 * c2 - c1 ^ 2 := by exact_mod_cast hγ
  have hδR : (δ : ℝ) * c2 = -1 := by exact_mod_cast hδ
  have hwR : (w : ℝ) * (2 * c2) = -c1 := by exact_mod_cast hw
  have hhR : (half : ℝ) * 2 = κ := by exact_mod_cast hh
  have hσR : (σ : ℝ) = -c2 := by exact_mod_cast hσ
  have hσpos : (0 : ℝ) < σ := by rw [hσR]; linarith
  have hδpos : (0 : ℝ) < δ := by nlinarith
  have hc1 : (c1 : ℝ) = -(w * (2 * c2)) := by linarith
  have hγ' : (γ : ℝ) = c0 - c2 * w ^ 2 := by
    apply mul_right_cancel₀ (show (4 * (c2 : ℝ)) ≠ 0 from mul_ne_zero four_ne_zero hc)
    rw [hγR, hc1]
    ring
  refine ⟨hσpos, mul_nonneg Real.pi_pos.le hδpos.le, fun t => ?_, ?_, hq, hp, ?_⟩
  · rw [← Real.exp_add, quadratic_eval hq, mul_pow, Real.sq_sqrt hσpos.le, hγ', hσR, hc1]
    congr 1
    ring
  · have hds : √(δ : ℝ) * √(σ : ℝ) = 1 := by
      rw [← Real.sqrt_mul hδpos.le, hσR]
      have : (δ : ℝ) * -c2 = 1 := by linarith
      rw [this, Real.sqrt_one]
    have hne : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    rw [Real.sqrt_mul Real.pi_pos.le]
    field_simp
    linear_combination (2 * (half : ℝ) * √Real.pi) * hds + √Real.pi * hhR
  · rw [ho]
    cases reflected <;> simp

/-- The antiderivative between two bounds. -/
private theorem erf_deriv {R P Q : List ℚ} {κ c0 c1 c2 γ δ w half σ offset : ℚ}
    (h : erfCheck false R P Q κ c0 c1 c2 γ δ w half σ offset = true) (x : ℝ) :
    HasDerivAt (fun t : ℝ => polyEval R t * Real.exp (polyEval Q t) +
        half * (Real.exp γ * √(Real.pi * δ)) * Functions.erfR.value (√(σ : ℝ) * (t + offset)))
      (polyEval P x * Real.exp (polyEval Q x)) x := by
  obtain ⟨_, _, hC, hB, _, hp, ho⟩ := erf_facts h
  simp only [Bool.false_eq_true, if_false] at ho
  have hin : HasDerivAt (fun t : ℝ => √(σ : ℝ) * (t + offset)) (√(σ : ℝ) * 1) x :=
    ((hasDerivAt_id x).add_const (offset : ℝ)).const_mul _
  have h2 := ((erf_hasDerivAt (√(σ : ℝ) * (x + offset))).comp x hin).const_mul
    ((half : ℝ) * (Real.exp γ * √(Real.pi * δ)))
  refine ((gaussPrimitive_deriv hp x).add h2).congr_deriv ?_
  have hC' := hC x
  rw [show (x : ℝ) - w = x + offset by rw [ho]; ring] at hC'
  linear_combination (Real.exp γ * Real.exp (-(√(σ : ℝ) * (x + offset)) ^ 2)) * hB + (κ : ℝ) * hC'

/-- The antiderivative above a bound: it vanishes at infinity. -/
private theorem erfc_deriv {R P Q : List ℚ} {κ c0 c1 c2 γ δ w half σ offset : ℚ}
    (h : erfCheck false R P Q κ c0 c1 c2 γ δ w half σ offset = true) :
    (∀ x : ℝ, HasDerivAt (fun t : ℝ => polyEval R t * Real.exp (polyEval Q t) +
        -1 * (half * (Real.exp γ * √(Real.pi * δ)) *
          Functions.erfcR.value (√(σ : ℝ) * (t + offset))))
      (polyEval P x * Real.exp (polyEval Q x)) x) ∧
    Tendsto (fun t : ℝ => polyEval R t * Real.exp (polyEval Q t) +
        -1 * (half * (Real.exp γ * √(Real.pi * δ)) *
          Functions.erfcR.value (√(σ : ℝ) * (t + offset)))) atTop (𝓝 0) := by
  obtain ⟨hσ, _, hC, hB, hq, hp, ho⟩ := erf_facts h
  simp only [Bool.false_eq_true, if_false] at ho
  refine ⟨fun x => ?_, ?_⟩
  · have hin : HasDerivAt (fun t : ℝ => √(σ : ℝ) * (t + offset)) (√(σ : ℝ) * 1) x :=
      ((hasDerivAt_id x).add_const (offset : ℝ)).const_mul _
    have h2 := (((erfc_hasDerivAt (√(σ : ℝ) * (x + offset))).comp x hin).const_mul
      ((half : ℝ) * (Real.exp γ * √(Real.pi * δ)))).const_mul (-1 : ℝ)
    refine ((gaussPrimitive_deriv hp x).add h2).congr_deriv ?_
    have hC' := hC x
    rw [show (x : ℝ) - w = x + offset by rw [ho]; ring] at hC'
    linear_combination (Real.exp γ * Real.exp (-(√(σ : ℝ) * (x + offset)) ^ 2)) * hB +
      (κ : ℝ) * hC'
  · have harg : Tendsto (fun t : ℝ => √(σ : ℝ) * (t + offset)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (offset : ℝ) tendsto_id).const_mul_atTop
        (Real.sqrt_pos.2 hσ)
    have he := ((erfc_tendsto_atTop.comp harg).const_mul
      ((half : ℝ) * (Real.exp γ * √(Real.pi * δ)))).const_mul (-1 : ℝ)
    simpa using (quadratic_vanishes_atTop hq R).add he

/-- The antiderivative below a bound: it vanishes at minus infinity. -/
private theorem erfc_reflected_deriv {R P Q : List ℚ} {κ c0 c1 c2 γ δ w half σ offset : ℚ}
    (h : erfCheck true R P Q κ c0 c1 c2 γ δ w half σ offset = true) :
    (∀ x : ℝ, HasDerivAt (fun t : ℝ => polyEval R t * Real.exp (polyEval Q t) +
        half * (Real.exp γ * √(Real.pi * δ)) *
          Functions.erfcR.value (√(σ : ℝ) * (offset + -1 * t)))
      (polyEval P x * Real.exp (polyEval Q x)) x) ∧
    Tendsto (fun t : ℝ => polyEval R t * Real.exp (polyEval Q t) +
        half * (Real.exp γ * √(Real.pi * δ)) *
          Functions.erfcR.value (√(σ : ℝ) * (offset + -1 * t))) atBot (𝓝 0) := by
  obtain ⟨hσ, _, hC, hB, hq, hp, ho⟩ := erf_facts h
  simp only [if_true] at ho
  refine ⟨fun x => ?_, ?_⟩
  · have hin : HasDerivAt (fun t : ℝ => √(σ : ℝ) * (offset + -1 * t)) (√(σ : ℝ) * (-1 * 1)) x :=
      (((hasDerivAt_id x).const_mul (-1 : ℝ)).const_add (offset : ℝ)).const_mul _
    have h2 := ((erfc_hasDerivAt (√(σ : ℝ) * (offset + -1 * x))).comp x hin).const_mul
      ((half : ℝ) * (Real.exp γ * √(Real.pi * δ)))
    refine ((gaussPrimitive_deriv hp x).add h2).congr_deriv ?_
    have hC' := hC x
    rw [show (-(√(σ : ℝ) * (x - w)) ^ 2) = -(√(σ : ℝ) * (offset + -1 * x)) ^ 2 by rw [ho]; ring]
      at hC'
    linear_combination (Real.exp γ * Real.exp (-(√(σ : ℝ) * (offset + -1 * x)) ^ 2)) * hB +
      (κ : ℝ) * hC'
  · have harg : Tendsto (fun t : ℝ => √(σ : ℝ) * (offset + -1 * t)) atBot atTop := by
      have h1 : Tendsto (fun t : ℝ => -1 * t) atBot atTop := by
        simpa using (tendsto_neg_atBot_atTop : Tendsto (Neg.neg : ℝ → ℝ) atBot atTop)
      exact (tendsto_atTop_add_const_left atBot (offset : ℝ) h1).const_mul_atTop
        (Real.sqrt_pos.2 hσ)
    have he := (erfc_tendsto_atTop.comp harg).const_mul
      ((half : ℝ) * (Real.exp γ * √(Real.pi * δ)))
    simpa using (quadratic_vanishes_atBot hq R).add he

/-- The constant in front of the error function and its argument, between two
bounds: `k·(exp(g)·√(π·d))·erf(√s·(o + n))` after the antiderivative of the
rest. -/
noncomputable def erfBetween (GR : Option ℝ → Option ℝ) (k g d pi s n o : Option ℝ) : Option ℝ :=
  Value.add (GR o) (Value.mul
    (Value.mul k (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))))
    (Functions.erfR.apply (Value.mul (Functions.sqrtR.apply s) (Value.add o n))))

/-- Above a bound: the complement, negated. -/
noncomputable def erfAbove (GR : Option ℝ → Option ℝ) (m k g d pi s n o : Option ℝ) : Option ℝ :=
  Value.add (GR o) (Value.mul m (Value.mul
    (Value.mul k (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))))
    (Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply s) (Value.add o n)))))

/-- Below a bound: the complement of the reflected argument. -/
noncomputable def erfBelow (GR : Option ℝ → Option ℝ) (m k g d pi s n o : Option ℝ) : Option ℝ :=
  Value.add (GR o) (Value.mul
    (Value.mul k (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))))
    (Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply s) (Value.add n (Value.mul m o)))))

/-- The literals of such an antiderivative. -/
private theorem erf_literals {reflected : Bool} {R P Q : List ℚ}
    {κ c0 c1 c2 γ δ w half σ offset : ℚ}
    (h : erfCheck reflected R P Q κ c0 c1 c2 γ δ w half σ offset = true) {k g d pi s n : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) offset)) :
    Value.mul k (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))) =
        some ((half : ℝ) * (Real.exp γ * √(Real.pi * δ))) ∧
      Functions.sqrtR.apply s = some (√(σ : ℝ)) ∧ n = some ((offset : ℚ) : ℝ) := by
  obtain ⟨hσ, hpos, _⟩ := erf_facts h
  refine ⟨?_, ?_, ?_⟩
  · rw [hk, hg, hd, hpi]
    simp [Value.mul, Function1.apply, Functions.expR, Functions.sqrtR, Functions.pi,
      Numeric.denote, hpos]
  · rw [hs]
    simp [Function1.apply, Functions.sqrtR, Numeric.denote, hσ.le]
  · rw [hn]
    simp [Numeric.denote]

/-- Between two bounds, with the error function. -/
theorem IntervalTerms.erf {a b m : Option ℝ} {v : ℝ → Option ℝ} {GR : Option ℝ → Option ℝ}
    {R P Q : List ℚ} (κ c0 c1 c2 γ δ w half σ offset : ℚ) (hv : EventualExp ⊤ v P Q)
    (hGR : EventualExp ⊤ (fun t => GR (some t)) R Q)
    (h : erfCheck false R P Q κ c0 c1 c2 γ δ w half σ offset = true) {k g d pi s n : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) offset)) :
    IntervalTerms a b m v (Value.add (erfBetween GR k g d pi s n b)
      (Value.mul m (erfBetween GR k g d pi s n a))) := by
  obtain ⟨hK, hS, hN⟩ := erf_literals h hk hg hd hpi hs hn
  have hc : Continuous fun x : ℝ => polyEval P x * Real.exp (polyEval Q x) :=
    (polyEval_continuous P).mul (Real.continuous_exp.comp (polyEval_continuous Q))
  refine .primitive (G := erfBetween GR k g d pi s n) (Filter.eventually_top.1 hv)
    (fun t => ?_) hc (erf_deriv h)
  have hR : GR (some t) = _ := Filter.eventually_top.1 hGR t
  rw [erfBetween, hR, hK, hS, hN]
  show Value.add (some _) (Value.mul (some _) (Functions.erfR.apply (some _))) = _
  rw [erf_apply]
  rfl

/-- The same under a scale that does not mention the axis. -/
theorem IntervalTerms.scaledErf {a b m : Option ℝ} {v : ℝ → Option ℝ} {c : Option ℝ}
    {GR : Option ℝ → Option ℝ} {R P Q : List ℚ} (κ c0 c1 c2 γ δ w half σ offset : ℚ)
    (hv : EventualScaled ⊤ v c P Q) (hGR : EventualExp ⊤ (fun t => GR (some t)) R Q)
    (h : erfCheck false R P Q κ c0 c1 c2 γ δ w half σ offset = true) {k g d pi s n : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) offset)) :
    IntervalTerms a b m v (Value.mul c (Value.add (erfBetween GR k g d pi s n b)
      (Value.mul m (erfBetween GR k g d pi s n a)))) := by
  obtain ⟨hK, hS, hN⟩ := erf_literals h hk hg hd hpi hs hn
  have hc : Continuous fun x : ℝ => polyEval P x * Real.exp (polyEval Q x) :=
    (polyEval_continuous P).mul (Real.continuous_exp.comp (polyEval_continuous Q))
  refine .scaledPrimitive (G := erfBetween GR k g d pi s n) (Filter.eventually_top.1 hv)
    (fun t => ?_) hc (erf_deriv h)
  have hR : GR (some t) = _ := Filter.eventually_top.1 hGR t
  rw [erfBetween, hR, hK, hS, hN]
  show Value.add (some _) (Value.mul (some _) (Functions.erfR.apply (some _))) = _
  rw [erf_apply]
  rfl

/-- Above a bound, with the complement of the error function. -/
theorem HalfLineTerms.erf {a m : Option ℝ} {v : ℝ → Option ℝ}
    {GR : Option ℝ → Option ℝ} {R P Q : List ℚ} (κ c0 c1 c2 γ δ w half σ offset : ℚ)
    (hv : EventualExp ⊤ v P Q) (hGR : EventualExp ⊤ (fun t => GR (some t)) R Q) (h0 : GR none = none)
    (h : erfCheck false R P Q κ c0 c1 c2 γ δ w half σ offset = true) {u k g d pi s n : Option ℝ}
    (hu : u = some (Numeric.denote (s := .real) (-1 : ℚ))) (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) offset)) :
    HalfLineTerms a m v (Value.mul m (erfAbove GR u k g d pi s n a)) := by
  obtain ⟨hK, hS, hN⟩ := erf_literals h hk hg hd hpi hs hn
  obtain ⟨_, _, _, _, hq, hp, _⟩ := erf_facts h
  obtain ⟨hD, hT⟩ := erfc_deriv h
  have hU : u = some (-1 : ℝ) := by rw [hu]; simp [Numeric.denote]
  refine .primitive (G := erfAbove GR u k g d pi s n) (Filter.eventually_top.1 hv) (fun t => ?_) ?_
    (fun l => (gaussian_polynomial_integral hq hp).1.integrableOn) hD hT
  · have hR : GR (some t) = _ := Filter.eventually_top.1 hGR t
    rw [erfAbove, hR, hU, hK, hS, hN]
    show Value.add (some _) (Value.mul (some _) (Value.mul (some _)
      (Functions.erfcR.apply (some _)))) = _
    rw [erfc_apply]
    rfl
  · show Value.add (GR none) _ = none
    rw [h0]
    rfl

/-- The same under a scale that does not mention the axis. -/
theorem HalfLineTerms.scaledErf {a m : Option ℝ} {v : ℝ → Option ℝ} {c : Option ℝ}
    {GR : Option ℝ → Option ℝ} {R P Q : List ℚ} (κ c0 c1 c2 γ δ w half σ offset : ℚ)
    (hv : EventualScaled ⊤ v c P Q) (hGR : EventualExp ⊤ (fun t => GR (some t)) R Q) (h0 : GR none = none)
    (h : erfCheck false R P Q κ c0 c1 c2 γ δ w half σ offset = true) {u k g d pi s n : Option ℝ}
    (hu : u = some (Numeric.denote (s := .real) (-1 : ℚ))) (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) offset)) :
    HalfLineTerms a m v (Value.mul c (Value.mul m (erfAbove GR u k g d pi s n a))) := by
  obtain ⟨hK, hS, hN⟩ := erf_literals h hk hg hd hpi hs hn
  obtain ⟨_, _, _, _, hq, hp, _⟩ := erf_facts h
  obtain ⟨hD, hT⟩ := erfc_deriv h
  have hU : u = some (-1 : ℝ) := by rw [hu]; simp [Numeric.denote]
  refine .scaledPrimitive (G := erfAbove GR u k g d pi s n) (Filter.eventually_top.1 hv) (fun t => ?_) ?_
    (fun l => (gaussian_polynomial_integral hq hp).1.integrableOn) hD hT
  · have hR : GR (some t) = _ := Filter.eventually_top.1 hGR t
    rw [erfAbove, hR, hU, hK, hS, hN]
    show Value.add (some _) (Value.mul (some _) (Value.mul (some _)
      (Functions.erfcR.apply (some _)))) = _
    rw [erfc_apply]
    rfl
  · show Value.add (GR none) _ = none
    rw [h0]
    rfl

/-- Below a bound, with the complement of the error function of the reflected
argument. -/
theorem UpperTerms.erf {b : Option ℝ} {v : ℝ → Option ℝ}
    {GR : Option ℝ → Option ℝ} {R P Q : List ℚ} (κ c0 c1 c2 γ δ w half σ offset : ℚ)
    (hv : EventualExp ⊤ v P Q) (hGR : EventualExp ⊤ (fun t => GR (some t)) R Q) (h0 : GR none = none)
    (h : erfCheck true R P Q κ c0 c1 c2 γ δ w half σ offset = true) {u k g d pi s n : Option ℝ}
    (hu : u = some (Numeric.denote (s := .real) (-1 : ℚ))) (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) offset)) :
    UpperTerms b v (erfBelow GR u k g d pi s n b) := by
  obtain ⟨hK, hS, hN⟩ := erf_literals h hk hg hd hpi hs hn
  obtain ⟨_, _, _, _, hq, hp, _⟩ := erf_facts h
  obtain ⟨hD, hT⟩ := erfc_reflected_deriv h
  have hU : u = some (-1 : ℝ) := by rw [hu]; simp [Numeric.denote]
  refine .primitive (G := erfBelow GR u k g d pi s n) (Filter.eventually_top.1 hv) (fun t => ?_) ?_
    (fun l => (gaussian_polynomial_integral hq hp).1.integrableOn) hD hT
  · have hR : GR (some t) = _ := Filter.eventually_top.1 hGR t
    rw [erfBelow, hR, hU, hK, hS, hN]
    show Value.add (some _) (Value.mul (some _) (Functions.erfcR.apply (some _))) = _
    rw [erfc_apply]
    rfl
  · show Value.add (GR none) _ = none
    rw [h0]
    rfl

/-- The same under a scale that does not mention the axis. -/
theorem UpperTerms.scaledErf {b : Option ℝ} {v : ℝ → Option ℝ} {c : Option ℝ}
    {GR : Option ℝ → Option ℝ} {R P Q : List ℚ} (κ c0 c1 c2 γ δ w half σ offset : ℚ)
    (hv : EventualScaled ⊤ v c P Q) (hGR : EventualExp ⊤ (fun t => GR (some t)) R Q) (h0 : GR none = none)
    (h : erfCheck true R P Q κ c0 c1 c2 γ δ w half σ offset = true) {u k g d pi s n : Option ℝ}
    (hu : u = some (Numeric.denote (s := .real) (-1 : ℚ))) (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) offset)) :
    UpperTerms b v (Value.mul c (erfBelow GR u k g d pi s n b)) := by
  obtain ⟨hK, hS, hN⟩ := erf_literals h hk hg hd hpi hs hn
  obtain ⟨_, _, _, _, hq, hp, _⟩ := erf_facts h
  obtain ⟨hD, hT⟩ := erfc_reflected_deriv h
  have hU : u = some (-1 : ℝ) := by rw [hu]; simp [Numeric.denote]
  refine .scaledPrimitive (G := erfBelow GR u k g d pi s n) (Filter.eventually_top.1 hv) (fun t => ?_) ?_
    (fun l => (gaussian_polynomial_integral hq hp).1.integrableOn) hD hT
  · have hR : GR (some t) = _ := Filter.eventually_top.1 hGR t
    rw [erfBelow, hR, hU, hK, hS, hN]
    show Value.add (some _) (Value.mul (some _) (Functions.erfcR.apply (some _))) = _
    rw [erfc_apply]
    rfl
  · show Value.add (GR none) _ = none
    rw [h0]
    rfl

end QSym.Distribution.StepSource
