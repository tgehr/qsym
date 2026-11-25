import QSym.DistributionGaussianSymbolic
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

/-! Constant and linear coefficients that do not mention the axis. The
exponent is a quadratic by its structure, with a curvature that is a negative
rational: the vertex is a multiple of the linear coefficient, and the constant
in front of the error function has the exponential of the value at the vertex,
`c₀ + γ·c₁²`. A coefficient that is undefined leaves the value undefined
everywhere, and that constant with it. -/

/-- The checks of the antiderivative with the error function under a constant
`κ`: the curvature `q₂` is negative, `γ = -1/(4·q₂)`, `δ = -1/q₂`,
`w = 1/(2·q₂)`, half the constant, the negated curvature `σ`, and the factor
`ν` of the linear coefficient in the argument, `-w` where it is reflected and
`w` otherwise. -/
def symErfCheck (reflected : Bool) (P : List ℚ) (κ q2 γ δ w half σ ν : ℚ) : Bool :=
  polyZero (polyAdd P (polyScale (-1) [κ])) && decide (q2 < 0) && decide (γ * (4 * q2) = -1) &&
    decide (δ * q2 = -1) && decide (w * (2 * q2) = 1) && decide (half * 2 = κ) &&
    decide (σ = -q2) && decide (ν = (if reflected then -w else w))

/-- What the checks say of the real functions, at real coefficients. -/
private theorem symErf_facts {reflected : Bool} {P : List ℚ} {κ q2 γ δ w half σ ν : ℚ}
    (h : symErfCheck reflected P κ q2 γ δ w half σ ν = true) (a b : ℝ) :
    (q2 : ℝ) < 0 ∧ (0 : ℝ) < σ ∧ 0 ≤ Real.pi * (δ : ℝ) ∧ (∀ x : ℝ, polyEval P x = κ) ∧
      (∀ t : ℝ, Real.exp (a + γ * (b * b)) * Real.exp (-(√(σ : ℝ) * (t + w * b)) ^ 2) =
        Real.exp (a + b * t + q2 * t ^ 2)) ∧
      (half : ℝ) * √(Real.pi * δ) * (2 / √Real.pi * √(σ : ℝ)) = κ ∧
      (ν : ℝ) = (if reflected then -(w : ℝ) else w) := by
  simp only [symErfCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hP, hq⟩, hγ⟩, hδ⟩, hw⟩, hh⟩, hσ⟩, hν⟩ := h
  have hcR : ((q2 : ℚ) : ℝ) < 0 := by exact_mod_cast hq
  have hc : ((q2 : ℚ) : ℝ) ≠ 0 := hcR.ne
  have hγR : (γ : ℝ) * (4 * q2) = -1 := by exact_mod_cast hγ
  have hδR : (δ : ℝ) * q2 = -1 := by exact_mod_cast hδ
  have hwR : (w : ℝ) * (2 * q2) = 1 := by exact_mod_cast hw
  have hhR : (half : ℝ) * 2 = κ := by exact_mod_cast hh
  have hσR : (σ : ℝ) = -q2 := by exact_mod_cast hσ
  have hσpos : (0 : ℝ) < σ := by rw [hσR]; linarith
  have hδpos : (0 : ℝ) < δ := by nlinarith
  have hγ' : (γ : ℝ) = -(q2 * w ^ 2) := by
    apply mul_right_cancel₀ (show (4 * (q2 : ℝ)) ≠ 0 from mul_ne_zero four_ne_zero hc)
    linear_combination hγR + (2 * (q2 : ℝ) * w + 1) * hwR
  refine ⟨hcR, hσpos, mul_nonneg Real.pi_pos.le hδpos.le, fun x => ?_, fun t => ?_, ?_, ?_⟩
  · have hz := polyEval_zero hP x
    rw [polyEval_add, polyEval_scale] at hz
    simp only [polyEval] at hz
    push_cast at hz
    linarith
  · rw [← Real.exp_add, mul_pow, Real.sq_sqrt hσpos.le, hγ', hσR]
    congr 1
    linear_combination (b * t) * hwR
  · have hds : √(δ : ℝ) * √(σ : ℝ) = 1 := by
      rw [← Real.sqrt_mul hδpos.le, hσR]
      have : (δ : ℝ) * -q2 = 1 := by linarith
      rw [this, Real.sqrt_one]
    have hne : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    rw [Real.sqrt_mul Real.pi_pos.le]
    field_simp
    linear_combination (2 * (half : ℝ) * √Real.pi) * hds + √Real.pi * hhR
  · rw [hν]
    cases reflected <;> simp

/-- The antiderivative between two bounds. -/
private theorem symErf_deriv {P : List ℚ} {κ q2 γ δ w half σ ν : ℚ}
    (h : symErfCheck false P κ q2 γ δ w half σ ν = true) (a b x : ℝ) :
    HasDerivAt (fun t : ℝ => half * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)) *
        Functions.erfR.value (√(σ : ℝ) * (t + ν * b)))
      (κ * Real.exp (a + b * x + q2 * x ^ 2)) x := by
  obtain ⟨_, _, _, _, hC, hB, hν⟩ := symErf_facts h a b
  simp only [Bool.false_eq_true, if_false] at hν
  rw [hν]
  have hin : HasDerivAt (fun t : ℝ => √(σ : ℝ) * (t + w * b)) (√(σ : ℝ) * 1) x :=
    ((hasDerivAt_id x).add_const ((w : ℝ) * b)).const_mul _
  have h2 := ((erf_hasDerivAt (√(σ : ℝ) * (x + w * b))).comp x hin).const_mul
    ((half : ℝ) * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)))
  refine h2.congr_deriv ?_
  linear_combination
    (Real.exp (a + γ * (b * b)) * Real.exp (-(√(σ : ℝ) * (x + w * b)) ^ 2)) * hB + (κ : ℝ) * hC x

/-- The antiderivative above a bound: it vanishes at infinity. -/
private theorem symErfc_deriv {P : List ℚ} {κ q2 γ δ w half σ ν : ℚ}
    (h : symErfCheck false P κ q2 γ δ w half σ ν = true) (a b : ℝ) :
    (∀ x : ℝ, HasDerivAt (fun t : ℝ => -1 * (half * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)) *
        Functions.erfcR.value (√(σ : ℝ) * (t + ν * b))))
      (κ * Real.exp (a + b * x + q2 * x ^ 2)) x) ∧
    Tendsto (fun t : ℝ => -1 * (half * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)) *
        Functions.erfcR.value (√(σ : ℝ) * (t + ν * b)))) atTop (𝓝 0) := by
  obtain ⟨_, hσ, _, _, hC, hB, hν⟩ := symErf_facts h a b
  simp only [Bool.false_eq_true, if_false] at hν
  rw [hν]
  refine ⟨fun x => ?_, ?_⟩
  · have hin : HasDerivAt (fun t : ℝ => √(σ : ℝ) * (t + w * b)) (√(σ : ℝ) * 1) x :=
      ((hasDerivAt_id x).add_const ((w : ℝ) * b)).const_mul _
    have h2 := (((erfc_hasDerivAt (√(σ : ℝ) * (x + w * b))).comp x hin).const_mul
      ((half : ℝ) * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)))).const_mul (-1 : ℝ)
    refine h2.congr_deriv ?_
    linear_combination
      (Real.exp (a + γ * (b * b)) * Real.exp (-(√(σ : ℝ) * (x + w * b)) ^ 2)) * hB +
        (κ : ℝ) * hC x
  · have harg : Tendsto (fun t : ℝ => √(σ : ℝ) * (t + w * b)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop ((w : ℝ) * b) tendsto_id).const_mul_atTop
        (Real.sqrt_pos.2 hσ)
    have he := ((erfc_tendsto_atTop.comp harg).const_mul
      ((half : ℝ) * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)))).const_mul (-1 : ℝ)
    simpa using he

/-- The antiderivative below a bound: it vanishes at minus infinity. -/
private theorem symErfc_reflected_deriv {P : List ℚ} {κ q2 γ δ w half σ ν : ℚ}
    (h : symErfCheck true P κ q2 γ δ w half σ ν = true) (a b : ℝ) :
    (∀ x : ℝ, HasDerivAt (fun t : ℝ => half * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)) *
        Functions.erfcR.value (√(σ : ℝ) * (ν * b + -1 * t)))
      (κ * Real.exp (a + b * x + q2 * x ^ 2)) x) ∧
    Tendsto (fun t : ℝ => half * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)) *
        Functions.erfcR.value (√(σ : ℝ) * (ν * b + -1 * t))) atBot (𝓝 0) := by
  obtain ⟨_, hσ, _, _, hC, hB, hν⟩ := symErf_facts h a b
  simp only [if_true] at hν
  rw [hν]
  refine ⟨fun x => ?_, ?_⟩
  · have hin : HasDerivAt (fun t : ℝ => √(σ : ℝ) * (-(w : ℝ) * b + -1 * t))
        (√(σ : ℝ) * (-1 * 1)) x :=
      (((hasDerivAt_id x).const_mul (-1 : ℝ)).const_add (-(w : ℝ) * b)).const_mul _
    have h2 := ((erfc_hasDerivAt (√(σ : ℝ) * (-(w : ℝ) * b + -1 * x))).comp x hin).const_mul
      ((half : ℝ) * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)))
    refine h2.congr_deriv ?_
    have hC' := hC x
    rw [show (-(√(σ : ℝ) * (x + w * b)) ^ 2) = -(√(σ : ℝ) * (-(w : ℝ) * b + -1 * x)) ^ 2 by ring]
      at hC'
    linear_combination
      (Real.exp (a + γ * (b * b)) * Real.exp (-(√(σ : ℝ) * (-(w : ℝ) * b + -1 * x)) ^ 2)) * hB +
        (κ : ℝ) * hC'
  · have harg : Tendsto (fun t : ℝ => √(σ : ℝ) * (-(w : ℝ) * b + -1 * t)) atBot atTop := by
      have h1 : Tendsto (fun t : ℝ => -1 * t) atBot atTop := by
        simpa using (tendsto_neg_atBot_atTop : Tendsto (Neg.neg : ℝ → ℝ) atBot atTop)
      exact (tendsto_atTop_add_const_left atBot (-(w : ℝ) * b) h1).const_mul_atTop
        (Real.sqrt_pos.2 hσ)
    have he := (erfc_tendsto_atTop.comp harg).const_mul
      ((half : ℝ) * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ)))
    simpa using he

/-- The constant in front of the error function:
`k·(exp(c₀ + g·(c₁·c₁))·√(π·d))`. -/
noncomputable def symErfConstant (c0 c1 k g d pi : Option ℝ) : Option ℝ :=
  Value.mul k (Value.mul
    (Functions.expR.apply (Value.add c0 (Value.mul g (Value.mul c1 c1))))
    (Functions.sqrtR.apply (Value.mul pi d)))

/-- Between two bounds: the constant times `erf(√s·(o + n·c₁))`. -/
noncomputable def symErfBetween (c0 c1 k g d pi s n o : Option ℝ) : Option ℝ :=
  Value.mul (symErfConstant c0 c1 k g d pi)
    (Functions.erfR.apply (Value.mul (Functions.sqrtR.apply s) (Value.add o (Value.mul n c1))))

/-- Above a bound: the complement, negated. -/
noncomputable def symErfAbove (c0 c1 u k g d pi s n o : Option ℝ) : Option ℝ :=
  Value.mul u (Value.mul (symErfConstant c0 c1 k g d pi)
    (Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply s) (Value.add o (Value.mul n c1)))))

/-- Below a bound: the complement of the reflected argument. -/
noncomputable def symErfBelow (c0 c1 u k g d pi s n o : Option ℝ) : Option ℝ :=
  Value.mul (symErfConstant c0 c1 k g d pi)
    (Functions.erfcR.apply
      (Value.mul (Functions.sqrtR.apply s) (Value.add (Value.mul n c1) (Value.mul u o))))

/-- That constant is undefined where a coefficient is. -/
private theorem symErfConstant_missing {c0 c1 : Option ℝ} (k g d pi : Option ℝ)
    (h : c0 = none ∨ c1 = none) : symErfConstant c0 c1 k g d pi = none := by
  have hexp : Functions.expR.apply (Value.add c0 (Value.mul g (Value.mul c1 c1))) = none := by
    rcases h with rfl | rfl
    · rfl
    · cases c0 <;> cases g <;> rfl
  rw [symErfConstant, hexp]
  cases k <;> rfl

/-- The literals of such an antiderivative at real coefficients. -/
private theorem symErf_literals {reflected : Bool} {P : List ℚ} {κ q2 γ δ w half σ ν : ℚ}
    (h : symErfCheck reflected P κ q2 γ δ w half σ ν = true) (a b : ℝ) {k g d pi s n : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) ν)) :
    symErfConstant (some a) (some b) k g d pi =
        some ((half : ℝ) * (Real.exp (a + γ * (b * b)) * √(Real.pi * δ))) ∧
      Functions.sqrtR.apply s = some (√(σ : ℝ)) ∧ n = some ((ν : ℚ) : ℝ) := by
  obtain ⟨_, hσ, hpos, _⟩ := symErf_facts h a b
  refine ⟨?_, ?_, ?_⟩
  · rw [symErfConstant, hk, hg, hd, hpi]
    simp [Value.mul, Value.add, Function1.apply, Functions.expR, Functions.sqrtR, Functions.pi,
      Numeric.denote, hpos]
  · rw [hs]
    simp [Function1.apply, Functions.sqrtR, Numeric.denote, hσ.le]
  · rw [hn]
    simp [Numeric.denote]

/-- The value below the mask: undefined everywhere where a coefficient is,
and the constant times the exponential of the quadratic under the scale
otherwise. -/
private theorem symErf_value {reflected : Bool} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} {κ q2 γ δ w half σ ν : ℚ}
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : symErfCheck reflected P κ q2 γ δ w half σ ν = true) :
    ((c0 = none ∨ c1 = none) → ∀ x, v x = none) ∧
      ∀ a b : ℝ, c0 = some a → c1 = some b →
        ∀ x, v x = scaleBy S (some (κ * Real.exp (a + b * x + q2 * x ^ 2))) := by
  have hvx : ∀ x, v x = scaleBy S (Value.mul (some (polyEval P x)) (Functions.expR.apply (E x))) :=
    fun x => hv.plain x
  refine ⟨fun hm x => ?_, fun a b ha hb x => ?_⟩
  · have hEx : E x = none := by
      rcases hm with rfl | rfl
      · exact hE.missing (Or.inl rfl) x
      · exact hE.missing (Or.inr (Or.inl rfl)) x
    rw [hvx, hEx]
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul, Function1.apply]
  · subst ha hb
    obtain ⟨_, _, _, hP, _⟩ := symErf_facts h a b
    have hEx : E x = some (a + b * x + q2 * x ^ 2) := by
      rw [hE.equation, h2]
      simp [coefValue, Value.add, Value.mul, Numeric.denote]
      ring
    rw [hvx, hEx, hP]
    simp [Value.mul, Function1.apply, Functions.expR]

/-- Between two bounds, with the error function around a vertex that does not
mention the axis. -/
theorem IntervalTerms.symbolicErf {a b m : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ q2 γ δ w half σ ν : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : symErfCheck false P κ q2 γ δ w half σ ν = true) {k g d pi s n : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) ν)) :
    IntervalTerms a b m v (scaleBy S (Value.add (symErfBetween c0 c1 k g d pi s n b)
      (Value.mul m (symErfBetween c0 c1 k g d pi s n a)))) := by
  obtain ⟨hmiss, hval⟩ := symErf_value hv hE h2 h
  by_cases hm : c0 = none ∨ c1 = none
  · have hout : scaleBy S (Value.add (symErfBetween c0 c1 k g d pi s n b)
        (Value.mul m (symErfBetween c0 c1 k g d pi s n a))) = none := by
      simp only [symErfBetween, symErfConstant_missing k g d pi hm]
      rcases S with _ | _ | s' <;> rfl
    rw [hout]
    exact IntervalTerms.undefined (hmiss hm)
  obtain ⟨a0, rfl⟩ : ∃ a0, c0 = some a0 := Option.ne_none_iff_exists'.1 fun h0 => hm (Or.inl h0)
  obtain ⟨b1, rfl⟩ : ∃ b1, c1 = some b1 := Option.ne_none_iff_exists'.1 fun h0 => hm (Or.inr h0)
  obtain ⟨hK, hS, hN⟩ := symErf_literals h a0 b1 hk hg hd hpi hs hn
  have hG : ∀ t, symErfBetween (some a0) (some b1) k g d pi s n (some t) =
      some ((half : ℝ) * (Real.exp (a0 + γ * (b1 * b1)) * √(Real.pi * δ)) *
        Functions.erfR.value (√(σ : ℝ) * (t + ν * b1))) := fun t => by
    rw [symErfBetween, hK, hS, hN]
    show Value.mul (some _) (Functions.erfR.apply (some _)) = _
    rw [erf_apply]
    rfl
  have hc : Continuous fun x : ℝ => (κ : ℝ) * Real.exp (a0 + b1 * x + q2 * x ^ 2) :=
    continuous_const.mul (Real.continuous_exp.comp (by fun_prop))
  rcases S with _ | c
  · exact .primitive (G := symErfBetween (some a0) (some b1) k g d pi s n)
      (hval a0 b1 rfl rfl) hG hc (symErf_deriv h a0 b1)
  · exact .scaledPrimitive (G := symErfBetween (some a0) (some b1) k g d pi s n)
      (hval a0 b1 rfl rfl) hG hc (symErf_deriv h a0 b1)

/-- Above a bound, with the complement of the error function. -/
theorem HalfLineTerms.symbolicErf {a m : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ q2 γ δ w half σ ν : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : symErfCheck false P κ q2 γ δ w half σ ν = true) {u k g d pi s n : Option ℝ}
    (hu : u = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) ν)) :
    HalfLineTerms a m v (scaleBy S (Value.mul m (symErfAbove c0 c1 u k g d pi s n a))) := by
  obtain ⟨hmiss, hval⟩ := symErf_value hv hE h2 h
  have hU : u = some (-1 : ℝ) := by rw [hu]; simp [Numeric.denote]
  by_cases hm : c0 = none ∨ c1 = none
  · have hout : scaleBy S (Value.mul m (symErfAbove c0 c1 u k g d pi s n a)) = none := by
      simp only [symErfAbove, symErfConstant_missing k g d pi hm, hU]
      rcases S with _ | _ | s' <;> cases m <;> rfl
    rw [hout]
    exact HalfLineTerms.undefined (hmiss hm)
  obtain ⟨a0, rfl⟩ : ∃ a0, c0 = some a0 := Option.ne_none_iff_exists'.1 fun h0 => hm (Or.inl h0)
  obtain ⟨b1, rfl⟩ : ∃ b1, c1 = some b1 := Option.ne_none_iff_exists'.1 fun h0 => hm (Or.inr h0)
  obtain ⟨hK, hS, hN⟩ := symErf_literals h a0 b1 hk hg hd hpi hs hn
  obtain ⟨hq, _⟩ := symErf_facts h a0 b1
  obtain ⟨hD, hT⟩ := symErfc_deriv h a0 b1
  have hG : ∀ t, symErfAbove (some a0) (some b1) u k g d pi s n (some t) =
      some (-1 * ((half : ℝ) * (Real.exp (a0 + γ * (b1 * b1)) * √(Real.pi * δ)) *
        Functions.erfcR.value (√(σ : ℝ) * (t + ν * b1)))) := fun t => by
    rw [symErfAbove, hU, hK, hS, hN]
    show Value.mul (some _) (Value.mul (some _) (Functions.erfcR.apply (some _))) = _
    rw [erfc_apply]
    rfl
  have h0 : symErfAbove (some a0) (some b1) u k g d pi s n none = none := by
    rw [symErfAbove, hU, hK, hS]
    rfl
  have hi : ∀ l : ℝ, IntegrableOn (fun x : ℝ => (κ : ℝ) * Real.exp (a0 + b1 * x + q2 * x ^ 2))
      (Ioi l) volume := fun l => ((gaussian_integrable a0 b1 q2 hq).const_mul _).integrableOn
  rcases S with _ | c
  · exact .primitive (G := symErfAbove (some a0) (some b1) u k g d pi s n)
      (hval a0 b1 rfl rfl) hG h0 hi hD hT
  · exact .scaledPrimitive (G := symErfAbove (some a0) (some b1) u k g d pi s n)
      (hval a0 b1 rfl rfl) hG h0 hi hD hT

/-- Below a bound, with the complement of the error function of the reflected
argument. -/
theorem UpperTerms.symbolicErf {b : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ q2 γ δ w half σ ν : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : symErfCheck true P κ q2 γ δ w half σ ν = true) {u k g d pi s n : Option ℝ}
    (hu : u = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) ν)) :
    UpperTerms b v (scaleBy S (symErfBelow c0 c1 u k g d pi s n b)) := by
  obtain ⟨hmiss, hval⟩ := symErf_value hv hE h2 h
  have hU : u = some (-1 : ℝ) := by rw [hu]; simp [Numeric.denote]
  by_cases hm : c0 = none ∨ c1 = none
  · have hout : scaleBy S (symErfBelow c0 c1 u k g d pi s n b) = none := by
      simp only [symErfBelow, symErfConstant_missing k g d pi hm]
      rcases S with _ | _ | s' <;> rfl
    rw [hout]
    exact UpperTerms.undefined (hmiss hm)
  obtain ⟨a0, rfl⟩ : ∃ a0, c0 = some a0 := Option.ne_none_iff_exists'.1 fun h0 => hm (Or.inl h0)
  obtain ⟨b1, rfl⟩ : ∃ b1, c1 = some b1 := Option.ne_none_iff_exists'.1 fun h0 => hm (Or.inr h0)
  obtain ⟨hK, hS, hN⟩ := symErf_literals h a0 b1 hk hg hd hpi hs hn
  obtain ⟨hq, _⟩ := symErf_facts h a0 b1
  obtain ⟨hD, hT⟩ := symErfc_reflected_deriv h a0 b1
  have hG : ∀ t, symErfBelow (some a0) (some b1) u k g d pi s n (some t) =
      some ((half : ℝ) * (Real.exp (a0 + γ * (b1 * b1)) * √(Real.pi * δ)) *
        Functions.erfcR.value (√(σ : ℝ) * (ν * b1 + -1 * t))) := fun t => by
    rw [symErfBelow, hU, hK, hS, hN]
    show Value.mul (some _) (Functions.erfcR.apply (some _)) = _
    rw [erfc_apply]
    rfl
  have h0 : symErfBelow (some a0) (some b1) u k g d pi s n none = none := by
    rw [symErfBelow, hU, hK, hS, hN]
    rfl
  have hi : ∀ l : ℝ, IntegrableOn (fun x : ℝ => (κ : ℝ) * Real.exp (a0 + b1 * x + q2 * x ^ 2))
      (Iic l) volume := fun l => ((gaussian_integrable a0 b1 q2 hq).const_mul _).integrableOn
  rcases S with _ | c
  · exact .primitive (G := symErfBelow (some a0) (some b1) u k g d pi s n)
      (hval a0 b1 rfl rfl) hG h0 hi hD hT
  · exact .scaledPrimitive (G := symErfBelow (some a0) (some b1) u k g d pi s n)
      (hval a0 b1 rfl rfl) hG h0 hi hD hT

/-! A rate that does not mention the axis. Beyond a single bound the
exponential of a linear exponent is integrable exactly where its rate has the
sign of decay, so the observation stands under the guard of that sign: where
the rate has the other sign, or is zero, the integrand is defined and not
integrable. Under a scale that may vanish the integrand is zero where the
scale is, whatever the rate. -/

/-- The exponential of a linear exponent with a negative rate above a bound. -/
theorem exp_linear_Ioi (α : ℝ) {β : ℝ} (hβ : β < 0) (l : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (α + β * x)) (Ioi l) volume ∧
      ∫ x in Ioi l, Real.exp (α + β * x) = -(β⁻¹ * Real.exp (α + β * l)) := by
  have he : (fun x : ℝ => Real.exp (α + β * x)) = fun x => Real.exp α * Real.exp (β * x) := by
    funext x
    rw [Real.exp_add]
  have hne : β ≠ 0 := hβ.ne
  rw [he]
  refine ⟨(integrableOn_exp_mul_Ioi hβ l).const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Ioi hβ l, Real.exp_add]
  field_simp

/-- With a positive rate below one. -/
theorem exp_linear_Iic (α : ℝ) {β : ℝ} (hβ : 0 < β) (u : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (α + β * x)) (Iic u) volume ∧
      ∫ x in Iic u, Real.exp (α + β * x) = β⁻¹ * Real.exp (α + β * u) := by
  have he : (fun x : ℝ => Real.exp (α + β * x)) = fun x => Real.exp α * Real.exp (β * x) := by
    funext x
    rw [Real.exp_add]
  have hne : β ≠ 0 := hβ.ne'
  rw [he]
  refine ⟨(integrableOn_exp_mul_Iic hβ u).const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Iic hβ u, Real.exp_add]
  field_simp

/-- With a rate that is not negative it is not integrable above a bound: it
stays above its value there. -/
theorem exp_linear_not_integrableOn_Ioi (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) (l : ℝ) {k : ℝ}
    (hk : k ≠ 0) : ¬ IntegrableOn (fun x : ℝ => k * Real.exp (α + β * x)) (Ioi l) volume := by
  intro hi
  have hs : IntegrableOn (fun _ : ℝ => |k| * Real.exp (α + β * l)) (Ioi l) volume := by
    refine Integrable.mono' hi.norm aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : l < x := hx
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg k) (Real.exp_pos _).le), norm_mul,
      Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hβ (sub_nonneg.2 hx'.le)])) (abs_nonneg k)
  rw [integrableOn_const] at hs
  rcases hs with h0 | hfin
  · exact (mul_pos (abs_pos.2 hk) (Real.exp_pos _)).ne' h0
  · rw [Real.volume_Ioi] at hfin
    exact lt_irrefl _ hfin

/-- With a rate that is not positive it is not integrable below one. -/
theorem exp_linear_not_integrableOn_Iic (α : ℝ) {β : ℝ} (hβ : β ≤ 0) (u : ℝ) {k : ℝ}
    (hk : k ≠ 0) : ¬ IntegrableOn (fun x : ℝ => k * Real.exp (α + β * x)) (Iic u) volume := by
  intro hi
  have hs : IntegrableOn (fun _ : ℝ => |k| * Real.exp (α + β * u)) (Iic u) volume := by
    refine Integrable.mono' hi.norm aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : x ≤ u := hx
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg k) (Real.exp_pos _).le), norm_mul,
      Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [mul_nonneg_of_nonpos_of_nonpos hβ (sub_nonpos.2 hx')]))
      (abs_nonneg k)
  rw [integrableOn_const] at hs
  rcases hs with h0 | hfin
  · exact (mul_pos (abs_pos.2 hk) (Real.exp_pos _)).ne' h0
  · rw [Real.volume_Iic] at hfin
    exact lt_irrefl _ hfin

/-- The polynomial in front is a constant other than zero. -/
def rateCheck (P : List ℚ) (κ : ℚ) : Bool :=
  polyZero (polyAdd P (polyScale (-1) [κ])) && decide (κ ≠ 0)

/-- The value below the mask: undefined everywhere where a coefficient or the
scale is, and the constant times the exponential under the scale otherwise. -/
private theorem rate_value {v : ℝ → Option ℝ} {S : Option (Option ℝ)} {P : List ℚ}
    {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} {κ : ℚ} (hv : Bell v S none P (some E))
    (hE : Quadratic E (some c0) (some c1) none) (hP : rateCheck P κ = true) :
    (κ : ℝ) ≠ 0 ∧ ((S = some none ∨ c0 = none ∨ c1 = none) → ∀ x, v x = none) ∧
      ∀ α β : ℝ, S ≠ some none → c0 = some α → c1 = some β →
        ∀ x, v x = some (scaleReal S * (κ * Real.exp (α + β * x))) := by
  simp only [rateCheck, Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨hz, hκ⟩ := hP
  have hPx : ∀ x : ℝ, polyEval P x = κ := fun x => by
    have h0 := polyEval_zero hz x
    rw [polyEval_add, polyEval_scale] at h0
    simp only [polyEval] at h0
    push_cast at h0
    linarith
  have hvx : ∀ x, v x = scaleBy S (Value.mul (some (polyEval P x)) (Functions.expR.apply (E x))) :=
    fun x => hv.plain x
  refine ⟨by exact_mod_cast hκ, fun hm x => ?_, fun α β hS h0 h1 x => ?_⟩
  · rw [hvx]
    rcases hm with rfl | rfl | rfl
    · rfl
    · have : E x = none := by rw [hE.equation]; rfl
      rw [this]
      rcases S with _ | _ | s <;> simp [scaleBy, Value.mul, Function1.apply]
    · have : E x = none := by rw [hE.equation]; cases c0 <;> rfl
      rw [this]
      rcases S with _ | _ | s <;> simp [scaleBy, Value.mul, Function1.apply]
  · subst h0 h1
    have hEx : E x = some (α + β * x) := by
      rw [hE.equation]
      simp [coefValue, Value.add, Value.mul]
    rw [hvx, hEx, hPx]
    rcases S with _ | _ | s
    · simp [scaleBy, scaleReal, Value.mul, Function1.apply, Functions.expR]
    · exact absurd rfl hS
    · simp [scaleBy, scaleReal, Value.mul, Function1.apply, Functions.expR]

/-- A value that is undefined everywhere is observed as undefined above a
bound: at the points above it, or everywhere where the bound is undefined. -/
private theorem above_undefined (strict : Bool) (a : Option ℝ) {v : ℝ → Option ℝ}
    (hv : ∀ x, v x = none) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) = none := by
  apply if_neg
  intro hd
  rcases compare_lower_cases strict a with ⟨y, hy⟩ | hn
  · obtain ⟨r, hr⟩ := hd.1 y
    simp only [hy, hv] at hr
    cases hr
  · obtain ⟨r, hr⟩ := hd.1 0
    simp only [hn] at hr
    cases hr

private theorem below_undefined (strict : Bool) (b : Option ℝ) {v : ℝ → Option ℝ}
    (hv : ∀ x, v x = none) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) = none := by
  apply if_neg
  intro hd
  rcases compare_upper_cases strict b with ⟨y, hy⟩ | hn
  · obtain ⟨r, hr⟩ := hd.1 y
    simp only [hy, hv] at hr
    cases hr
  · obtain ⟨r, hr⟩ := hd.1 0
    simp only [hn] at hr
    cases hr

/-- Above a bound: `guard(c₁ < 0, -κ·exp(c₀ + c₁·a)/c₁)` under the scale. -/
theorem rate_above (strict : Bool) {a : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (κ : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hP : rateCheck P κ = true) (hS : scaleNonvanishing S) {m k z : Option ℝ}
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) κ))
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) =
      Binding.guardValue (Value.lt c1 z) (scaleBy S (Value.mul m (Value.mul k
        (Value.mul (Value.inv c1) (Functions.expR.apply (Value.add c0 (Value.mul c1 a))))))) := by
  obtain ⟨hκ, hmiss, hval⟩ := rate_value hv hE hP
  have hM : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  have hK : k = some (κ : ℝ) := by rw [hk]; simp [Numeric.denote]
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  by_cases hu : S = some none ∨ c0 = none ∨ c1 = none
  · rw [above_undefined strict a (hmiss hu)]
    rcases hu with rfl | rfl | rfl
    · simp [scaleBy, Value.mul, Binding.guardValue]
    · have : Functions.expR.apply (Value.add (none : Option ℝ) (Value.mul c1 a)) = none := rfl
      rw [this, hM, hK]
      cases Value.inv c1 <;> simp [Value.mul, hnone, Binding.guardValue]
    · simp [Value.lt, Binding.guardValue]
  simp only [not_or] at hu
  obtain ⟨hS', h0, h1⟩ := hu
  obtain ⟨α, rfl⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨β, rfl⟩ := Option.ne_none_iff_exists'.1 h1
  have hg := hval α β hS' rfl rfl
  have hσ : scaleReal S ≠ 0 := by
    rcases S with _ | _ | s
    · simp [scaleReal]
    · exact absurd rfl hS'
    · exact hS s rfl
  rcases a with _ | l
  · rw [show partialIntegral volume (fun x => Value.mask (compare strict none (some x)) (v x)) =
        none from if_neg fun hd => by
          obtain ⟨r, hr⟩ := hd.1 0
          cases strict <;> cases hr]
    have : Functions.expR.apply (Value.add (some α) (Value.mul (some β) none)) = none := rfl
    rw [this, hM, hK]
    cases Value.inv (some β) <;> simp [Value.mul, hnone, Binding.guardValue]
  have hcmp : ∀ x : ℝ, l < x → compare strict (some l) (some x) = some true := fun x hx => by
    cases strict <;> simp [compare, Value.lt, Value.le, hx, hx.le]
  by_cases hβ : β < 0
  · obtain ⟨hi, hint⟩ := exp_linear_Ioi α hβ l
    have hI : ∀ l' : ℝ, IntegrableOn (fun x : ℝ => scaleReal S * (κ * Real.exp (α + β * x)))
        (Ioi l') volume := fun l' =>
      (((exp_linear_Ioi α hβ l').1.const_mul _).const_mul _)
    rw [halfline_integral strict (some l) m hm ⟨fun _ => rfl⟩
      (HalfLineTerms.value hg hI (fun h => by cases h) fun l' hl => by
        cases hl
        rfl)]
    have hne : β ≠ 0 := hβ.ne
    rw [integral_const_mul, integral_const_mul, hint, hM, hK, hZ]
    rcases S with _ | _ | s
    · simp [Value.lt, hβ, Binding.guardValue, scaleBy, scaleReal, Value.mul, Value.add, Value.inv,
        hne, Function1.apply, Functions.expR]
    · exact absurd rfl hS'
    · simp [Value.lt, hβ, Binding.guardValue, scaleBy, scaleReal, Value.mul, Value.add, Value.inv,
        hne, Function1.apply, Functions.expR]
  · have hn : partialIntegral volume
        (fun x => Value.mask (compare strict (some l) (some x)) (v x)) = none := by
      apply if_neg
      rintro ⟨_, hint⟩
      have hon : IntegrableOn (fun x : ℝ => scaleReal S * κ * Real.exp (α + β * x)) (Ioi l)
          volume := by
        refine (hint.integrableOn (s := Ioi l)).congr_fun (fun x hx => ?_) measurableSet_Ioi
        show (Value.mask (compare strict (some l) (some x)) (v x)).getD 0 = _
        rw [hcmp x hx, hg]
        show scaleReal S * (κ * Real.exp (α + β * x)) = _
        ring
      exact exp_linear_not_integrableOn_Ioi α (not_lt.1 hβ) l (mul_ne_zero hσ hκ) hon
    rw [hn, hZ]
    simp [Value.lt, hβ, Binding.guardValue]

/-- The same under a scale that may vanish: zero where the scale is, under
its mask and the guard of that or the sign of the rate, after the scale, the
bound and the coefficients of the exponent. -/
theorem rate_above_masked (strict : Bool) {a : Option ℝ} {v : ℝ → Option ℝ} {c : Option ℝ}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (κ : ℚ)
    (hv : Bell v (some c) none P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hP : rateCheck P κ = true) {m k z : Option ℝ}
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) κ))
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) =
      after [c, a, c0, c1] (Binding.guardValue
        (Value.or (Value.not (Value.nonzero c)) (Value.lt c1 z))
        (Value.mask (Value.nonzero c) (Value.mul c (Value.mul m (Value.mul k
          (Value.mul (Value.inv c1) (Functions.expR.apply (Value.add c0 (Value.mul c1 a))))))))) := by
  obtain ⟨_, hmiss, hval⟩ := rate_value hv hE hP
  rcases c with _ | s
  · rw [above_undefined strict a (hmiss (Or.inl rfl))]
    rfl
  rcases a with _ | l
  · rw [show partialIntegral volume (fun x => Value.mask (compare strict none (some x)) (v x)) =
        none from if_neg fun hd => by
          obtain ⟨r, hr⟩ := hd.1 0
          cases strict <;> cases hr]
    rfl
  rcases c0 with _ | α
  · rw [above_undefined strict (some l) (hmiss (Or.inr (Or.inl rfl)))]
    rfl
  rcases c1 with _ | β
  · rw [above_undefined strict (some l) (hmiss (Or.inr (Or.inr rfl)))]
    rfl
  show _ = Binding.guardValue (Value.or (Value.not (Value.nonzero (some s))) (Value.lt (some β) z)) _
  by_cases hs : s = 0
  · subst hs
    rw [partialIntegral_zero fun x => by
      rw [hval α β (by simp) rfl rfl x]
      cases hcmp : compare strict (some l) (some x) with
      | none => cases strict <;> simp [compare, Value.lt, Value.le] at hcmp
      | some t => cases t <;> simp [Value.mask, scaleReal]]
    simp [Value.nonzero, Value.not, Value.or, Value.mask, Binding.guardValue]
  · rw [rate_above strict κ hv hE hP (fun t ht => by cases ht; exact hs) hm hk hz]
    simp [Value.nonzero, hs, Value.not, Value.or, Value.mask, scaleBy]

/-- Below a bound: `guard(0 < c₁, κ·exp(c₀ + c₁·b)/c₁)` under the scale. -/
theorem rate_below (strict : Bool) {b : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (κ : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hP : rateCheck P κ = true) (hS : scaleNonvanishing S) {k z : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) κ))
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) =
      Binding.guardValue (Value.lt z c1) (scaleBy S (Value.mul k
        (Value.mul (Value.inv c1) (Functions.expR.apply (Value.add c0 (Value.mul c1 b)))))) := by
  obtain ⟨hκ, hmiss, hval⟩ := rate_value hv hE hP
  have hK : k = some (κ : ℝ) := by rw [hk]; simp [Numeric.denote]
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  by_cases hu : S = some none ∨ c0 = none ∨ c1 = none
  · rw [below_undefined strict b (hmiss hu)]
    rcases hu with rfl | rfl | rfl
    · simp [scaleBy, Value.mul, Binding.guardValue]
    · have : Functions.expR.apply (Value.add (none : Option ℝ) (Value.mul c1 b)) = none := rfl
      rw [this, hK]
      cases Value.inv c1 <;> simp [Value.mul, hnone, Binding.guardValue]
    · rw [hZ]
      simp [Value.lt, Binding.guardValue]
  simp only [not_or] at hu
  obtain ⟨hS', h0, h1⟩ := hu
  obtain ⟨α, rfl⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨β, rfl⟩ := Option.ne_none_iff_exists'.1 h1
  have hg := hval α β hS' rfl rfl
  have hσ : scaleReal S ≠ 0 := by
    rcases S with _ | _ | s
    · simp [scaleReal]
    · exact absurd rfl hS'
    · exact hS s rfl
  rcases b with _ | u
  · rw [show partialIntegral volume (fun x => Value.mask (compare strict (some x) none) (v x)) =
        none from if_neg fun hd => by
          obtain ⟨r, hr⟩ := hd.1 0
          cases strict <;> cases hr]
    have : Functions.expR.apply (Value.add (some α) (Value.mul (some β) none)) = none := rfl
    rw [this, hK]
    cases Value.inv (some β) <;> simp [Value.mul, hnone, Binding.guardValue]
  have hcmp : ∀ x : ℝ, x < u → compare strict (some x) (some u) = some true := fun x hx => by
    cases strict <;> simp [compare, Value.lt, Value.le, hx, hx.le]
  by_cases hβ : 0 < β
  · obtain ⟨hi, hint⟩ := exp_linear_Iic α hβ u
    have hI : ∀ u' : ℝ, IntegrableOn (fun x : ℝ => scaleReal S * (κ * Real.exp (α + β * x)))
        (Iic u') volume := fun u' =>
      (((exp_linear_Iic α hβ u').1.const_mul _).const_mul _)
    rw [upper_integral strict (some u) ⟨fun _ => rfl⟩
      (UpperTerms.value hg hI (fun h => by cases h) fun u' hu' => by
        cases hu'
        rfl)]
    have hne : β ≠ 0 := hβ.ne'
    rw [integral_const_mul, integral_const_mul, hint, hK, hZ]
    rcases S with _ | _ | s
    · simp [Value.lt, hβ, Binding.guardValue, scaleBy, scaleReal, Value.mul, Value.add, Value.inv,
        hne, Function1.apply, Functions.expR]
    · exact absurd rfl hS'
    · simp [Value.lt, hβ, Binding.guardValue, scaleBy, scaleReal, Value.mul, Value.add, Value.inv,
        hne, Function1.apply, Functions.expR]
  · have hn : partialIntegral volume
        (fun x => Value.mask (compare strict (some x) (some u)) (v x)) = none := by
      apply if_neg
      rintro ⟨_, hint⟩
      have hon : IntegrableOn (fun x : ℝ => scaleReal S * κ * Real.exp (α + β * x)) (Iio u)
          volume := by
        refine (hint.integrableOn (s := Iio u)).congr_fun (fun x hx => ?_) measurableSet_Iio
        show (Value.mask (compare strict (some x) (some u)) (v x)).getD 0 = _
        rw [hcmp x hx, hg]
        show scaleReal S * (κ * Real.exp (α + β * x)) = _
        ring
      exact exp_linear_not_integrableOn_Iic α (not_lt.1 hβ) u (mul_ne_zero hσ hκ)
        (integrableOn_Iic_iff_integrableOn_Iio.2 hon)
    rw [hn, hZ]
    simp [Value.lt, hβ, Binding.guardValue]

/-- The same under a scale that may vanish. -/
theorem rate_below_masked (strict : Bool) {b : Option ℝ} {v : ℝ → Option ℝ} {c : Option ℝ}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (κ : ℚ)
    (hv : Bell v (some c) none P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hP : rateCheck P κ = true) {k z : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) κ))
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) =
      after [c, b, c0, c1] (Binding.guardValue
        (Value.or (Value.not (Value.nonzero c)) (Value.lt z c1))
        (Value.mask (Value.nonzero c) (Value.mul c (Value.mul k
          (Value.mul (Value.inv c1) (Functions.expR.apply (Value.add c0 (Value.mul c1 b)))))))) := by
  obtain ⟨_, hmiss, hval⟩ := rate_value hv hE hP
  rcases c with _ | s
  · rw [below_undefined strict b (hmiss (Or.inl rfl))]
    rfl
  rcases b with _ | u
  · rw [show partialIntegral volume (fun x => Value.mask (compare strict (some x) none) (v x)) =
        none from if_neg fun hd => by
          obtain ⟨r, hr⟩ := hd.1 0
          cases strict <;> cases hr]
    rfl
  rcases c0 with _ | α
  · rw [below_undefined strict (some u) (hmiss (Or.inr (Or.inl rfl)))]
    rfl
  rcases c1 with _ | β
  · rw [below_undefined strict (some u) (hmiss (Or.inr (Or.inr rfl)))]
    rfl
  show _ = Binding.guardValue (Value.or (Value.not (Value.nonzero (some s))) (Value.lt z (some β))) _
  by_cases hs : s = 0
  · subst hs
    rw [partialIntegral_zero fun x => by
      rw [hval α β (by simp) rfl rfl x]
      cases hcmp : compare strict (some x) (some u) with
      | none => cases strict <;> simp [compare, Value.lt, Value.le] at hcmp
      | some t => cases t <;> simp [Value.mask, scaleReal]]
    simp [Value.nonzero, Value.not, Value.or, Value.mask, Binding.guardValue]
  · rw [rate_below strict κ hv hE hP (fun t ht => by cases ht; exact hs) hk hz]
    simp [Value.nonzero, hs, Value.not, Value.or, Value.mask, scaleBy]

end QSym.Distribution.StepSource
