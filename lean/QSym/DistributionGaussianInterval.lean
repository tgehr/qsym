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

/-! A rate that does not mention the axis. Beyond a single bound a polynomial
times the exponential of a linear exponent is integrable exactly where its
rate has the sign of decay, so the observation stands under the guard of that
sign: where the rate has the other sign, or is zero, the integrand is defined
and not integrable. The antiderivative is the exponential times a polynomial
in the axis and in the inverse of the rate. Under a scale that may vanish the
integrand is zero where the scale is, whatever the rate. -/

/-- The rows of that polynomial in the powers of the inverse rate from the
first on, `P, -P', P'', …`: each is the opposite of the derivative of the one
before, and the derivative of the last vanishes. -/
def rateRowsCheck : List ℚ → List (List ℚ) → Bool
  | P, [] => polyZero P
  | P, r :: R =>
    polyZero (polyAdd r (polyScale (-1) P)) &&
      rateRowsCheck (polyScale (-1) (polyDerivative P)) R

/-- Coefficient lists with the same values have derivatives with the same
values. -/
private theorem polyDerivative_congr {p q : List ℚ} (h : ∀ x : ℝ, polyEval p x = polyEval q x)
    (x : ℝ) : polyEval (polyDerivative p) x = polyEval (polyDerivative q) x := by
  have hf : polyEval p = polyEval q := funext h
  exact (polyEval_hasDerivAt p x).unique (hf ▸ polyEval_hasDerivAt q x)

/-- The derivative of a polynomial in two values in the first. -/
theorem poly2Eval_hasDerivAt (K : List (List ℚ)) (h x : ℝ) :
    HasDerivAt (fun t : ℝ => poly2Eval K t h) (poly2Eval (K.map polyDerivative) x h) x := by
  induction K with
  | nil => simpa [poly2Eval] using hasDerivAt_const x (0 : ℝ)
  | cons p K ih =>
    simp only [poly2Eval, List.map_cons]
    exact (polyEval_hasDerivAt p x).add (ih.const_mul h)

/-- Those rows `B` satisfy `B + h·B' = P`. -/
theorem rateRows_identity (h : ℝ) :
    ∀ (R : List (List ℚ)) (P : List ℚ), rateRowsCheck P R = true → ∀ x : ℝ,
      poly2Eval R x h + h * poly2Eval (R.map polyDerivative) x h = polyEval P x := by
  intro R
  induction R with
  | nil =>
    intro P hP x
    simp only [rateRowsCheck] at hP
    simp [poly2Eval, polyEval_zero hP]
  | cons r R ih =>
    intro P hP x
    simp only [rateRowsCheck, Bool.and_eq_true] at hP
    obtain ⟨hr, hR⟩ := hP
    have hrP : ∀ y : ℝ, polyEval r y = polyEval P y := fun y => by
      have h0 := polyEval_zero hr y
      rw [polyEval_add, polyEval_scale] at h0
      push_cast at h0
      linarith
    have hd := polyDerivative_congr hrP x
    have hih := ih _ hR x
    rw [polyEval_scale] at hih
    push_cast at hih
    simp only [poly2Eval, List.map_cons]
    rw [hrP x, hd]
    linear_combination h * hih

/-- The checks of the table of an antiderivative: the polynomial is not zero,
the row without a power of the inverse rate is, and the others are those rows
for the polynomial times a sign. -/
def rateTableCheck (s : ℚ) (P : List ℚ) : List (List ℚ) → Bool
  | [] => false
  | z :: R => !polyZero P && polyZero z && rateRowsCheck (polyScale s P) R

theorem rateTable_nonzero {s : ℚ} {P : List ℚ} {K : List (List ℚ)}
    (hK : rateTableCheck s P K = true) : polyZero P = false := by
  rcases K with _ | ⟨z, R⟩
  · simp [rateTableCheck] at hK
  · simp only [rateTableCheck, Bool.and_eq_true, Bool.not_eq_true'] at hK
    exact hK.1.1

/-- The exponential times the table at the inverse rate is an antiderivative
of the sign times the polynomial times the exponential. -/
theorem rateTable_deriv {s : ℚ} {P : List ℚ} {K : List (List ℚ)}
    (hK : rateTableCheck s P K = true) (α : ℝ) {β : ℝ} (hβ : β ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (α + β * t) * poly2Eval K t β⁻¹)
      (s * (polyEval P x * Real.exp (α + β * x))) x := by
  rcases K with _ | ⟨z, R⟩
  · simp [rateTableCheck] at hK
  simp only [rateTableCheck, Bool.and_eq_true, Bool.not_eq_true'] at hK
  obtain ⟨⟨_, hz⟩, hR⟩ := hK
  have hid := rateRows_identity β⁻¹ R _ hR x
  rw [polyEval_scale] at hid
  have hz0 : ∀ y : ℝ, polyEval z y = 0 := fun y => polyEval_zero hz y
  have hzd : polyEval (polyDerivative z) x = 0 := by
    have h0 := polyDerivative_congr (p := z) (q := []) (fun y => by rw [hz0]; rfl) x
    simpa [polyDerivative, polyEval] using h0
  have he : HasDerivAt (fun t : ℝ => Real.exp (α + β * t)) (Real.exp (α + β * x) * (β * 1)) x :=
    (((hasDerivAt_id x).const_mul β).const_add α).exp
  refine (he.mul (poly2Eval_hasDerivAt (z :: R) β⁻¹ x)).congr_deriv ?_
  simp only [poly2Eval, List.map_cons, hz0, hzd]
  have hβi : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
  linear_combination Real.exp (α + β * x) * hid +
    Real.exp (α + β * x) * poly2Eval R x β⁻¹ * hβi

/-- With a negative rate that antiderivative vanishes at infinity. -/
theorem poly2_exp_tendsto_atTop (K : List (List ℚ)) (h α : ℝ) {β : ℝ} (hβ : β < 0) :
    Tendsto (fun t : ℝ => Real.exp (α + β * t) * poly2Eval K t h) atTop (𝓝 0) := by
  induction K with
  | nil => simp [poly2Eval]
  | cons p K ih =>
    have h3 := ((expPolynomial_tendsto p hβ).const_mul (Real.exp α)).add (ih.const_mul h)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun t => ?_
    simp only [poly2Eval]
    rw [Real.exp_add]
    ring

/-- With a positive rate at minus infinity. -/
theorem poly2_exp_tendsto_atBot (K : List (List ℚ)) (h α : ℝ) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun t : ℝ => Real.exp (α + β * t) * poly2Eval K t h) atBot (𝓝 0) := by
  induction K with
  | nil => simp [poly2Eval]
  | cons p K ih =>
    have h3 := ((expPolynomial_tendsto_atBot p hβ).const_mul (Real.exp α)).add (ih.const_mul h)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun t => ?_
    simp only [poly2Eval]
    rw [Real.exp_add]
    ring

theorem poly_exp_linear_integrableOn_Ioi (P : List ℚ) (α : ℝ) {β : ℝ} (hβ : β < 0) (l : ℝ) :
    IntegrableOn (fun x : ℝ => polyEval P x * Real.exp (α + β * x)) (Ioi l) volume := by
  have hc : Continuous fun x : ℝ => polyEval P x * Real.exp (β * x) :=
    (polyEval_continuous P).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hi : IntegrableOn (fun x : ℝ => polyEval P x * Real.exp (β * x)) (Ioi l) volume :=
    integrable_of_isBigO_exp_neg (show (0 : ℝ) < -β / 2 by linarith) hc.continuousOn
      (expPolynomial_isBigO P hβ)
  have he : (fun x : ℝ => polyEval P x * Real.exp (α + β * x)) =
      fun x => Real.exp α * (polyEval P x * Real.exp (β * x)) := by
    funext x
    rw [Real.exp_add]
    ring
  rw [he]
  exact hi.const_mul _

theorem poly_exp_linear_integrableOn_Iic (P : List ℚ) (α : ℝ) {β : ℝ} (hβ : 0 < β) (u : ℝ) :
    IntegrableOn (fun x : ℝ => polyEval P x * Real.exp (α + β * x)) (Iic u) volume := by
  have hc : Continuous fun x : ℝ => polyEval P x * Real.exp (β * x) :=
    (polyEval_continuous P).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hi : IntegrableOn (fun x : ℝ => polyEval P x * Real.exp (β * x)) (Iic u) volume :=
    (hc.locallyIntegrable.locallyIntegrableOn _).integrableOn_of_isBigO_atBot
      (expPolynomial_isBigO_atBot P hβ)
      ⟨Iic 0, Iic_mem_atBot 0, integrableOn_exp_mul_Iic (half_pos hβ) 0⟩
  have he : (fun x : ℝ => polyEval P x * Real.exp (α + β * x)) =
      fun x => Real.exp α * (polyEval P x * Real.exp (β * x)) := by
    funext x
    rw [Real.exp_add]
    ring
  rw [he]
  exact hi.const_mul _

/-- The integral above a bound, with a negative rate. -/
theorem rateTable_integral_Ioi {P : List ℚ} {K : List (List ℚ)}
    (hK : rateTableCheck (-1) P K = true) (α : ℝ) {β : ℝ} (hβ : β < 0) (l : ℝ) :
    ∫ x in Ioi l, polyEval P x * Real.exp (α + β * x) =
      Real.exp (α + β * l) * poly2Eval K l β⁻¹ := by
  have hD : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -(Real.exp (α + β * t) * poly2Eval K t β⁻¹))
      (polyEval P x * Real.exp (α + β * x)) x := fun x => by
    refine (rateTable_deriv hK α hβ.ne x).neg.congr_deriv ?_
    push_cast
    ring
  have hT : Tendsto (fun t : ℝ => -(Real.exp (α + β * t) * poly2Eval K t β⁻¹)) atTop (𝓝 0) := by
    simpa using (poly2_exp_tendsto_atTop K β⁻¹ α hβ).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hD x)
    (poly_exp_linear_integrableOn_Ioi P α hβ l) hT]
  ring

/-- Below a bound, with a positive rate. -/
theorem rateTable_integral_Iic {P : List ℚ} {K : List (List ℚ)}
    (hK : rateTableCheck 1 P K = true) (α : ℝ) {β : ℝ} (hβ : 0 < β) (u : ℝ) :
    ∫ x in Iic u, polyEval P x * Real.exp (α + β * x) =
      Real.exp (α + β * u) * poly2Eval K u β⁻¹ := by
  have hD : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Real.exp (α + β * t) * poly2Eval K t β⁻¹)
      (polyEval P x * Real.exp (α + β * x)) x := fun x => by
    refine (rateTable_deriv hK α hβ.ne' x).congr_deriv ?_
    push_cast
    ring
  rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hD x)
    (poly_exp_linear_integrableOn_Iic P α hβ u) (poly2_exp_tendsto_atBot K β⁻¹ α hβ)]
  ring

/-- With a rate that is not negative a polynomial that is not zero times the
exponential is not integrable above a bound: far enough the polynomial stays
away from zero and the exponential above its value. -/
theorem poly_exp_linear_not_integrableOn_Ioi {P : List ℚ} (hP : polyZero P = false) (α : ℝ)
    {β : ℝ} (hβ : 0 ≤ β) (l : ℝ) {k : ℝ} (hk : k ≠ 0) :
    ¬ IntegrableOn (fun x : ℝ => k * (polyEval P x * Real.exp (α + β * x))) (Ioi l) volume := by
  intro hi
  obtain ⟨δ, hδ, hev⟩ := eval_eventually_away (QSym.Limit.toPoly_ne_zero hP)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  have hs : IntegrableOn (fun _ : ℝ => |k| * (δ * Real.exp (α + β * max M l))) (Ioi (max M l))
      volume := by
    refine Integrable.mono' (hi.mono_set (Ioi_subset_Ioi (le_max_right _ _))).norm
      aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : max M l < x := hx
    have h1 := hM x (le_trans (le_max_left _ _) hx'.le)
    rw [QSym.Limit.eval_toPoly] at h1
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg k) (mul_nonneg hδ.le (Real.exp_pos _).le)),
      norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1
      (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hβ (sub_nonneg.2 hx'.le)]))
      (Real.exp_pos _).le (abs_nonneg _)) (abs_nonneg k)
  rw [integrableOn_const] at hs
  rcases hs with h0 | hfin
  · exact (mul_pos (abs_pos.2 hk) (mul_pos hδ (Real.exp_pos _))).ne' h0
  · rw [Real.volume_Ioi] at hfin
    exact lt_irrefl _ hfin

/-- With a rate that is not positive, below one. -/
theorem poly_exp_linear_not_integrableOn_Iic {P : List ℚ} (hP : polyZero P = false) (α : ℝ)
    {β : ℝ} (hβ : β ≤ 0) (u : ℝ) {k : ℝ} (hk : k ≠ 0) :
    ¬ IntegrableOn (fun x : ℝ => k * (polyEval P x * Real.exp (α + β * x))) (Iic u) volume := by
  intro hi
  have hq : (QSym.Limit.toPoly P).comp (-Polynomial.X) ≠ 0 := fun h0 =>
    QSym.Limit.toPoly_ne_zero hP (by
      have h1 := congrArg (fun r : Polynomial ℝ => r.comp (-Polynomial.X)) h0
      simpa [Polynomial.comp_assoc] using h1)
  obtain ⟨δ, hδ, hev⟩ := eval_eventually_away hq
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  have hs : IntegrableOn (fun _ : ℝ => |k| * (δ * Real.exp (α + β * min (-M) u)))
      (Iic (min (-M) u)) volume := by
    refine Integrable.mono' (hi.mono_set (Iic_subset_Iic.2 (min_le_right _ _))).norm
      aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : x ≤ min (-M) u := hx
    have hxM : M ≤ -x := by linarith [le_trans hx' (min_le_left _ _)]
    have h1 := hM (-x) hxM
    rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, neg_neg,
      QSym.Limit.eval_toPoly] at h1
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg k) (mul_nonneg hδ.le (Real.exp_pos _).le)),
      norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1
      (Real.exp_le_exp.2 (by nlinarith [mul_nonneg_of_nonpos_of_nonpos hβ (sub_nonpos.2 hx')]))
      (Real.exp_pos _).le (abs_nonneg _)) (abs_nonneg k)
  rw [integrableOn_const] at hs
  rcases hs with h0 | hfin
  · exact (mul_pos (abs_pos.2 hk) (mul_pos hδ (Real.exp_pos _))).ne' h0
  · rw [Real.volume_Iic] at hfin
    exact lt_irrefl _ hfin

/-- The polynomial in front is a constant other than zero. -/
def rateCheck (P : List ℚ) (κ : ℚ) : Bool :=
  polyZero (polyAdd P (polyScale (-1) [κ])) && decide (κ ≠ 0)

/-- The value below the mask: undefined everywhere where a coefficient or the
scale is, and the polynomial times the exponential under the scale otherwise. -/
private theorem rate_value {v : ℝ → Option ℝ} {S : Option (Option ℝ)} {P : List ℚ}
    {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (hv : Bell v S none P (some E))
    (hE : Quadratic E (some c0) (some c1) none) :
    ((S = some none ∨ c0 = none ∨ c1 = none) → ∀ x, v x = none) ∧
      ∀ α β : ℝ, S ≠ some none → c0 = some α → c1 = some β →
        ∀ x, v x = some (scaleReal S * (polyEval P x * Real.exp (α + β * x))) := by
  have hvx : ∀ x, v x = scaleBy S (Value.mul (some (polyEval P x)) (Functions.expR.apply (E x))) :=
    fun x => hv.plain x
  refine ⟨fun hm x => ?_, fun α β hS h0 h1 x => ?_⟩
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
    rw [hvx, hEx]
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

/-- The sum of the monomials of a table at a bound and at the inverse of a
rate that is not zero. -/
private theorem rate_sum {a c1 k : Option ℝ} {K : List (List ℚ)} {ms : List (Option ℝ)}
    (hm : MomentTerms a (curvatureCoefs (Value.inv c1) K 0) K ms) (hk : Sums ms k) (l : ℝ)
    {β : ℝ} (hβ : β ≠ 0) (ha : a = some l) (hc : c1 = some β) :
    k = some (poly2Eval K l β⁻¹) := by
  subst ha hc
  have hi : Value.inv (some β) = some β⁻¹ := by simp [Value.inv, hβ]
  rw [hi] at hm
  rw [hk.value, hm.value l rfl (curvatureCoefs_defined _ K 0), momentValue_curvature]
  simp

/-- Above a bound: `guard(c₁ < 0, k·exp(c₀ + c₁·a))` under the scale, where
`k` is the table at the bound and at the inverse of the rate. -/
theorem rate_above (strict : Bool) {a : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (K : List (List ℚ))
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hK : rateTableCheck (-1) P K = true) (hS : scaleNonvanishing S) {k z : Option ℝ}
    {ms : List (Option ℝ)} (hm : MomentTerms a (curvatureCoefs (Value.inv c1) K 0) K ms)
    (hk : Sums ms k) (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) =
      Binding.guardValue (Value.lt c1 z) (scaleBy S (Value.mul k
        (Functions.expR.apply (Value.add c0 (Value.mul c1 a))))) := by
  obtain ⟨hmiss, hval⟩ := rate_value hv hE
  have hP := rateTable_nonzero hK
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  have hmul : ∀ X : Option ℝ, X = none → Binding.guardValue (Value.lt c1 z)
      (scaleBy S (Value.mul k X)) = none := fun X hX => by
    subst hX
    cases k <;> simp [Value.mul, hnone, Binding.guardValue]
  by_cases hu : S = some none ∨ c0 = none ∨ c1 = none
  · rw [above_undefined strict a (hmiss hu)]
    rcases hu with rfl | rfl | rfl
    · simp [scaleBy, Value.mul, Binding.guardValue]
    · exact (hmul _ rfl).symm
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
    exact (hmul _ rfl).symm
  have hcmp : ∀ x : ℝ, l < x → compare strict (some l) (some x) = some true := fun x hx => by
    cases strict <;> simp [compare, Value.lt, Value.le, hx, hx.le]
  by_cases hβ : β < 0
  · have hI : ∀ l' : ℝ, IntegrableOn
        (fun x : ℝ => scaleReal S * (polyEval P x * Real.exp (α + β * x))) (Ioi l') volume :=
      fun l' => (poly_exp_linear_integrableOn_Ioi P α hβ l').const_mul _
    rw [halfline_integral strict (some l) (some (Numeric.denote (s := .real) (-1 : ℚ))) rfl
      ⟨fun _ => rfl⟩ (HalfLineTerms.value hg hI (fun h => by cases h) fun l' hl => by
        cases hl
        rfl)]
    rw [integral_const_mul, rateTable_integral_Ioi hK α hβ l, rate_sum hm hk l hβ.ne rfl rfl, hZ]
    rcases S with _ | _ | s
    · simp only [Value.lt, hβ, Binding.guardValue, scaleBy, scaleReal, Value.mul, Value.add,
        Function1.apply, Functions.expR]
      simp [hβ, mul_comm]
    · exact absurd rfl hS'
    · simp only [Value.lt, hβ, Binding.guardValue, scaleBy, scaleReal, Value.mul, Value.add,
        Function1.apply, Functions.expR]
      simp [hβ, mul_comm]
  · have hn : partialIntegral volume
        (fun x => Value.mask (compare strict (some l) (some x)) (v x)) = none := by
      apply if_neg
      rintro ⟨_, hint⟩
      have hon : IntegrableOn
          (fun x : ℝ => scaleReal S * (polyEval P x * Real.exp (α + β * x))) (Ioi l) volume := by
        refine (hint.integrableOn (s := Ioi l)).congr_fun (fun x hx => ?_) measurableSet_Ioi
        show (Value.mask (compare strict (some l) (some x)) (v x)).getD 0 = _
        rw [hcmp x hx, hg]
        rfl
      exact poly_exp_linear_not_integrableOn_Ioi hP α (not_lt.1 hβ) l hσ hon
    rw [hn, hZ]
    simp [Value.lt, hβ, Binding.guardValue]

/-- The same under a scale that may vanish: zero where the scale is, under
its mask and the guard of that or the sign of the rate, after the scale, the
bound and the coefficients of the exponent. -/
theorem rate_above_masked (strict : Bool) {a : Option ℝ} {v : ℝ → Option ℝ} {c : Option ℝ}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (K : List (List ℚ))
    (hv : Bell v (some c) none P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hK : rateTableCheck (-1) P K = true) {k z : Option ℝ} {ms : List (Option ℝ)}
    (hm : MomentTerms a (curvatureCoefs (Value.inv c1) K 0) K ms) (hk : Sums ms k)
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) =
      after [c, a, c0, c1] (Binding.guardValue
        (Value.or (Value.not (Value.nonzero c)) (Value.lt c1 z))
        (Value.mask (Value.nonzero c) (Value.mul c (Value.mul k
          (Functions.expR.apply (Value.add c0 (Value.mul c1 a))))))) := by
  obtain ⟨hmiss, hval⟩ := rate_value hv hE
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
  · rw [rate_above strict K hv hE hK (fun t ht => by cases ht; exact hs) hm hk hz]
    simp [Value.nonzero, hs, Value.not, Value.or, Value.mask, scaleBy]

/-- Below a bound: `guard(0 < c₁, k·exp(c₀ + c₁·b))` under the scale. -/
theorem rate_below (strict : Bool) {b : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (K : List (List ℚ))
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hK : rateTableCheck 1 P K = true) (hS : scaleNonvanishing S) {k z : Option ℝ}
    {ms : List (Option ℝ)} (hm : MomentTerms b (curvatureCoefs (Value.inv c1) K 0) K ms)
    (hk : Sums ms k) (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) =
      Binding.guardValue (Value.lt z c1) (scaleBy S (Value.mul k
        (Functions.expR.apply (Value.add c0 (Value.mul c1 b))))) := by
  obtain ⟨hmiss, hval⟩ := rate_value hv hE
  have hP := rateTable_nonzero hK
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  have hmul : ∀ X : Option ℝ, X = none → Binding.guardValue (Value.lt z c1)
      (scaleBy S (Value.mul k X)) = none := fun X hX => by
    subst hX
    cases k <;> simp [Value.mul, hnone, Binding.guardValue]
  by_cases hu : S = some none ∨ c0 = none ∨ c1 = none
  · rw [below_undefined strict b (hmiss hu)]
    rcases hu with rfl | rfl | rfl
    · simp [scaleBy, Value.mul, Binding.guardValue]
    · exact (hmul _ rfl).symm
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
    exact (hmul _ rfl).symm
  have hcmp : ∀ x : ℝ, x < u → compare strict (some x) (some u) = some true := fun x hx => by
    cases strict <;> simp [compare, Value.lt, Value.le, hx, hx.le]
  by_cases hβ : 0 < β
  · have hI : ∀ u' : ℝ, IntegrableOn
        (fun x : ℝ => scaleReal S * (polyEval P x * Real.exp (α + β * x))) (Iic u') volume :=
      fun u' => (poly_exp_linear_integrableOn_Iic P α hβ u').const_mul _
    rw [upper_integral strict (some u) ⟨fun _ => rfl⟩
      (UpperTerms.value hg hI (fun h => by cases h) fun u' hu' => by
        cases hu'
        rfl)]
    rw [integral_const_mul, rateTable_integral_Iic hK α hβ u, rate_sum hm hk u hβ.ne' rfl rfl, hZ]
    rcases S with _ | _ | s
    · simp only [Value.lt, hβ, Binding.guardValue, scaleBy, scaleReal, Value.mul, Value.add,
        Function1.apply, Functions.expR]
      simp [hβ, mul_comm]
    · exact absurd rfl hS'
    · simp only [Value.lt, hβ, Binding.guardValue, scaleBy, scaleReal, Value.mul, Value.add,
        Function1.apply, Functions.expR]
      simp [hβ, mul_comm]
  · have hn : partialIntegral volume
        (fun x => Value.mask (compare strict (some x) (some u)) (v x)) = none := by
      apply if_neg
      rintro ⟨_, hint⟩
      have hon : IntegrableOn
          (fun x : ℝ => scaleReal S * (polyEval P x * Real.exp (α + β * x))) (Iio u) volume := by
        refine (hint.integrableOn (s := Iio u)).congr_fun (fun x hx => ?_) measurableSet_Iio
        show (Value.mask (compare strict (some x) (some u)) (v x)).getD 0 = _
        rw [hcmp x hx, hg]
        rfl
      exact poly_exp_linear_not_integrableOn_Iic hP α (not_lt.1 hβ) u hσ
        (integrableOn_Iic_iff_integrableOn_Iio.2 hon)
    rw [hn, hZ]
    simp [Value.lt, hβ, Binding.guardValue]

/-- The same under a scale that may vanish. -/
theorem rate_below_masked (strict : Bool) {b : Option ℝ} {v : ℝ → Option ℝ} {c : Option ℝ}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (K : List (List ℚ))
    (hv : Bell v (some c) none P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hK : rateTableCheck 1 P K = true) {k z : Option ℝ} {ms : List (Option ℝ)}
    (hm : MomentTerms b (curvatureCoefs (Value.inv c1) K 0) K ms) (hk : Sums ms k)
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) =
      after [c, b, c0, c1] (Binding.guardValue
        (Value.or (Value.not (Value.nonzero c)) (Value.lt z c1))
        (Value.mask (Value.nonzero c) (Value.mul c (Value.mul k
          (Functions.expR.apply (Value.add c0 (Value.mul c1 b))))))) := by
  obtain ⟨hmiss, hval⟩ := rate_value hv hE
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
  · rw [rate_below strict K hv hE hK (fun t ht => by cases ht; exact hs) hm hk hz]
    simp [Value.nonzero, hs, Value.not, Value.or, Value.mask, scaleBy]

/-! Between two bounds a polynomial times the exponential of a linear exponent
is integrable whatever the rate. Where the rate is not zero the integral is
the difference of the antiderivative above at the bounds; where it is zero the
exponential is that of the constant, in front of the difference of an
antiderivative of the polynomial. The two stand under the masks of that test:
the first mentions the inverse of the rate, and its mask hides it where the
rate is zero. -/

/-- The polynomial is the derivative of the other. -/
def flatCheck (P Q : List ℚ) : Bool :=
  polyZero (polyAdd (polyDerivative Q) (polyScale (-1) P))

theorem flat_deriv {P Q : List ℚ} (h : flatCheck P Q = true) (x : ℝ) :
    HasDerivAt (fun t : ℝ => polyEval Q t) (polyEval P x) x := by
  have h0 := polyEval_zero h x
  rw [polyEval_add, polyEval_scale] at h0
  push_cast at h0
  have hd : polyEval (polyDerivative Q) x = polyEval P x := by linarith
  rw [← hd]
  exact polyEval_hasDerivAt Q x

/-- The sum of the monomials of a polynomial at a point. -/
private theorem flat_sum {c p : Option ℝ} {Q : List ℚ} {qs : List (Option ℝ)}
    (hq : RowTerms none c Q 0 [] qs) (hp : Sums qs p) (t : ℝ) (hc : c = some t) :
    p = some (polyEval Q t) := by
  rw [hp.value, hq.value t hc (by simp)]
  simp [factorReal, listSum, Value.add]

/-- Between two bounds, under the scale:
`[c₁≠0]·(k_b·exp(c₀+c₁·b) - k_a·exp(c₀+c₁·a)) + [c₁=0]·(exp(c₀)·(p_b - p_a))`,
where `k` is the table of the antiderivative at a bound and at the inverse of
the rate, and `p` an antiderivative of the polynomial at a bound. -/
theorem IntervalTerms.rate {a b m : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (K : List (List ℚ)) (Q : List ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hK : rateTableCheck 1 P K = true) (hQ : flatCheck P Q = true)
    {kb ka pb pa : Option ℝ} {msb msa qsb qsa : List (Option ℝ)}
    (hmb : MomentTerms b (curvatureCoefs (Value.inv c1) K 0) K msb) (hkb : Sums msb kb)
    (hma : MomentTerms a (curvatureCoefs (Value.inv c1) K 0) K msa) (hka : Sums msa ka)
    (hqb : RowTerms none b Q 0 [] qsb) (hpb : Sums qsb pb)
    (hqa : RowTerms none a Q 0 [] qsa) (hpa : Sums qsa pa) :
    IntervalTerms a b m v (scaleBy S (Value.add
      (Value.mask (Value.nonzero c1) (Value.add
        (Value.mul kb (Functions.expR.apply (Value.add c0 (Value.mul c1 b))))
        (Value.mul m (Value.mul ka (Functions.expR.apply (Value.add c0 (Value.mul c1 a)))))))
      (Value.mask (Value.not (Value.nonzero c1))
        (Value.mul (Functions.expR.apply c0) (Value.add pb (Value.mul m pa)))))) := by
  obtain ⟨hmiss, hval⟩ := rate_value hv hE
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  by_cases hu : S = some none ∨ c0 = none ∨ c1 = none
  · have hout : scaleBy S (Value.add
        (Value.mask (Value.nonzero c1) (Value.add
          (Value.mul kb (Functions.expR.apply (Value.add c0 (Value.mul c1 b))))
          (Value.mul m (Value.mul ka (Functions.expR.apply (Value.add c0 (Value.mul c1 a)))))))
        (Value.mask (Value.not (Value.nonzero c1))
          (Value.mul (Functions.expR.apply c0) (Value.add pb (Value.mul m pa))))) = none := by
      rcases hu with rfl | rfl | rfl
      · rfl
      · have h1 : Value.add (Value.mul kb (Functions.expR.apply (Value.add none (Value.mul c1 b))))
            (Value.mul m (Value.mul ka (Functions.expR.apply (Value.add none (Value.mul c1 a))))) =
            none := by
          cases kb <;> rfl
        have h2 : Value.mul (Functions.expR.apply none) (Value.add pb (Value.mul m pa)) = none :=
          rfl
        rw [h1, h2]
        rcases c1 with _ | β
        · exact hnone
        · by_cases hβ : β = 0 <;>
            simp [Value.nonzero, Value.not, Value.mask, Value.add, hβ, hnone]
      · exact hnone
    rw [hout]
    exact IntervalTerms.undefined (hmiss hu)
  simp only [not_or] at hu
  obtain ⟨hS', h0, h1⟩ := hu
  obtain ⟨α, rfl⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨β, rfl⟩ := Option.ne_none_iff_exists'.1 h1
  have hg := hval α β hS' rfl rfl
  have hcP : Continuous fun x : ℝ => polyEval P x * Real.exp (α + β * x) :=
    (polyEval_continuous P).mul (Real.continuous_exp.comp (by fun_prop))
  refine IntervalTerms.value hg (continuous_const.mul hcP) fun l u ha hb hm => ?_
  subst ha hb hm
  rw [intervalIntegral.integral_const_mul]
  by_cases hβ : β = 0
  · subst hβ
    have hI : ∫ x in l..u, polyEval P x * Real.exp (α + 0 * x) =
        Real.exp α * polyEval Q u - Real.exp α * polyEval Q l := by
      have hd : ∀ x ∈ Set.uIcc l u, HasDerivAt (fun t : ℝ => Real.exp α * polyEval Q t)
          (polyEval P x * Real.exp (α + 0 * x)) x := fun x _ => by
        refine ((flat_deriv hQ x).const_mul (Real.exp α)).congr_deriv ?_
        rw [zero_mul, add_zero]
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcP.intervalIntegrable _ _)]
    rw [hI, flat_sum hqb hpb u rfl, flat_sum hqa hpa l rfl]
    rcases S with _ | _ | s
    · simp [scaleBy, scaleReal, Value.nonzero, Value.not, Value.mask, Value.add, Value.mul,
        Function1.apply, Functions.expR]
      ring
    · exact absurd rfl hS'
    · simp [scaleBy, scaleReal, Value.nonzero, Value.not, Value.mask, Value.add, Value.mul,
        Function1.apply, Functions.expR]
      left
      ring
  · have hI : ∫ x in l..u, polyEval P x * Real.exp (α + β * x) =
        Real.exp (α + β * u) * poly2Eval K u β⁻¹ - Real.exp (α + β * l) * poly2Eval K l β⁻¹ := by
      have hd : ∀ x ∈ Set.uIcc l u,
          HasDerivAt (fun t : ℝ => Real.exp (α + β * t) * poly2Eval K t β⁻¹)
            (polyEval P x * Real.exp (α + β * x)) x := fun x _ => by
        refine (rateTable_deriv hK α hβ x).congr_deriv ?_
        push_cast
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcP.intervalIntegrable _ _)]
    rw [hI, rate_sum hmb hkb u hβ rfl rfl, rate_sum hma hka l hβ rfl rfl]
    rcases S with _ | _ | s
    · simp [scaleBy, scaleReal, Value.nonzero, Value.not, Value.mask, Value.add, Value.mul,
        Function1.apply, Functions.expR, hβ]
      ring
    · exact absurd rfl hS'
    · simp [scaleBy, scaleReal, Value.nonzero, Value.not, Value.mask, Value.add, Value.mul,
        Function1.apply, Functions.expR, hβ]
      left
      ring

/-! The same under a polynomial whose coefficients do not mention the axis: the
integral is linear in them. Coefficient `j` meets the table and the
antiderivative of `xʲ` times the rational polynomial. -/

/-- Table `j` is that of `xʲ·P`, and it has a row that is not zero. -/
def rateTablesCheck : List ℚ → List (List (List ℚ)) → Bool
  | _, [] => true
  | P, K :: Ks => rateTableCheck 1 P K && !poly2Zero K && rateTablesCheck (0 :: P) Ks

/-- Polynomial `j` is an antiderivative of `xʲ·P`. -/
def flatsCheck : List ℚ → List (List ℚ) → Bool
  | _, [] => true
  | P, Q :: Qs => flatCheck P Q && flatsCheck (0 :: P) Qs

theorem rateTables_nonzero :
    ∀ (Ks : List (List (List ℚ))) (P : List ℚ), rateTablesCheck P Ks = true →
      ∀ K ∈ Ks, poly2Zero K = false := by
  intro Ks
  induction Ks with
  | nil => intro P _ K hK; simp at hK
  | cons K Ks ih =>
    intro P h K' hK'
    simp only [rateTablesCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases List.mem_cons.1 hK' with rfl | hm
    · exact h.1.2
    · exact ih (0 :: P) h.2 K' hm

/-- The exponential times the tables under their coefficients is an
antiderivative of the polynomial of the coefficients times the rational one
times the exponential. -/
theorem rateTables_deriv (α : ℝ) {β : ℝ} (hβ : β ≠ 0) (x : ℝ) :
    ∀ (cs : List (Option (Option ℝ))) (Ks : List (List (List ℚ))) (P : List ℚ),
      cs.length = Ks.length → rateTablesCheck P Ks = true →
      HasDerivAt (fun t : ℝ => Real.exp (α + β * t) * momentValue2 t β⁻¹ cs Ks)
        (realEval cs x * polyEval P x * Real.exp (α + β * x)) x := by
  intro cs
  induction cs with
  | nil =>
    intro Ks P hl _
    cases Ks with
    | nil => simpa [momentValue2, realEval] using hasDerivAt_const x (0 : ℝ)
    | cons K Ks => simp at hl
  | cons c cs ih =>
    intro Ks P hl hK
    cases Ks with
    | nil => simp at hl
    | cons K Ks =>
      simp only [rateTablesCheck, Bool.and_eq_true] at hK
      have h1 := (rateTable_deriv hK.1.1 α hβ x).const_mul (coefReal c)
      have h2 := ih Ks (0 :: P) (by simpa using hl) hK.2
      have hf : (fun t : ℝ => Real.exp (α + β * t) * momentValue2 t β⁻¹ (c :: cs) (K :: Ks)) =
          fun t => coefReal c * (Real.exp (α + β * t) * poly2Eval K t β⁻¹) +
            Real.exp (α + β * t) * momentValue2 t β⁻¹ cs Ks := by
        funext t
        simp only [momentValue2]
        ring
      rw [hf]
      refine (h1.add h2).congr_deriv ?_
      simp only [realEval, polyEval]
      push_cast
      ring

/-- The antiderivatives under their coefficients. -/
theorem flats_deriv (x : ℝ) :
    ∀ (cs : List (Option (Option ℝ))) (Qs : List (List ℚ)) (P : List ℚ),
      cs.length = Qs.length → flatsCheck P Qs = true →
      HasDerivAt (fun t : ℝ => momentValue t cs Qs) (realEval cs x * polyEval P x) x := by
  intro cs
  induction cs with
  | nil =>
    intro Qs P hl _
    cases Qs with
    | nil => simpa [momentValue, realEval] using hasDerivAt_const x (0 : ℝ)
    | cons Q Qs => simp at hl
  | cons c cs ih =>
    intro Qs P hl hQ
    cases Qs with
    | nil => simp at hl
    | cons Q Qs =>
      simp only [flatsCheck, Bool.and_eq_true] at hQ
      have h1 := (flat_deriv hQ.1 x).const_mul (coefReal c)
      have h2 := ih Qs (0 :: P) (by simpa using hl) hQ.2
      refine (h1.add h2).congr_deriv ?_
      simp only [realEval, polyEval]
      push_cast
      ring

/-- The value: undefined everywhere where the scale, a coefficient or the
exponent is, and the polynomials times the exponential under the scale
otherwise. -/
private theorem rateTerms_value {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {cs : List (Option (Option ℝ))} {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ}
    (hv : Bell v S (some cs) P (some E)) (hE : Quadratic E (some c0) (some c1) none) :
    ((S = some none ∨ some none ∈ cs ∨ c0 = none ∨ c1 = none) → ∀ x, v x = none) ∧
      ∀ α β : ℝ, S ≠ some none → some none ∉ cs → c0 = some α → c1 = some β →
        ∀ x, v x = some (scaleReal S *
          (realEval cs x * polyEval P x * Real.exp (α + β * x))) := by
  have hvx : ∀ x, v x = scaleBy S (Value.mul (Value.mul (symEval cs x) (some (polyEval P x)))
      (Functions.expR.apply (E x))) := fun x => hv.equation x
  have hnone : ∀ X : Option ℝ, scaleBy S (Value.mul X none) = none := fun X => by
    rcases S with _ | _ | s <;> cases X <;> rfl
  refine ⟨fun hm x => ?_, fun α β hS hd h0 h1 x => ?_⟩
  · rw [hvx]
    rcases hm with rfl | hd | rfl | rfl
    · rfl
    · rw [(symEval_none_iff cs x).2 hd]
      rcases S with _ | _ | s <;> rfl
    · have : E x = none := by rw [hE.equation]; rfl
      rw [this]
      exact hnone _
    · have : E x = none := by rw [hE.equation]; cases c0 <;> rfl
      rw [this]
      exact hnone _
  · subst h0 h1
    have hEx : E x = some (α + β * x) := by
      rw [hE.equation]
      simp [coefValue, Value.add, Value.mul]
    rw [hvx, hEx, symEval_real hd]
    rcases S with _ | _ | s
    · simp [scaleBy, scaleReal, Value.mul, Function1.apply, Functions.expR]
    · exact absurd rfl hS
    · simp [scaleBy, scaleReal, Value.mul, Function1.apply, Functions.expR]

/-- Between two bounds, under the scale, with `k` the tables under their
coefficients at a bound and at the inverse of the rate, and `p` the
antiderivatives under their coefficients at a bound:
`[c₁≠0]·(k_b·exp(c₀+c₁·b) - k_a·exp(c₀+c₁·a)) + [c₁=0]·(exp(c₀)·(p_b - p_a))`. -/
theorem IntervalTerms.rateTerms {a b m : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {cs : List (Option (Option ℝ))} {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option ℝ}
    (Ks : List (List (List ℚ))) (Qs : List (List ℚ))
    (hv : Bell v S (some cs) P (some E)) (hE : Quadratic E (some c0) (some c1) none)
    (hK : rateTablesCheck P Ks = true) (hQ : flatsCheck P Qs = true)
    (hl : cs.length = Ks.length)
    {kb ka pb pa : Option ℝ} {msb msa qsb qsa : List (Option ℝ)}
    (hmb : MomentTerms b (momentCoefs (Value.inv c1) cs Ks) Ks.flatten msb) (hkb : Sums msb kb)
    (hma : MomentTerms a (momentCoefs (Value.inv c1) cs Ks) Ks.flatten msa) (hka : Sums msa ka)
    (hqb : MomentTerms b cs Qs qsb) (hpb : Sums qsb pb)
    (hqa : MomentTerms a cs Qs qsa) (hpa : Sums qsa pa) :
    IntervalTerms a b m v (scaleBy S (Value.add
      (Value.mask (Value.nonzero c1) (Value.add
        (Value.mul kb (Functions.expR.apply (Value.add c0 (Value.mul c1 b))))
        (Value.mul m (Value.mul ka (Functions.expR.apply (Value.add c0 (Value.mul c1 a)))))))
      (Value.mask (Value.not (Value.nonzero c1))
        (Value.mul (Functions.expR.apply c0) (Value.add pb (Value.mul m pa)))))) := by
  obtain ⟨hmiss, hval⟩ := rateTerms_value hv hE
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  by_cases hu : S = some none ∨ some none ∈ cs ∨ c0 = none ∨ c1 = none
  · have hout : scaleBy S (Value.add
        (Value.mask (Value.nonzero c1) (Value.add
          (Value.mul kb (Functions.expR.apply (Value.add c0 (Value.mul c1 b))))
          (Value.mul m (Value.mul ka (Functions.expR.apply (Value.add c0 (Value.mul c1 a)))))))
        (Value.mask (Value.not (Value.nonzero c1))
          (Value.mul (Functions.expR.apply c0) (Value.add pb (Value.mul m pa))))) = none := by
      rcases hu with rfl | hd | rfl | rfl
      · rfl
      · have hkb' : kb = none := by
          rw [hkb.value, hmb.undefined
            (momentCoefs_undefined _ cs Ks hl (rateTables_nonzero Ks P hK) hd)]
        have hpb' : pb = none := by rw [hpb.value, hqb.undefined hd]
        subst hkb' hpb'
        have h1 : Value.add (Value.mul none (Functions.expR.apply (Value.add c0 (Value.mul c1 b))))
            (Value.mul m (Value.mul ka (Functions.expR.apply (Value.add c0 (Value.mul c1 a))))) =
            none := rfl
        have h2 : Value.mul (Functions.expR.apply c0) (Value.add none (Value.mul m pa)) = none := by
          cases Functions.expR.apply c0 <;> rfl
        rw [h1, h2]
        rcases c1 with _ | β
        · exact hnone
        · by_cases hβ : β = 0 <;>
            simp [Value.nonzero, Value.not, Value.mask, Value.add, hβ, hnone]
      · have h1 : Value.add (Value.mul kb (Functions.expR.apply (Value.add none (Value.mul c1 b))))
            (Value.mul m (Value.mul ka (Functions.expR.apply (Value.add none (Value.mul c1 a))))) =
            none := by
          cases kb <;> rfl
        have h2 : Value.mul (Functions.expR.apply none) (Value.add pb (Value.mul m pa)) = none :=
          rfl
        rw [h1, h2]
        rcases c1 with _ | β
        · exact hnone
        · by_cases hβ : β = 0 <;>
            simp [Value.nonzero, Value.not, Value.mask, Value.add, hβ, hnone]
      · exact hnone
    rw [hout]
    exact IntervalTerms.undefined (hmiss hu)
  simp only [not_or] at hu
  obtain ⟨hS', hd, h0, h1⟩ := hu
  obtain ⟨α, rfl⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨β, rfl⟩ := Option.ne_none_iff_exists'.1 h1
  have hg := hval α β hS' hd rfl rfl
  have hcR : Continuous (realEval cs) :=
    (Polynomial.continuous (realPoly cs)).congr (eval_realPoly cs)
  have hcP : Continuous fun x : ℝ => realEval cs x * polyEval P x * Real.exp (α + β * x) :=
    (hcR.mul (polyEval_continuous P)).mul (Real.continuous_exp.comp (by fun_prop))
  refine IntervalTerms.value hg (continuous_const.mul hcP) fun l u ha hb hm => ?_
  subst ha hb hm
  rw [intervalIntegral.integral_const_mul]
  have hpu : pb = some (momentValue u cs Qs) := by rw [hpb.value, hqb.value u rfl hd]
  have hpl : pa = some (momentValue l cs Qs) := by rw [hpa.value, hqa.value l rfl hd]
  by_cases hβ : β = 0
  · subst hβ
    have hI : ∫ x in l..u, realEval cs x * polyEval P x * Real.exp (α + 0 * x) =
        Real.exp α * momentValue u cs Qs - Real.exp α * momentValue l cs Qs := by
      have hD : ∀ x ∈ Set.uIcc l u, HasDerivAt (fun t : ℝ => Real.exp α * momentValue t cs Qs)
          (realEval cs x * polyEval P x * Real.exp (α + 0 * x)) x := fun x _ => by
        refine ((flats_deriv x cs Qs P hqb.length hQ).const_mul (Real.exp α)).congr_deriv ?_
        rw [zero_mul, add_zero]
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD (hcP.intervalIntegrable _ _)]
    rw [hI, hpu, hpl]
    rcases S with _ | _ | s
    · simp [scaleBy, scaleReal, Value.nonzero, Value.not, Value.mask, Value.add, Value.mul,
        Function1.apply, Functions.expR]
      ring
    · exact absurd rfl hS'
    · simp [scaleBy, scaleReal, Value.nonzero, Value.not, Value.mask, Value.add, Value.mul,
        Function1.apply, Functions.expR]
      left
      ring
  · have hi : Value.inv (some β) = some β⁻¹ := by simp [Value.inv, hβ]
    rw [hi] at hmb hma
    have hku : kb = some (momentValue2 u β⁻¹ cs Ks) := by
      rw [hkb.value, hmb.value u rfl (momentCoefs_defined _ cs Ks hd),
        momentValue_coefs u _ cs Ks hd]
    have hkl : ka = some (momentValue2 l β⁻¹ cs Ks) := by
      rw [hka.value, hma.value l rfl (momentCoefs_defined _ cs Ks hd),
        momentValue_coefs l _ cs Ks hd]
    have hI : ∫ x in l..u, realEval cs x * polyEval P x * Real.exp (α + β * x) =
        Real.exp (α + β * u) * momentValue2 u β⁻¹ cs Ks -
          Real.exp (α + β * l) * momentValue2 l β⁻¹ cs Ks := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => rateTables_deriv α hβ x cs Ks P hl hK) (hcP.intervalIntegrable _ _)]
    rw [hI, hku, hkl]
    rcases S with _ | _ | s
    · simp [scaleBy, scaleReal, Value.nonzero, Value.not, Value.mask, Value.add, Value.mul,
        Function1.apply, Functions.expR, hβ]
      ring
    · exact absurd rfl hS'
    · simp [scaleBy, scaleReal, Value.nonzero, Value.not, Value.mask, Value.add, Value.mul,
        Function1.apply, Functions.expR, hβ]
      left
      ring

/-! A polynomial in front of the exponential of a quadratic whose constant and
linear coefficients do not mention the axis. With `Q` the quadratic,
`P = κ + R' + Q'·R` for a polynomial `R` in the axis and a constant `κ` that
are both polynomials in the linear coefficient. Then `R·exp(Q)` and `κ` times
the antiderivative of the exponential, with the error function, are together
an antiderivative of `P·exp(Q)`. `R` is the list of its rows in the powers of
the linear coefficient, polynomials in the axis. -/

/-- A polynomial in the second value alone. -/
def poly2Const (κ : List ℚ) : List (List ℚ) := κ.map fun k => [k]

theorem poly2Eval_const (κ : List ℚ) (x c : ℝ) :
    poly2Eval (poly2Const κ) x c = polyEval κ c := by
  induction κ with
  | nil => rfl
  | cons k κ ih =>
    have ih' : poly2Eval (List.map (fun k => [k]) κ) x c = polyEval κ c := ih
    simp [poly2Const, poly2Eval, polyEval, ih']

/-- `P = κ + R' + (c₁ + 2·q₂·x)·R`, as polynomials in the axis and in the
linear coefficient. -/
def symErfRowsCheck (P : List ℚ) (K : List (List ℚ)) (κ : List ℚ) (q2 : ℚ) : Bool :=
  poly2Zero (poly2Add [P] (poly2Scale (-1)
    (poly2Add (poly2Const κ) (poly2Add (K.map polyDerivative)
      (poly2Add ([] :: K) (poly2Scale (2 * q2) (poly2Shift K)))))))

theorem symErfRows_identity {P : List ℚ} {K : List (List ℚ)} {κ : List ℚ} {q2 : ℚ}
    (h : symErfRowsCheck P K κ q2 = true) (x c : ℝ) :
    polyEval P x = polyEval κ c + poly2Eval (K.map polyDerivative) x c +
      (c + 2 * q2 * x) * poly2Eval K x c := by
  have h0 := poly2Eval_zero h x c
  simp only [poly2Eval_add, poly2Eval_scale, poly2Eval_const, poly2Eval_shift, poly2Eval,
    polyEval] at h0
  push_cast at h0
  linear_combination h0

/-- The derivative of the rest times the exponential. -/
theorem symErfRest_deriv (K : List (List ℚ)) (a b q x : ℝ) :
    HasDerivAt (fun t : ℝ => poly2Eval K t b * Real.exp (a + b * t + q * t ^ 2))
      ((poly2Eval (K.map polyDerivative) x b + (b + 2 * q * x) * poly2Eval K x b) *
        Real.exp (a + b * x + q * x ^ 2)) x := by
  have hq : HasDerivAt (fun t : ℝ => a + b * t + q * t ^ 2) (b + 2 * q * x) x := by
    have h1 := ((hasDerivAt_id x).const_mul b).const_add a
    have h2 := (hasDerivAt_pow 2 x).const_mul q
    refine (h1.add h2).congr_deriv ?_
    simp
    ring
  refine ((poly2Eval_hasDerivAt K b x).mul hq.exp).congr_deriv ?_
  ring

private theorem poly_gaussian_tendsto {l : Filter ℝ} {Q : ℝ → ℝ}
    (hpow : ∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (Q x)) l (𝓝 0)) (p : List ℚ) :
    ∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * polyEval p x * Real.exp (Q x)) l (𝓝 0) := by
  induction p with
  | nil => intro n; simpa [polyEval] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) l (𝓝 0))
  | cons c p ih =>
    intro n
    have h := ((hpow n).const_mul (c : ℝ)).add (ih (n + 1))
    simp only [mul_zero, add_zero] at h
    refine h.congr fun x => ?_
    simp only [polyEval]
    ring

/-- The rest times the exponential vanishes wherever every power times the
exponential does. -/
private theorem poly2_gaussian_tendsto {l : Filter ℝ} {Q : ℝ → ℝ}
    (hpow : ∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (Q x)) l (𝓝 0)) (b : ℝ)
    (K : List (List ℚ)) : Tendsto (fun x : ℝ => poly2Eval K x b * Real.exp (Q x)) l (𝓝 0) := by
  induction K with
  | nil => simpa [poly2Eval] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) l (𝓝 0))
  | cons p K ih =>
    have h := (poly_gaussian_tendsto hpow p 0).add (ih.const_mul b)
    simp only [mul_zero, add_zero] at h
    refine h.congr fun x => ?_
    simp only [poly2Eval, pow_zero, one_mul]
    ring

/-- The value below the mask: undefined everywhere where the scale or a
coefficient is, and the polynomial times the exponential of the quadratic
under the scale otherwise. -/
private theorem symErfPoly_value {v : ℝ → Option ℝ} {S : Option (Option ℝ)} {P : List ℚ}
    {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} {q2 : ℚ} (hv : Bell v S none P (some E))
    (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2)) :
    ((S = some none ∨ c0 = none ∨ c1 = none) → ∀ x, v x = none) ∧
      ∀ a b : ℝ, S ≠ some none → c0 = some a → c1 = some b →
        ∀ x, v x = some (scaleReal S * (polyEval P x * Real.exp (a + b * x + q2 * x ^ 2))) := by
  have hvx : ∀ x, v x = scaleBy S (Value.mul (some (polyEval P x)) (Functions.expR.apply (E x))) :=
    fun x => hv.plain x
  refine ⟨fun hm x => ?_, fun a b hS ha hb x => ?_⟩
  · rw [hvx]
    rcases hm with rfl | rfl | rfl
    · rfl
    · rw [hE.missing (Or.inl rfl) x]
      rcases S with _ | _ | s <;> rfl
    · rw [hE.missing (Or.inr (Or.inl rfl)) x]
      rcases S with _ | _ | s <;> rfl
  · subst ha hb
    have hEx : E x = some (a + b * x + q2 * x ^ 2) := by
      rw [hE.equation, h2]
      simp [coefValue, Value.add, Value.mul, Numeric.denote]
      ring
    rw [hvx, hEx]
    rcases S with _ | _ | s
    · simp [scaleBy, scaleReal, Value.mul, Function1.apply, Functions.expR]
    · exact absurd rfl hS
    · simp [scaleBy, scaleReal, Value.mul, Function1.apply, Functions.expR]

/-- The sum of the monomials of a table at a point, each row under its power
of a value. -/
private theorem table_sum {a h k : Option ℝ} {K : List (List ℚ)} {ms : List (Option ℝ)}
    (hm : MomentTerms a (curvatureCoefs h K 0) K ms) (hk : Sums ms k) (l β : ℝ)
    (ha : a = some l) (hh : h = some β) : k = some (poly2Eval K l β) := by
  subst ha hh
  rw [hk.value, hm.value l rfl (curvatureCoefs_defined _ K 0), momentValue_curvature]
  simp

/-- The exponential of the quadratic at a bound. -/
noncomputable def symErfExp (c0 c1 c2 o : Option ℝ) : Option ℝ :=
  Functions.expR.apply (Value.add c0 (Value.add (Value.mul c1 o) (Value.mul c2 (Value.mul o o))))

private theorem symErfExp_some (a b : ℝ) (q2 : ℚ) (t : ℝ) :
    symErfExp (some a) (some b) (some (Numeric.denote (s := .real) q2)) (some t) =
      some (Real.exp (a + b * t + q2 * t ^ 2)) := by
  simp [symErfExp, Value.add, Value.mul, Function1.apply, Functions.expR, Numeric.denote]
  ring

/-- It is undefined where a coefficient is, and at a bound that is. -/
private theorem symErfExp_missing {c0 c1 : Option ℝ} (c2 o : Option ℝ)
    (h : c0 = none ∨ c1 = none ∨ o = none) : symErfExp c0 c1 c2 o = none := by
  rcases h with rfl | rfl | rfl
  · rfl
  · cases c0 <;> rfl
  · cases c0 <;> cases c1 <;> rfl

/-- Above a bound: the constant times the complement of the error function. -/
noncomputable def symErfTail (c0 c1 k g d pi s n o : Option ℝ) : Option ℝ :=
  Value.mul (symErfConstant c0 c1 k g d pi)
    (Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply s) (Value.add o (Value.mul n c1))))

/-- Between two bounds, under the scale, with `R` the rest at a bound and `κ`
the polynomial of the constant at the linear coefficient:
`R(b)·exp(Q(b)) - R(a)·exp(Q(a)) + κ·(G(b) - G(a))`, where `G` is the
antiderivative of the exponential with the error function. -/
theorem IntervalTerms.symbolicErfPolynomial {a b m : Option ℝ} {v : ℝ → Option ℝ}
    {S : Option (Option ℝ)} {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ}
    (K : List (List ℚ)) (κ : List ℚ) (q2 γ δ w σ ν : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : symErfCheck false [1] 1 q2 γ δ w (1 / 2) σ ν = true)
    (hR : symErfRowsCheck P K κ q2 = true)
    {kb ka kk k g d pi s n : Option ℝ} {msb msa msk : List (Option ℝ)}
    (hmb : MomentTerms b (curvatureCoefs c1 K 0) K msb) (hkb : Sums msb kb)
    (hma : MomentTerms a (curvatureCoefs c1 K 0) K msa) (hka : Sums msa ka)
    (hmk : RowTerms none c1 κ 0 [] msk) (hkk : Sums msk kk)
    (hk : k = some (Numeric.denote (s := .real) (1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) ν)) :
    IntervalTerms a b m v (scaleBy S (Value.add
      (Value.add (Value.mul kb (symErfExp c0 c1 c2 b))
        (Value.mul m (Value.mul ka (symErfExp c0 c1 c2 a))))
      (Value.mul kk (Value.add (symErfBetween c0 c1 k g d pi s n b)
        (Value.mul m (symErfBetween c0 c1 k g d pi s n a)))))) := by
  obtain ⟨hmiss, hval⟩ := symErfPoly_value hv hE h2
  by_cases hu : S = some none ∨ c0 = none ∨ c1 = none
  · have hout : scaleBy S (Value.add
        (Value.add (Value.mul kb (symErfExp c0 c1 c2 b))
          (Value.mul m (Value.mul ka (symErfExp c0 c1 c2 a))))
        (Value.mul kk (Value.add (symErfBetween c0 c1 k g d pi s n b)
          (Value.mul m (symErfBetween c0 c1 k g d pi s n a))))) = none := by
      rcases hu with rfl | hm
      · rfl
      · rw [symErfExp_missing c2 b (hm.imp_right Or.inl)]
        have h1 : Value.add (Value.mul kb none)
            (Value.mul m (Value.mul ka (symErfExp c0 c1 c2 a))) = none := by cases kb <;> rfl
        rw [h1]
        rcases S with _ | _ | s' <;> rfl
    rw [hout]
    exact IntervalTerms.undefined (hmiss hu)
  simp only [not_or] at hu
  obtain ⟨hS', h0, h1⟩ := hu
  obtain ⟨a0, rfl⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨b1, rfl⟩ := Option.ne_none_iff_exists'.1 h1
  subst h2
  obtain ⟨hK, hSq, hN⟩ := symErf_literals h a0 b1 hk hg hd hpi hs hn
  have hval' := hval a0 b1 hS' rfl rfl
  have hcP : Continuous fun x : ℝ => polyEval P x * Real.exp (a0 + b1 * x + q2 * x ^ 2) :=
    (polyEval_continuous P).mul (Real.continuous_exp.comp (by fun_prop))
  refine IntervalTerms.value hval' (continuous_const.mul hcP) fun l u ha hb hm => ?_
  subst ha hb hm
  have hD := fun x : ℝ => ((symErfRest_deriv K a0 b1 q2 x).add
    ((symErf_deriv h a0 b1 x).const_mul (polyEval κ b1))).congr_deriv (show _ =
      polyEval P x * Real.exp (a0 + b1 * x + q2 * x ^ 2) by
        rw [symErfRows_identity hR x b1]
        push_cast
        ring)
  have hG : ∀ t, symErfBetween (some a0) (some b1) k g d pi s n (some t) =
      some (((1 / 2 : ℚ) : ℝ) * (Real.exp (a0 + γ * (b1 * b1)) * √(Real.pi * δ)) *
        Functions.erfR.value (√(σ : ℝ) * (t + ν * b1))) := fun t => by
    rw [symErfBetween, hK, hSq, hN]
    show Value.mul (some _) (Functions.erfR.apply (some _)) = _
    rw [erf_apply]
    rfl
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x) (hcP.intervalIntegrable _ _),
    table_sum hmb hkb u b1 rfl rfl, table_sum hma hka l b1 rfl rfl, flat_sum hmk hkk b1 rfl,
    hG u, hG l, symErfExp_some, symErfExp_some]
  rcases S with _ | _ | s'
  · simp only [scaleBy, scaleReal, Value.add, Value.mul, Option.some.injEq]
    ring
  · exact absurd rfl hS'
  · simp only [scaleBy, scaleReal, Value.add, Value.mul, Option.some.injEq]
    ring

/-- Above a bound: `-R(a)·exp(Q(a)) + κ·C·erfc(…)`, under the scale. -/
theorem HalfLineTerms.symbolicErfPolynomial {a m : Option ℝ} {v : ℝ → Option ℝ}
    {S : Option (Option ℝ)} {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ}
    (K : List (List ℚ)) (κ : List ℚ) (q2 γ δ w σ ν : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : symErfCheck false [1] 1 q2 γ δ w (1 / 2) σ ν = true)
    (hR : symErfRowsCheck P K κ q2 = true)
    {ka kk u k g d pi s n : Option ℝ} {msa msk : List (Option ℝ)}
    (hma : MomentTerms a (curvatureCoefs c1 K 0) K msa) (hka : Sums msa ka)
    (hmk : RowTerms none c1 κ 0 [] msk) (hkk : Sums msk kk)
    (hu : u = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) (1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) ν)) :
    HalfLineTerms a m v (scaleBy S (Value.add
      (Value.mul u (Value.mul ka (symErfExp c0 c1 c2 a)))
      (Value.mul kk (symErfTail c0 c1 k g d pi s n a)))) := by
  obtain ⟨hmiss, hval⟩ := symErfPoly_value hv hE h2
  have hU : u = some (-1 : ℝ) := by rw [hu]; simp [Numeric.denote]
  subst hU
  have hgone : ∀ o, (c0 = none ∨ c1 = none ∨ o = none) → scaleBy S (Value.add
      (Value.mul (some (-1 : ℝ)) (Value.mul ka (symErfExp c0 c1 c2 o)))
      (Value.mul kk (symErfTail c0 c1 k g d pi s n o))) = none := fun o hm => by
    rw [symErfExp_missing c2 o hm]
    have h1 : Value.add (Value.mul (some (-1 : ℝ)) (Value.mul ka none))
        (Value.mul kk (symErfTail c0 c1 k g d pi s n o)) = none := by cases ka <;> rfl
    rw [h1]
    rcases S with _ | _ | s' <;> rfl
  by_cases hund : S = some none ∨ c0 = none ∨ c1 = none
  · have hout : scaleBy S (Value.add
        (Value.mul (some (-1 : ℝ)) (Value.mul ka (symErfExp c0 c1 c2 a)))
        (Value.mul kk (symErfTail c0 c1 k g d pi s n a))) = none := by
      rcases hund with rfl | hm
      · rfl
      · exact hgone a (hm.imp_right Or.inl)
    rw [hout]
    exact HalfLineTerms.undefined (hmiss hund)
  simp only [not_or] at hund
  obtain ⟨hS', h0, h1⟩ := hund
  obtain ⟨a0, rfl⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨b1, rfl⟩ := Option.ne_none_iff_exists'.1 h1
  have hnone := hgone
  subst h2
  obtain ⟨hK, hSq, hN⟩ := symErf_literals h a0 b1 hk hg hd hpi hs hn
  obtain ⟨hq, _⟩ := symErf_facts h a0 b1
  obtain ⟨hDc, hTc⟩ := symErfc_deriv h a0 b1
  have hval' := hval a0 b1 hS' rfl rfl
  have hI : ∀ l : ℝ, IntegrableOn
      (fun x : ℝ => polyEval P x * Real.exp (a0 + b1 * x + q2 * x ^ 2)) (Ioi l) volume :=
    fun l => (gaussian_moments2 a0 b1 hq P).1.integrableOn
  have hD := fun x : ℝ => ((symErfRest_deriv K a0 b1 q2 x).add
    ((hDc x).const_mul (polyEval κ b1))).congr_deriv (show _ =
      polyEval P x * Real.exp (a0 + b1 * x + q2 * x ^ 2) by
        rw [symErfRows_identity hR x b1]
        push_cast
        ring)
  have hT := (poly2_gaussian_tendsto (Q := fun x : ℝ => a0 + b1 * x + q2 * x ^ 2)
    (fun n => pow_gaussian_atTop a0 b1 hq n) b1 K).add (hTc.const_mul (polyEval κ b1))
  simp only [mul_zero, add_zero] at hT
  have hG : ∀ t, symErfTail (some a0) (some b1) k g d pi s n (some t) =
      some (((1 / 2 : ℚ) : ℝ) * (Real.exp (a0 + γ * (b1 * b1)) * √(Real.pi * δ)) *
        Functions.erfcR.value (√(σ : ℝ) * (t + ν * b1))) := fun t => by
    rw [symErfTail, hK, hSq, hN]
    show Value.mul (some _) (Functions.erfcR.apply (some _)) = _
    rw [erfc_apply]
    rfl
  refine HalfLineTerms.value hval' (fun l => (hI l).const_mul _)
    (fun ha => hnone none (Or.inr (Or.inr rfl)) |>.trans rfl |> (ha ▸ ·)) fun l ha => ?_
  subst ha
  rw [integral_const_mul,
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hD x) (hI l) hT,
    table_sum hma hka l b1 rfl rfl, flat_sum hmk hkk b1 rfl, hG l, symErfExp_some]
  rcases S with _ | _ | s'
  · simp only [scaleBy, scaleReal, Value.add, Value.mul, Option.some.injEq]
    ring
  · exact absurd rfl hS'
  · simp only [scaleBy, scaleReal, Value.add, Value.mul, Option.some.injEq]
    ring

/-- Below a bound: `R(b)·exp(Q(b)) + κ·C·erfc(…)` of the reflected argument,
under the scale. -/
theorem UpperTerms.symbolicErfPolynomial {b : Option ℝ} {v : ℝ → Option ℝ}
    {S : Option (Option ℝ)} {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ}
    (K : List (List ℚ)) (κ : List ℚ) (q2 γ δ w σ ν : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : symErfCheck true [1] 1 q2 γ δ w (1 / 2) σ ν = true)
    (hR : symErfRowsCheck P K κ q2 = true)
    {kb kk u k g d pi s n : Option ℝ} {msb msk : List (Option ℝ)}
    (hmb : MomentTerms b (curvatureCoefs c1 K 0) K msb) (hkb : Sums msb kb)
    (hmk : RowTerms none c1 κ 0 [] msk) (hkk : Sums msk kk)
    (hu : u = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) (1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) (hs : s = some (Numeric.denote (s := .real) σ))
    (hn : n = some (Numeric.denote (s := .real) ν)) :
    UpperTerms b v (scaleBy S (Value.add (Value.mul kb (symErfExp c0 c1 c2 b))
      (Value.mul kk (symErfBelow c0 c1 u k g d pi s n b)))) := by
  obtain ⟨hmiss, hval⟩ := symErfPoly_value hv hE h2
  have hU : u = some (-1 : ℝ) := by rw [hu]; simp [Numeric.denote]
  subst hU
  have hgone : ∀ o, (c0 = none ∨ c1 = none ∨ o = none) → scaleBy S (Value.add
      (Value.mul kb (symErfExp c0 c1 c2 o))
      (Value.mul kk (symErfBelow c0 c1 (some (-1 : ℝ)) k g d pi s n o))) = none := fun o hm => by
    rw [symErfExp_missing c2 o hm]
    have h1 : Value.add (Value.mul kb none)
        (Value.mul kk (symErfBelow c0 c1 (some (-1 : ℝ)) k g d pi s n o)) = none := by
      cases kb <;> rfl
    rw [h1]
    rcases S with _ | _ | s' <;> rfl
  by_cases hund : S = some none ∨ c0 = none ∨ c1 = none
  · have hout : scaleBy S (Value.add (Value.mul kb (symErfExp c0 c1 c2 b))
        (Value.mul kk (symErfBelow c0 c1 (some (-1 : ℝ)) k g d pi s n b))) = none := by
      rcases hund with rfl | hm
      · rfl
      · exact hgone b (hm.imp_right Or.inl)
    rw [hout]
    exact UpperTerms.undefined (hmiss hund)
  simp only [not_or] at hund
  obtain ⟨hS', h0, h1⟩ := hund
  obtain ⟨a0, rfl⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨b1, rfl⟩ := Option.ne_none_iff_exists'.1 h1
  have hnone := hgone
  subst h2
  obtain ⟨hK, hSq, hN⟩ := symErf_literals h a0 b1 hk hg hd hpi hs hn
  obtain ⟨hq, _⟩ := symErf_facts h a0 b1
  obtain ⟨hDc, hTc⟩ := symErfc_reflected_deriv h a0 b1
  have hval' := hval a0 b1 hS' rfl rfl
  have hI : ∀ t : ℝ, IntegrableOn
      (fun x : ℝ => polyEval P x * Real.exp (a0 + b1 * x + q2 * x ^ 2)) (Iic t) volume :=
    fun t => (gaussian_moments2 a0 b1 hq P).1.integrableOn
  have hD := fun x : ℝ => ((symErfRest_deriv K a0 b1 q2 x).add
    ((hDc x).const_mul (polyEval κ b1))).congr_deriv (show _ =
      polyEval P x * Real.exp (a0 + b1 * x + q2 * x ^ 2) by
        rw [symErfRows_identity hR x b1]
        push_cast
        ring)
  have hT := (poly2_gaussian_tendsto (Q := fun x : ℝ => a0 + b1 * x + q2 * x ^ 2)
    (fun n => pow_gaussian_atBot a0 b1 hq n) b1 K).add (hTc.const_mul (polyEval κ b1))
  simp only [mul_zero, add_zero] at hT
  have hG : ∀ t, symErfBelow (some a0) (some b1) (some (-1 : ℝ)) k g d pi s n (some t) =
      some (((1 / 2 : ℚ) : ℝ) * (Real.exp (a0 + γ * (b1 * b1)) * √(Real.pi * δ)) *
        Functions.erfcR.value (√(σ : ℝ) * (ν * b1 + -1 * t))) := fun t => by
    rw [symErfBelow, hK, hSq, hN]
    show Value.mul (some _) (Functions.erfcR.apply (some _)) = _
    rw [erfc_apply]
    rfl
  refine UpperTerms.value hval' (fun t => (hI t).const_mul _)
    (fun hb => hnone none (Or.inr (Or.inr rfl)) |>.trans rfl |> (hb ▸ ·)) fun t hb => ?_
  subst hb
  rw [integral_const_mul,
    integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hD x) (hI t) hT,
    table_sum hmb hkb t b1 rfl rfl, flat_sum hmk hkk b1 rfl, hG t, symErfExp_some]
  rcases S with _ | _ | s'
  · simp only [scaleBy, scaleReal, Value.add, Value.mul, Option.some.injEq]
    ring
  · exact absurd rfl hS'
  · simp only [scaleBy, scaleReal, Value.add, Value.mul, Option.some.injEq]
    ring

/-! A curvature that does not mention the axis and cannot vanish. Beyond a
single bound the exponential of the quadratic is integrable exactly where the
curvature is negative, and the closed form with the complement of the error
function is missing exactly where it is positive, the root of a negative
number: no guard is needed. A curvature that may be zero is another matter:
there the exponent is linear, and integrable for one sign of its rate. -/

/-- Around its vertex, with real coefficients: the exponential of the value
there times a Gaussian, and the constant in front of the error function. -/
private theorem gauss_real_facts (α β : ℝ) {c : ℝ} (hc : c < 0) :
    (0 : ℝ) < -1 * c ∧ 0 ≤ Real.pi * (-1 * c⁻¹) ∧
      (∀ t : ℝ, Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) *
          Real.exp (-(√(-1 * c) * (t + 1 / 2 * c⁻¹ * β)) ^ 2) =
        Real.exp (α + β * t + c * t ^ 2)) ∧
      (1 / 2 : ℝ) * √(Real.pi * (-1 * c⁻¹)) * (2 / √Real.pi * √(-1 * c)) = 1 := by
  have hne : c ≠ 0 := hc.ne
  have hσ : (0 : ℝ) < -1 * c := by linarith
  have hinv : (0 : ℝ) < -1 * c⁻¹ := by
    have := inv_lt_zero.2 hc
    linarith
  refine ⟨hσ, mul_nonneg Real.pi_pos.le hinv.le, fun t => ?_, ?_⟩
  · rw [← Real.exp_add, mul_pow, Real.sq_sqrt hσ.le]
    congr 1
    field_simp
    ring
  · have hds : √(-1 * c⁻¹) * √(-1 * c) = 1 := by
      rw [← Real.sqrt_mul hinv.le]
      have : -1 * c⁻¹ * (-1 * c) = 1 := by field_simp
      rw [this, Real.sqrt_one]
    have hpi : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    rw [Real.sqrt_mul Real.pi_pos.le]
    have h1 : (1 / 2 : ℝ) * (√Real.pi * √(-1 * c⁻¹)) * (2 / √Real.pi * √(-1 * c)) =
        √Real.pi / √Real.pi * (√(-1 * c⁻¹) * √(-1 * c)) := by ring
    rw [h1, hds, div_self hpi, mul_one]

/-- The exponential of a quadratic with negative curvature above a bound. -/
theorem gauss_Ioi (α β : ℝ) {c : ℝ} (hc : c < 0) (l : ℝ) :
    ∫ x in Ioi l, Real.exp (α + β * x + c * x ^ 2) =
      1 / 2 * (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))) *
        Functions.erfcR.value (√(-1 * c) * (l + 1 / 2 * c⁻¹ * β)) := by
  obtain ⟨hσ, _, hC, hB⟩ := gauss_real_facts α β hc
  have hD : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -1 * (1 / 2 *
        (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))) *
        Functions.erfcR.value (√(-1 * c) * (t + 1 / 2 * c⁻¹ * β))))
      (Real.exp (α + β * x + c * x ^ 2)) x := fun x => by
    have hin : HasDerivAt (fun t : ℝ => √(-1 * c) * (t + 1 / 2 * c⁻¹ * β)) (√(-1 * c) * 1) x :=
      ((hasDerivAt_id x).add_const (1 / 2 * c⁻¹ * β)).const_mul _
    have h2 := (((erfc_hasDerivAt (√(-1 * c) * (x + 1 / 2 * c⁻¹ * β))).comp x hin).const_mul
      (1 / 2 * (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))))).const_mul
        (-1 : ℝ)
    refine h2.congr_deriv ?_
    linear_combination
      (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) *
        Real.exp (-(√(-1 * c) * (x + 1 / 2 * c⁻¹ * β)) ^ 2)) * hB + hC x
  have hT : Tendsto (fun t : ℝ => -1 * (1 / 2 *
        (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))) *
        Functions.erfcR.value (√(-1 * c) * (t + 1 / 2 * c⁻¹ * β)))) atTop (𝓝 0) := by
    have harg : Tendsto (fun t : ℝ => √(-1 * c) * (t + 1 / 2 * c⁻¹ * β)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (1 / 2 * c⁻¹ * β) tendsto_id).const_mul_atTop
        (Real.sqrt_pos.2 hσ)
    have he := ((erfc_tendsto_atTop.comp harg).const_mul
      (1 / 2 * (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))))).const_mul
        (-1 : ℝ)
    simpa using he
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hD x)
    (gaussian_integrable α β c hc).integrableOn hT]
  ring

/-- Below a bound. -/
theorem gauss_Iic (α β : ℝ) {c : ℝ} (hc : c < 0) (u : ℝ) :
    ∫ x in Iic u, Real.exp (α + β * x + c * x ^ 2) =
      1 / 2 * (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))) *
        Functions.erfcR.value (√(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * u)) := by
  obtain ⟨hσ, _, hC, hB⟩ := gauss_real_facts α β hc
  have hD : ∀ x : ℝ, HasDerivAt (fun t : ℝ => 1 / 2 *
        (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))) *
        Functions.erfcR.value (√(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * t)))
      (Real.exp (α + β * x + c * x ^ 2)) x := fun x => by
    have hin : HasDerivAt (fun t : ℝ => √(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * t))
        (√(-1 * c) * (-1 * 1)) x :=
      (((hasDerivAt_id x).const_mul (-1 : ℝ)).const_add (-1 / 2 * c⁻¹ * β)).const_mul _
    have h2 := ((erfc_hasDerivAt (√(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * x))).comp x hin).const_mul
      (1 / 2 * (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))))
    refine h2.congr_deriv ?_
    have hC' := hC x
    rw [show (-(√(-1 * c) * (x + 1 / 2 * c⁻¹ * β)) ^ 2) =
        -(√(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * x)) ^ 2 by ring] at hC'
    linear_combination
      (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) *
        Real.exp (-(√(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * x)) ^ 2)) * hB + hC'
  have hT : Tendsto (fun t : ℝ => 1 / 2 *
        (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))) *
        Functions.erfcR.value (√(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * t))) atBot (𝓝 0) := by
    have harg : Tendsto (fun t : ℝ => √(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * t)) atBot atTop := by
      have h1 : Tendsto (fun t : ℝ => -1 * t) atBot atTop := by
        simpa using (tendsto_neg_atBot_atTop : Tendsto (Neg.neg : ℝ → ℝ) atBot atTop)
      exact (tendsto_atTop_add_const_left atBot (-1 / 2 * c⁻¹ * β) h1).const_mul_atTop
        (Real.sqrt_pos.2 hσ)
    have he := (erfc_tendsto_atTop.comp harg).const_mul
      (1 / 2 * (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹))))
    simpa using he
  rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hD x)
    (gaussian_integrable α β c hc).integrableOn hT]
  ring

/-- With a positive curvature the exponential of a quadratic is not integrable
above a bound: far enough it stays above a constant. -/
theorem exp_quadratic_not_integrableOn_Ioi (α β : ℝ) {c : ℝ} (hc : 0 < c) (l : ℝ) {k : ℝ}
    (hk : k ≠ 0) :
    ¬ IntegrableOn (fun x : ℝ => k * Real.exp (α + β * x + c * x ^ 2)) (Ioi l) volume := by
  intro hi
  have hs : IntegrableOn (fun _ : ℝ => |k| * Real.exp α) (Ioi (max l (max (-β / c) 0))) volume := by
    refine Integrable.mono' (hi.mono_set (Ioi_subset_Ioi (le_max_left _ _))).norm
      aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : max l (max (-β / c) 0) < x := hx
    have h1 : -β / c < x := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hx'
    have h0 : 0 < x := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hx'
    have h2 : 0 ≤ β + c * x := by
      rw [div_lt_iff₀ hc] at h1
      linarith
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg k) (Real.exp_pos _).le), norm_mul,
      Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [mul_nonneg h0.le h2])) (abs_nonneg k)
  rw [integrableOn_const] at hs
  rcases hs with h0 | hfin
  · exact (mul_pos (abs_pos.2 hk) (Real.exp_pos _)).ne' h0
  · rw [Real.volume_Ioi] at hfin
    exact lt_irrefl _ hfin

/-- Nor below one. -/
theorem exp_quadratic_not_integrableOn_Iic (α β : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ) {k : ℝ}
    (hk : k ≠ 0) :
    ¬ IntegrableOn (fun x : ℝ => k * Real.exp (α + β * x + c * x ^ 2)) (Iic u) volume := by
  intro hi
  have hs : IntegrableOn (fun _ : ℝ => |k| * Real.exp α) (Iic (min u (min (-β / c) 0))) volume := by
    refine Integrable.mono' (hi.mono_set (Iic_subset_Iic.2 (min_le_left _ _))).norm
      aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : x ≤ min u (min (-β / c) 0) := hx
    have h1 : x ≤ -β / c := le_trans hx' (le_trans (min_le_right _ _) (min_le_left _ _))
    have h0 : x ≤ 0 := le_trans hx' (le_trans (min_le_right _ _) (min_le_right _ _))
    have h2 : β + c * x ≤ 0 := by
      rw [le_div_iff₀ hc] at h1
      linarith
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg k) (Real.exp_pos _).le), norm_mul,
      Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [mul_nonneg_of_nonpos_of_nonpos h0 h2])) (abs_nonneg k)
  rw [integrableOn_const] at hs
  rcases hs with h0 | hfin
  · exact (mul_pos (abs_pos.2 hk) (Real.exp_pos _)).ne' h0
  · rw [Real.volume_Iic] at hfin
    exact lt_irrefl _ hfin

/-- The polynomial in front is a constant other than zero, of which `half` is
half. -/
def curvatureHalfCheck (P : List ℚ) (κ half : ℚ) : Bool :=
  rateCheck P κ && decide (half * 2 = κ)

/-- The constant in front of the complement of the error function:
`k·(exp(c₀ + (g·c₂⁻¹)·(c₁·c₁))·√(π·(m·c₂⁻¹)))`. -/
noncomputable def curvatureConstant (c0 c1 c2 k g m pi : Option ℝ) : Option ℝ :=
  Value.mul k (Value.mul
    (Functions.expR.apply
      (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
    (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))

/-- It is undefined where a coefficient is. -/
private theorem curvatureConstant_missing {c0 c1 c2 : Option ℝ} (k g m pi : Option ℝ)
    (h : c0 = none ∨ c1 = none ∨ c2 = none) : curvatureConstant c0 c1 c2 k g m pi = none := by
  have hexp : Functions.expR.apply
      (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))) = none := by
    rcases h with rfl | rfl | rfl
    · rfl
    · cases c0 <;> cases Value.mul g (Value.inv c2) <;> rfl
    · cases c0 <;> cases g <;> rfl
  rw [curvatureConstant, hexp]
  cases k <;> rfl

/-- The value below the mask: undefined everywhere where a coefficient or the
scale is, and the constant times the exponential under the scale otherwise. -/
private theorem curvature_value {v : ℝ → Option ℝ} {S : Option (Option ℝ)} {P : List ℚ}
    {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} {κ half : ℚ} (hv : Bell v S none P (some E))
    (hE : Quadratic E (some c0) (some c1) (some c2)) (hP : curvatureHalfCheck P κ half = true) :
    (κ : ℝ) ≠ 0 ∧ (half : ℝ) * 2 = κ ∧
      ((S = some none ∨ c0 = none ∨ c1 = none ∨ c2 = none) → ∀ x, v x = none) ∧
      ∀ α β c : ℝ, S ≠ some none → c0 = some α → c1 = some β → c2 = some c →
        ∀ x, v x = some (scaleReal S * (κ * Real.exp (α + β * x + c * x ^ 2))) := by
  simp only [curvatureHalfCheck, rateCheck, Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨hz, hκ⟩, hh⟩ := hP
  have hPx : ∀ x : ℝ, polyEval P x = κ := fun x => by
    have h0 := polyEval_zero hz x
    rw [polyEval_add, polyEval_scale] at h0
    simp only [polyEval] at h0
    push_cast at h0
    linarith
  have hvx : ∀ x, v x = scaleBy S (Value.mul (some (polyEval P x)) (Functions.expR.apply (E x))) :=
    fun x => hv.plain x
  refine ⟨by exact_mod_cast hκ, by exact_mod_cast hh, fun hm x => ?_,
    fun α β c hS h0 h1 h2 x => ?_⟩
  · rw [hvx]
    rcases hm with rfl | hm
    · rfl
    · rw [hE.missing hm x]
      rcases S with _ | _ | s <;> simp [scaleBy, Value.mul, Function1.apply]
  · subst h0 h1 h2
    have hEx : E x = some (α + β * x + c * x ^ 2) := by
      rw [hE.equation]
      show some (α + (β * x + c * x ^ 2)) = some (α + β * x + c * x ^ 2)
      congr 1
      ring
    rw [hvx, hEx, hPx]
    rcases S with _ | _ | s
    · simp [scaleBy, scaleReal, Value.mul, Function1.apply, Functions.expR]
    · exact absurd rfl hS
    · simp [scaleBy, scaleReal, Value.mul, Function1.apply, Functions.expR]

/-- The literals of the constant and of the root, at real coefficients with a
negative curvature; with a positive one the constant is undefined. -/
private theorem curvature_literals (α β : ℝ) {c : ℝ} (hne : c ≠ 0) {half : ℚ}
    {k g m pi : Option ℝ} (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    (c < 0 → curvatureConstant (some α) (some β) (some c) k g m pi =
        some ((half : ℝ) * (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹)))) ∧
      Functions.sqrtR.apply (Value.mul m (some c)) = some (√(-1 * c))) ∧
    (0 < c → curvatureConstant (some α) (some β) (some c) k g m pi = none) := by
  constructor
  · intro hc
    obtain ⟨hσ, hpos, _⟩ := gauss_real_facts α β hc
    have hpos' : Real.pi * c⁻¹ ≤ 0 := by linarith
    constructor
    · rw [curvatureConstant, hk, hg, hm, hpi]
      simp [Value.mul, Value.add, Value.inv, hne, Function1.apply, Functions.expR,
        Functions.sqrtR, Functions.pi, Numeric.denote, hpos']
    · rw [hm]
      have : (0 : ℝ) ≤ -c := by linarith
      simp [Value.mul, Function1.apply, Functions.sqrtR, Numeric.denote, this]
  · intro hc
    have hneg : ¬ Real.pi * c⁻¹ ≤ 0 := not_le.2 (mul_pos Real.pi_pos (inv_pos.2 hc))
    have hroot : Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv (some c)))) = none := by
      rw [hm, hpi]
      simp [Value.inv, hne, Value.mul, Function1.apply, Functions.sqrtR, Functions.pi,
        Numeric.denote, hneg]
    rw [curvatureConstant, hroot]
    cases k <;> cases Functions.expR.apply
      (Value.add (some α) (Value.mul (Value.mul g (Value.inv (some c))) (Value.mul (some β) (some β)))) <;> rfl

/-- Above a bound, with the complement of the error function. -/
theorem curvature_above (strict : Bool) {a : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ half : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (hP : curvatureHalfCheck P κ half = true) (hS : scaleNonvanishing S) (hN : Nonvanishing c2)
    {k g m h pi : Option ℝ} (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hh : h = some (Numeric.denote (s := .real) (1 / 2 : ℚ))) (hpi : pi = some Functions.pi) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) =
      scaleBy S (Value.mul (curvatureConstant c0 c1 c2 k g m pi)
        (Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply (Value.mul m c2))
          (Value.add a (Value.mul (Value.mul h (Value.inv c2)) c1))))) := by
  obtain ⟨hκ, hhalf, hmiss, hval⟩ := curvature_value hv hE hP
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  by_cases hu : S = some none ∨ c0 = none ∨ c1 = none ∨ c2 = none
  · rw [above_undefined strict a (hmiss hu)]
    rcases hu with rfl | hu
    · rfl
    · rw [curvatureConstant_missing k g m pi hu]
      exact hnone.symm
  simp only [not_or] at hu
  obtain ⟨hS', h0, h1, h2⟩ := hu
  obtain ⟨α, rfl⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨β, rfl⟩ := Option.ne_none_iff_exists'.1 h1
  obtain ⟨c, rfl⟩ := Option.ne_none_iff_exists'.1 h2
  have hne : c ≠ 0 := hN c rfl
  have hg' := hval α β c hS' rfl rfl rfl
  have hσ : scaleReal S ≠ 0 := by
    rcases S with _ | _ | s
    · simp [scaleReal]
    · exact absurd rfl hS'
    · exact hS s rfl
  obtain ⟨hlit, hpos⟩ := curvature_literals α β hne hk hg hm hpi
  have hH : h = some ((1 / 2 : ℝ)) := by rw [hh]; simp [Numeric.denote]
  rcases a with _ | l
  · rw [show partialIntegral volume (fun x => Value.mask (compare strict none (some x)) (v x)) =
        none from if_neg fun hd => by
          obtain ⟨r, hr⟩ := hd.1 0
          cases strict <;> cases hr]
    have : Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply (Value.mul m (some c)))
        (Value.add none (Value.mul (Value.mul h (Value.inv (some c))) (some β)))) = none := by
      cases Functions.sqrtR.apply (Value.mul m (some c)) <;> rfl
    rw [this]
    cases curvatureConstant (some α) (some β) (some c) k g m pi <;> exact hnone.symm
  have hcmp : ∀ x : ℝ, l < x → compare strict (some l) (some x) = some true := fun x hx => by
    cases strict <;> simp [compare, Value.lt, Value.le, hx, hx.le]
  rcases lt_or_gt_of_ne hne with hc | hc
  · obtain ⟨hK, hR⟩ := hlit hc
    have hI : ∀ l' : ℝ, IntegrableOn
        (fun x : ℝ => scaleReal S * (κ * Real.exp (α + β * x + c * x ^ 2))) (Ioi l') volume :=
      fun l' => (((gaussian_integrable α β c hc).integrableOn.const_mul _).const_mul _)
    rw [halfline_integral strict (some l) (some (Numeric.denote (s := .real) (-1 : ℚ))) rfl
      ⟨fun _ => rfl⟩ (HalfLineTerms.value hg' hI (fun h => by cases h) fun l' hl => by
        cases hl
        rfl)]
    rw [integral_const_mul, integral_const_mul, gauss_Ioi α β hc l, hK, hR, hH]
    have harg : Value.mul (some (√(-1 * c)))
        (Value.add (some l) (Value.mul (Value.mul (some (1 / 2 : ℝ)) (Value.inv (some c))) (some β))) =
        some (√(-1 * c) * (l + 1 / 2 * c⁻¹ * β)) := by
      simp [Value.mul, Value.add, Value.inv, hne]
    rw [harg, erfc_apply]
    rcases S with _ | _ | s
    · simp only [scaleBy, scaleReal, Value.mul, Option.some.injEq]
      linear_combination (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹)) *
        Functions.erfcR.value (√(-1 * c) * (l + 1 / 2 * c⁻¹ * β))) * (-hhalf) / 2
    · exact absurd rfl hS'
    · simp only [scaleBy, scaleReal, Value.mul, Option.some.injEq]
      linear_combination (s * (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹)) *
        Functions.erfcR.value (√(-1 * c) * (l + 1 / 2 * c⁻¹ * β)))) * (-hhalf) / 2
  · have hn : partialIntegral volume
        (fun x => Value.mask (compare strict (some l) (some x)) (v x)) = none := by
      apply if_neg
      rintro ⟨_, hint⟩
      have hon : IntegrableOn (fun x : ℝ => scaleReal S * κ * Real.exp (α + β * x + c * x ^ 2))
          (Ioi l) volume := by
        refine (hint.integrableOn (s := Ioi l)).congr_fun (fun x hx => ?_) measurableSet_Ioi
        show (Value.mask (compare strict (some l) (some x)) (v x)).getD 0 = _
        rw [hcmp x hx, hg']
        show scaleReal S * (κ * Real.exp (α + β * x + c * x ^ 2)) = _
        ring
      exact exp_quadratic_not_integrableOn_Ioi α β hc l (mul_ne_zero hσ hκ) hon
    rw [hn, hpos hc]
    exact hnone.symm

/-- Below a bound, with the complement of the reflected argument. -/
theorem curvature_below (strict : Bool) {b : Option ℝ} {v : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ half : ℚ)
    (hv : Bell v S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (hP : curvatureHalfCheck P κ half = true) (hS : scaleNonvanishing S) (hN : Nonvanishing c2)
    {k g m h pi : Option ℝ} (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hh : h = some (Numeric.denote (s := .real) (-1 / 2 : ℚ))) (hpi : pi = some Functions.pi) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) =
      scaleBy S (Value.mul (curvatureConstant c0 c1 c2 k g m pi)
        (Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply (Value.mul m c2))
          (Value.add (Value.mul (Value.mul h (Value.inv c2)) c1) (Value.mul m b))))) := by
  obtain ⟨hκ, hhalf, hmiss, hval⟩ := curvature_value hv hE hP
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  by_cases hu : S = some none ∨ c0 = none ∨ c1 = none ∨ c2 = none
  · rw [below_undefined strict b (hmiss hu)]
    rcases hu with rfl | hu
    · rfl
    · rw [curvatureConstant_missing k g m pi hu]
      exact hnone.symm
  simp only [not_or] at hu
  obtain ⟨hS', h0, h1, h2⟩ := hu
  obtain ⟨α, rfl⟩ := Option.ne_none_iff_exists'.1 h0
  obtain ⟨β, rfl⟩ := Option.ne_none_iff_exists'.1 h1
  obtain ⟨c, rfl⟩ := Option.ne_none_iff_exists'.1 h2
  have hne : c ≠ 0 := hN c rfl
  have hg' := hval α β c hS' rfl rfl rfl
  have hσ : scaleReal S ≠ 0 := by
    rcases S with _ | _ | s
    · simp [scaleReal]
    · exact absurd rfl hS'
    · exact hS s rfl
  obtain ⟨hlit, hpos⟩ := curvature_literals α β hne hk hg hm hpi
  have hH : h = some ((-1 / 2 : ℝ)) := by rw [hh]; simp [Numeric.denote]
  have hM : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  rcases b with _ | u
  · rw [show partialIntegral volume (fun x => Value.mask (compare strict (some x) none) (v x)) =
        none from if_neg fun hd => by
          obtain ⟨r, hr⟩ := hd.1 0
          cases strict <;> cases hr]
    have : Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply (Value.mul m (some c)))
        (Value.add (Value.mul (Value.mul h (Value.inv (some c))) (some β)) (Value.mul m none))) =
        none := by
      rw [hM]
      cases Functions.sqrtR.apply (Value.mul (some (-1 : ℝ)) (some c)) <;>
        cases Value.mul (Value.mul h (Value.inv (some c))) (some β) <;> rfl
    rw [this]
    cases curvatureConstant (some α) (some β) (some c) k g m pi <;> exact hnone.symm
  have hcmp : ∀ x : ℝ, x < u → compare strict (some x) (some u) = some true := fun x hx => by
    cases strict <;> simp [compare, Value.lt, Value.le, hx, hx.le]
  rcases lt_or_gt_of_ne hne with hc | hc
  · obtain ⟨hK, hR⟩ := hlit hc
    have hI : ∀ u' : ℝ, IntegrableOn
        (fun x : ℝ => scaleReal S * (κ * Real.exp (α + β * x + c * x ^ 2))) (Iic u') volume :=
      fun u' => (((gaussian_integrable α β c hc).integrableOn.const_mul _).const_mul _)
    rw [upper_integral strict (some u) ⟨fun _ => rfl⟩
      (UpperTerms.value hg' hI (fun h => by cases h) fun u' hu' => by
        cases hu'
        rfl)]
    rw [integral_const_mul, integral_const_mul, gauss_Iic α β hc u, hK, hR, hH]
    have harg : Value.mul (some (√(-1 * c)))
        (Value.add (Value.mul (Value.mul (some (-1 / 2 : ℝ)) (Value.inv (some c))) (some β))
          (Value.mul m (some u))) = some (√(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * u)) := by
      rw [hM]
      simp [Value.mul, Value.add, Value.inv, hne]
    rw [harg, erfc_apply]
    rcases S with _ | _ | s
    · simp only [scaleBy, scaleReal, Value.mul, Option.some.injEq]
      linear_combination (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹)) *
        Functions.erfcR.value (√(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * u))) * (-hhalf) / 2
    · exact absurd rfl hS'
    · simp only [scaleBy, scaleReal, Value.mul, Option.some.injEq]
      linear_combination (s * (Real.exp (α + -1 / 4 * c⁻¹ * (β * β)) * √(Real.pi * (-1 * c⁻¹)) *
        Functions.erfcR.value (√(-1 * c) * (-1 / 2 * c⁻¹ * β + -1 * u)))) * (-hhalf) / 2
  · have hn : partialIntegral volume
        (fun x => Value.mask (compare strict (some x) (some u)) (v x)) = none := by
      apply if_neg
      rintro ⟨_, hint⟩
      have hon : IntegrableOn (fun x : ℝ => scaleReal S * κ * Real.exp (α + β * x + c * x ^ 2))
          (Iio u) volume := by
        refine (hint.integrableOn (s := Iio u)).congr_fun (fun x hx => ?_) measurableSet_Iio
        show (Value.mask (compare strict (some x) (some u)) (v x)).getD 0 = _
        rw [hcmp x hx, hg']
        show scaleReal S * (κ * Real.exp (α + β * x + c * x ^ 2)) = _
        ring
      exact exp_quadratic_not_integrableOn_Iic α β hc u (mul_ne_zero hσ hκ)
        (integrableOn_Iic_iff_integrableOn_Iio.2 hon)
    rw [hn, hpos hc]
    exact hnone.symm

/-- The same under a scale that may vanish: zero where the scale is, under its
mask, after the scale, the bound and the coefficients of the exponent. -/
theorem curvature_above_masked (strict : Bool) {a : Option ℝ} {v : ℝ → Option ℝ} {s : Option ℝ}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ half : ℚ)
    (hv : Bell v (some s) none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (hP : curvatureHalfCheck P κ half = true) (hN : Nonvanishing c2)
    {k g m h pi : Option ℝ} (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hh : h = some (Numeric.denote (s := .real) (1 / 2 : ℚ))) (hpi : pi = some Functions.pi) :
    partialIntegral volume (fun x => Value.mask (compare strict a (some x)) (v x)) =
      after [s, a, c0, c1, c2] (Value.mask (Value.nonzero s)
        (Value.mul s (Value.mul (curvatureConstant c0 c1 c2 k g m pi)
          (Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply (Value.mul m c2))
            (Value.add a (Value.mul (Value.mul h (Value.inv c2)) c1))))))) := by
  obtain ⟨_, _, hmiss, hval⟩ := curvature_value hv hE hP
  rcases s with _ | σ
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
  · rw [above_undefined strict (some l) (hmiss (Or.inr (Or.inr (Or.inl rfl))))]
    rfl
  rcases c2 with _ | c
  · rw [above_undefined strict (some l) (hmiss (Or.inr (Or.inr (Or.inr rfl))))]
    rfl
  show _ = Value.mask (Value.nonzero (some σ)) _
  by_cases hs : σ = 0
  · subst hs
    rw [partialIntegral_zero fun x => by
      rw [hval α β c (by simp) rfl rfl rfl x]
      cases hcmp : compare strict (some l) (some x) with
      | none => cases strict <;> simp [compare, Value.lt, Value.le] at hcmp
      | some t => cases t <;> simp [Value.mask, scaleReal]]
    simp [Value.nonzero, Value.mask]
  · rw [curvature_above strict κ half hv hE hP (fun t ht => by cases ht; exact hs) hN hk hg hm hh
      hpi]
    simp [Value.nonzero, hs, Value.mask, scaleBy]

theorem curvature_below_masked (strict : Bool) {b : Option ℝ} {v : ℝ → Option ℝ} {s : Option ℝ}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ half : ℚ)
    (hv : Bell v (some s) none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (hP : curvatureHalfCheck P κ half = true) (hN : Nonvanishing c2)
    {k g m h pi : Option ℝ} (hk : k = some (Numeric.denote (s := .real) half))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hh : h = some (Numeric.denote (s := .real) (-1 / 2 : ℚ))) (hpi : pi = some Functions.pi) :
    partialIntegral volume (fun x => Value.mask (compare strict (some x) b) (v x)) =
      after [s, b, c0, c1, c2] (Value.mask (Value.nonzero s)
        (Value.mul s (Value.mul (curvatureConstant c0 c1 c2 k g m pi)
          (Functions.erfcR.apply (Value.mul (Functions.sqrtR.apply (Value.mul m c2))
            (Value.add (Value.mul (Value.mul h (Value.inv c2)) c1) (Value.mul m b))))))) := by
  obtain ⟨_, _, hmiss, hval⟩ := curvature_value hv hE hP
  rcases s with _ | σ
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
  · rw [below_undefined strict (some u) (hmiss (Or.inr (Or.inr (Or.inl rfl))))]
    rfl
  rcases c2 with _ | c
  · rw [below_undefined strict (some u) (hmiss (Or.inr (Or.inr (Or.inr rfl))))]
    rfl
  show _ = Value.mask (Value.nonzero (some σ)) _
  by_cases hs : σ = 0
  · subst hs
    rw [partialIntegral_zero fun x => by
      rw [hval α β c (by simp) rfl rfl rfl x]
      cases hcmp : compare strict (some x) (some u) with
      | none => cases strict <;> simp [compare, Value.lt, Value.le] at hcmp
      | some t => cases t <;> simp [Value.mask, scaleReal]]
    simp [Value.nonzero, Value.mask]
  · rw [curvature_below strict κ half hv hE hP (fun t ht => by cases ht; exact hs) hN hk hg hm hh
      hpi]
    simp [Value.nonzero, hs, Value.mask, scaleBy]

end QSym.Distribution.StepSource
