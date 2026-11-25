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

end QSym.Distribution.StepSource
