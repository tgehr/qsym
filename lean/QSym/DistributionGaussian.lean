import QSym.LimitExponential
import QSym.DistributionInterval
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace QSym.Distribution.StepSource
open MeasureTheory Filter Topology
open QSym.Limit

/-- `R·exp(Q)` is an antiderivative of `(P - κ)·exp(Q)`: `P = R' + Q'·R + κ`. -/
def gaussPrimitive (R P Q : List ℚ) (κ : ℚ) : Bool :=
  polyZero (polyAdd (polyAdd (polyDerivative R) (polyMul (polyDerivative Q) R))
    (polyAdd [κ] (polyScale (-1) P)))

theorem gaussPrimitive_deriv {R P Q : List ℚ} {κ : ℚ} (h : gaussPrimitive R P Q κ = true)
    (x : ℝ) : HasDerivAt (fun y => polyEval R y * Real.exp (polyEval Q y))
      ((polyEval P x - κ) * Real.exp (polyEval Q x)) x := by
  have hz := polyEval_zero h x
  rw [polyEval_add, polyEval_add, polyEval_add, polyEval_mul, polyEval_scale] at hz
  simp only [polyEval, Rat.cast_neg, Rat.cast_one, mul_zero, add_zero] at hz
  have he : polyEval (polyDerivative R) x + polyEval (polyDerivative Q) x * polyEval R x =
      polyEval P x - κ := by linarith
  have hd := (polyEval_hasDerivAt R x).mul ((polyEval_hasDerivAt Q x).exp)
  convert hd using 1
  rw [← he]
  ring

/-- The exponent is this quadratic with negative leading coefficient. -/
def quadratic (Q : List ℚ) (c0 c1 c2 : ℚ) : Bool :=
  decide (c2 < 0) && polyZero (polyAdd Q (polyScale (-1) [c0, c1, c2]))

theorem quadratic_eval {Q : List ℚ} {c0 c1 c2 : ℚ} (h : quadratic Q c0 c1 c2 = true) (x : ℝ) :
    polyEval Q x = c0 + c1 * x + c2 * x ^ 2 := by
  simp only [quadratic, Bool.and_eq_true, decide_eq_true_eq] at h
  have hz := polyEval_zero h.2 x
  rw [polyEval_add, polyEval_scale] at hz
  simp only [polyEval, Rat.cast_neg, Rat.cast_one, mul_zero, add_zero] at hz
  linarith

theorem gaussian_integrable (c0 c1 c2 : ℝ) (h : c2 < 0) :
    Integrable fun x : ℝ => Real.exp (c0 + c1 * x + c2 * x ^ 2) := by
  have hb : 0 < -c2 := by linarith
  have hi := ((integrable_exp_neg_mul_sq hb).comp_sub_right (c1 / (2 * -c2))).const_mul
    (Real.exp (c0 - c1 ^ 2 / (4 * c2)))
  refine hi.congr (Eventually.of_forall fun x => ?_)
  show Real.exp (c0 - c1 ^ 2 / (4 * c2)) * Real.exp (- -c2 * (x - c1 / (2 * -c2)) ^ 2) = _
  rw [← Real.exp_add]
  congr 1
  have hc : c2 ≠ 0 := h.ne
  field_simp
  ring

theorem gaussian_integral (c0 c1 c2 : ℝ) (h : c2 < 0) :
    ∫ x : ℝ, Real.exp (c0 + c1 * x + c2 * x ^ 2) =
      Real.exp (c0 - c1 ^ 2 / (4 * c2)) * √(Real.pi / (-c2)) := by
  have hb : 0 < -c2 := by linarith
  have he : (fun x : ℝ => Real.exp (c0 + c1 * x + c2 * x ^ 2)) = fun x =>
      Real.exp (c0 - c1 ^ 2 / (4 * c2)) * Real.exp (- -c2 * (x - c1 / (2 * -c2)) ^ 2) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    have hc : c2 ≠ 0 := h.ne
    field_simp
    ring
  rw [he, integral_const_mul,
    integral_sub_right_eq_self (fun y : ℝ => Real.exp (- -c2 * y ^ 2)) (c1 / (2 * -c2)),
    integral_gaussian]

private theorem vanishes_quadratic (top : Bool) (p : List ℚ) {c0 c1 c2 : ℚ} (h : c2 < 0) :
    Vanishes (if top then atTop else atBot) p [c0, c1, c2] := by
  cases top
  · refine decays_atBot 1 2 ?_
    simp [descends, polyAdd, polyZero, h]
  · refine decays_atTop (-1) 2 ?_
    simp [descends, polyAdd, polyZero, h]

/-- A continuous function that vanishes at both ends is bounded. -/
private theorem bounded_of_vanishing {g : ℝ → ℝ} (hc : Continuous g)
    (ht : Tendsto g atTop (𝓝 0)) (hb : Tendsto g atBot (𝓝 0)) : ∃ M, ∀ x, |g x| ≤ M := by
  obtain ⟨A, hA⟩ := (ht.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)).exists_forall_of_atTop
  obtain ⟨B, hB⟩ := (hb.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)).exists_forall_of_atBot
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := B) (b := A)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc B A
  · exact le_trans (by simpa using hC x hx) (le_max_left _ _)
  · have h1 : |g x| < 1 := by
      rcases not_and_or.1 hx with h | h
      · simpa [Real.dist_eq] using hB x (le_of_not_le h)
      · simpa [Real.dist_eq] using hA x (le_of_not_le h)
    exact le_trans h1.le (le_max_right _ _)

theorem gaussian_polynomial_integrable (p : List ℚ) {c0 c1 c2 : ℚ} (h : c2 < 0) :
    Integrable fun x : ℝ => polyEval p x * Real.exp (c0 + c1 * x + c2 * x ^ 2) := by
  have hh : c2 / 2 < 0 := by linarith
  have hR : ((c2 / 2 : ℚ) : ℝ) < 0 := by exact_mod_cast hh
  have hv := fun top => vanishes_quadratic top p (c0 := c0 / 2) (c1 := c1 / 2) hh
  have heval : ∀ x : ℝ, polyEval [c0 / 2, c1 / 2, c2 / 2] x =
      (c0 / 2 : ℚ) + (c1 / 2 : ℚ) * x + (c2 / 2 : ℚ) * x ^ 2 := fun x => by
    simp [polyEval]; ring
  have hcont : Continuous fun x : ℝ => polyEval p x * Real.exp (polyEval [c0 / 2, c1 / 2, c2 / 2] x) :=
    (polyEval_continuous p).mul (Real.continuous_exp.comp (polyEval_continuous _))
  obtain ⟨M, hM⟩ := bounded_of_vanishing hcont (hv true) (hv false)
  have hi := (gaussian_integrable ((c0 / 2 : ℚ) : ℝ) ((c1 / 2 : ℚ) : ℝ) ((c2 / 2 : ℚ) : ℝ) hR).const_mul M
  refine hi.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((polyEval_continuous p).mul (Real.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · have hs : Real.exp (c0 + c1 * x + c2 * x ^ 2) =
        Real.exp (polyEval [c0 / 2, c1 / 2, c2 / 2] x) *
          Real.exp ((c0 / 2 : ℚ) + (c1 / 2 : ℚ) * x + (c2 / 2 : ℚ) * x ^ 2) := by
      rw [heval, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hs, ← mul_assoc, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hM x) (Real.exp_pos _).le

/-- The integral of a polynomial times the exponential of a quadratic: the
polynomial is a constant up to a derivative that vanishes at both ends. -/
theorem gaussian_polynomial_integral {P R Q : List ℚ} {κ c0 c1 c2 : ℚ}
    (hq : quadratic Q c0 c1 c2 = true) (hp : gaussPrimitive R P Q κ = true) :
    Integrable (fun x : ℝ => polyEval P x * Real.exp (polyEval Q x)) ∧
      ∫ x : ℝ, polyEval P x * Real.exp (polyEval Q x) =
        κ * (Real.exp (c0 - c1 ^ 2 / (4 * c2)) * √(Real.pi / (-c2))) := by
  have hc2 : c2 < 0 := by
    simp only [quadratic, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.1
  have hcR : ((c2 : ℚ) : ℝ) < 0 := by exact_mod_cast hc2
  have hQ : ∀ x : ℝ, polyEval Q x = c0 + c1 * x + c2 * x ^ 2 := quadratic_eval hq
  have hL : ∀ x : ℝ, polyEval [c0, c1, c2] x = c0 + c1 * x + c2 * x ^ 2 := fun x => by
    simp [polyEval]; ring
  have hfun : ∀ p : List ℚ, (fun x : ℝ => polyEval p x * Real.exp (polyEval Q x)) =
      fun x => polyEval p x * Real.exp (c0 + c1 * x + c2 * x ^ 2) := fun p => by
    funext x; rw [hQ]
  have hE : (fun x : ℝ => Real.exp (polyEval Q x)) =
      fun x => Real.exp (c0 + c1 * x + c2 * x ^ 2) := by funext x; rw [hQ]
  have hPi : Integrable fun x : ℝ => polyEval P x * Real.exp (polyEval Q x) := by
    rw [hfun]; exact gaussian_polynomial_integrable P hc2
  have hEi : Integrable fun x : ℝ => Real.exp (polyEval Q x) := by
    rw [hE]; exact gaussian_integrable _ _ _ hcR
  have hDi : Integrable fun x : ℝ => (polyEval P x - κ) * Real.exp (polyEval Q x) := by
    have h := hPi.sub (hEi.const_mul (κ : ℝ))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hlim : ∀ top : Bool, Tendsto (fun x : ℝ => polyEval R x * Real.exp (polyEval Q x))
      (if top then atTop else atBot) (𝓝 0) := fun top => by
    have h := vanishes_quadratic top R (c0 := c0) (c1 := c1) hc2
    unfold Vanishes at h
    simp only [hL] at h
    rw [hfun]
    exact h
  have hzero := integral_of_hasDerivAt_of_tendsto (gaussPrimitive_deriv hp) hDi (hlim false)
    (hlim true)
  refine ⟨hPi, ?_⟩
  have hsplit : (fun x : ℝ => polyEval P x * Real.exp (polyEval Q x)) = fun x =>
      (polyEval P x - κ) * Real.exp (polyEval Q x) + κ * Real.exp (polyEval Q x) := by
    funext x; ring
  rw [hsplit, integral_add hDi (hEi.const_mul _), hzero, integral_const_mul, hE,
    gaussian_integral _ _ _ hcR]
  simp

/-- The checks of a Gaussian integral: the exponent is a quadratic that
descends, the polynomial is `κ` up to a derivative, and `γ`, `δ` are the
exponent at its vertex and the reciprocal of its curvature. -/
def gaussianCheck (R P Q : List ℚ) (κ c0 c1 c2 γ δ : ℚ) : Bool :=
  quadratic Q c0 c1 c2 && gaussPrimitive R P Q κ &&
    decide (γ * (4 * c2) = 4 * c0 * c2 - c1 ^ 2) && decide (δ * c2 = -1)

private theorem gaussian_value {R P Q : List ℚ} {κ c0 c1 c2 γ δ : ℚ}
    (h : gaussianCheck R P Q κ c0 c1 c2 γ δ = true) {k g d pi : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) κ)) (hg : g = some (Numeric.denote (s := .real) γ))
    (hd : d = some (Numeric.denote (s := .real) δ)) (hpi : pi = some Functions.pi) :
    Integrable (fun x : ℝ => polyEval P x * Real.exp (polyEval Q x)) ∧
      Value.mul k (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))) =
        some (∫ x : ℝ, polyEval P x * Real.exp (polyEval Q x)) := by
  simp only [gaussianCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hq, hp⟩, hγ⟩, hδ⟩ := h
  have hc2 : c2 < 0 := by
    simp only [quadratic, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.1
  have hcR : ((c2 : ℚ) : ℝ) < 0 := by exact_mod_cast hc2
  have hγR : (γ : ℝ) * (4 * c2) = 4 * c0 * c2 - c1 ^ 2 := by exact_mod_cast hγ
  have hδR : (δ : ℝ) * c2 = -1 := by exact_mod_cast hδ
  obtain ⟨hi, hv⟩ := gaussian_polynomial_integral hq hp
  refine ⟨hi, ?_⟩
  have hc : ((c2 : ℚ) : ℝ) ≠ 0 := hcR.ne
  have hγ' : (c0 : ℝ) - c1 ^ 2 / (4 * c2) = γ := by
    field_simp
    linarith
  have hδ' : Real.pi / (-(c2 : ℝ)) = Real.pi * δ := by
    have : (δ : ℝ) = 1 / (-c2) := by
      rw [eq_div_iff (neg_ne_zero.2 hc)]
      linarith
    rw [this]; ring
  have hpos : 0 ≤ Real.pi * (δ : ℝ) := by
    rw [← hδ']
    exact div_nonneg Real.pi_pos.le (by linarith)
  rw [hv, hγ', hδ', hk, hg, hd, hpi]
  simp [Value.mul, Function1.apply, Functions.expR, Functions.sqrtR, Functions.pi, Numeric.denote,
    hpos]

/-- A total integrand that is a polynomial times the exponential of a
quadratic with negative curvature. -/
theorem gaussian_partialIntegral {f : ℝ → Option ℝ} {R P Q : List ℚ} {κ c0 c1 c2 γ δ : ℚ}
    (hf : ∀ x, f x = some (polyEval P x * Real.exp (polyEval Q x)))
    (h : gaussianCheck R P Q κ c0 c1 c2 γ δ = true) {k g d pi : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) κ)) (hg : g = some (Numeric.denote (s := .real) γ))
    (hd : d = some (Numeric.denote (s := .real) δ)) (hpi : pi = some Functions.pi) :
    partialIntegral volume f =
      Value.mul k (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))) := by
  obtain ⟨hi, hv⟩ := gaussian_value h hk hg hd hpi
  have he : (fun x => (f x).getD 0) = fun x => polyEval P x * Real.exp (polyEval Q x) := by
    funext x; rw [hf]; rfl
  rw [hv, partialIntegral_valid volume f (fun x => ⟨_, hf x⟩) (by rw [he]; exact hi), he]

/-- The same under a scale that does not mention the variable: the integral
is the scale times the Gaussian one, and undefined with the scale. -/
theorem gaussian_partialIntegral_scaled {f : ℝ → Option ℝ} {c : Option ℝ} {R P Q : List ℚ}
    {κ c0 c1 c2 γ δ : ℚ}
    (hf : ∀ x, f x = Value.mul c (some (polyEval P x * Real.exp (polyEval Q x))))
    (h : gaussianCheck R P Q κ c0 c1 c2 γ δ = true) {k g d pi : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) κ)) (hg : g = some (Numeric.denote (s := .real) γ))
    (hd : d = some (Numeric.denote (s := .real) δ)) (hpi : pi = some Functions.pi) :
    partialIntegral volume f = Value.mul c
      (Value.mul k (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d)))) := by
  obtain ⟨hi, hv⟩ := gaussian_value h hk hg hd hpi
  rw [hv]
  cases c with
  | none =>
    apply if_neg
    intro hd
    obtain ⟨r, hr⟩ := hd.1 0
    rw [hf] at hr
    cases hr
  | some c =>
    have he : (fun x => (f x).getD 0) = fun x => c * (polyEval P x * Real.exp (polyEval Q x)) := by
      funext x; rw [hf]; rfl
    rw [partialIntegral_valid volume f (fun x => ⟨_, hf x⟩) (by rw [he]; exact hi.const_mul c),
      he, integral_const_mul]
    rfl

end QSym.Distribution.StepSource

namespace QSym.Distribution.DensityProgram
open MeasureTheory QSym.Limit

theorem presentation_mass_gaussian (p : DensityProgram) {R P Q : List ℚ}
    (κ c0 c1 c2 γ δ : ℚ) (hf : EventualExp ⊤ p.density P Q)
    (h : StepSource.gaussianCheck R P Q κ c0 c1 c2 γ δ = true) {k g d pi : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) κ)) (hg : g = some (Numeric.denote (s := .real) γ))
    (hd : d = some (Numeric.denote (s := .real) δ)) (hpi : pi = some Functions.pi) :
    massValue p.presentation =
      Value.mul k (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d))) := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.gaussian_partialIntegral (Filter.eventually_top.1 hf) h hk hg hd hpi

theorem presentation_mass_gaussian_scaled (p : DensityProgram) {c : Option ℝ} {R P Q : List ℚ}
    (κ c0 c1 c2 γ δ : ℚ) (hf : EventualScaled ⊤ p.density c P Q)
    (h : StepSource.gaussianCheck R P Q κ c0 c1 c2 γ δ = true) {k g d pi : Option ℝ}
    (hk : k = some (Numeric.denote (s := .real) κ)) (hg : g = some (Numeric.denote (s := .real) γ))
    (hd : d = some (Numeric.denote (s := .real) δ)) (hpi : pi = some Functions.pi) :
    massValue p.presentation = Value.mul c
      (Value.mul k (Value.mul (Functions.expR.apply g) (Functions.sqrtR.apply (Value.mul pi d)))) := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.gaussian_partialIntegral_scaled (Filter.eventually_top.1 hf) h hk hg hd hpi

end QSym.Distribution.DensityProgram
