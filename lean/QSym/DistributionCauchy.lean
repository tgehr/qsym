import QSym.DistributionMissingPoint
import QSym.IntegrationLaws
import QSym.DistributionInterval
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Integrals of reciprocals of quadratics without real roots. The sign of
the leading coefficient is retained for signed weights. -/
noncomputable section
namespace QSym.Distribution.StepSource
open MeasureTheory Set Filter

private def kernel (x : ℝ) := (1 + x^2)⁻¹

private theorem quadratic_nonzero {a b c k : ℝ} (hk : 0 < k) (key : k = a*c - b^2) (x : ℝ) :
    c + 2*b*x + a*x^2 ≠ 0 := by
  intro zero
  have h : a*(c+2*b*x+a*x^2) = (a*x+b)^2+k := by rw [key]; ring
  rw [zero, mul_zero] at h
  linarith [sq_nonneg (a*x+b)]

private theorem quadratic_kernel {a b c k : ℝ} (ha : a ≠ 0) (hk : 0 < k)
    (he : k = a*c - b^2) (x : ℝ) :
    (c + 2*b*x + a*x^2)⁻¹ = (a/k) * kernel (a/√k*x + b/√k) := by
  have hw := (Real.sqrt_pos.2 hk).ne'
  have sq := Real.sq_sqrt hk.le
  have completed : (1 + (a/√k*x + b/√k)^2) * k = a * (c + 2*b*x + a*x^2) := by
    calc
      _ = k + (a*x+b)^2 := by
        conv_lhs => rw [← sq]
        field_simp [hw]
      _ = _ := by rw [he]; ring
  have eq : c + 2*b*x + a*x^2 = (k/a) * (1 + (a/√k*x + b/√k)^2) := by
    apply mul_left_cancel₀ ha
    rw [← completed]
    field_simp [ha]
    ring
  rw [eq, kernel, mul_inv_rev, inv_div, mul_comm]

private theorem quadratic_integral {a b c k : ℝ} (ha : a ≠ 0) (hk : 0 < k)
    (he : k = a*c - b^2) :
    Integrable (fun x : ℝ => (c + 2*b*x + a*x^2)⁻¹) ∧
      (∫ x : ℝ, (c + 2*b*x + a*x^2)⁻¹) = (a/|a|) * Real.pi / √k := by
  have hw := Real.sqrt_pos.2 hk
  have shifted : Integrable (fun x : ℝ => kernel (x + b/√k)) := by
    simpa only [kernel, sub_neg_eq_add] using integrable_inv_one_add_sq.comp_sub_right (-(b/√k))
  have scaled := shifted.comp_mul_left' (div_ne_zero ha hw.ne')
  simp_rw [quadratic_kernel ha hk he]
  refine ⟨scaled.const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ => kernel (x + b/√k)),
    integral_add_right_eq_self, smul_eq_mul]
  change a/k * (|(a / √k)⁻¹| * (∫ x : ℝ, (1 + x^2)⁻¹)) = _
  rw [integral_univ_inv_one_add_sq, abs_inv, abs_div, abs_of_pos hw]
  field_simp [ha, hw.ne', (abs_pos.mpr ha).ne', hk.ne']
  linear_combination a * Real.pi * |a| * (Real.sq_sqrt hk.le)

/-- Source check for the denominator, the completed square and the sign of
the resulting integral. Coefficients may have trailing zeroes. -/
def cauchyCheck (p : List ℚ) (c b a k s : ℚ) : Bool :=
  polyZero (polyAdd p (polyScale (-1) [c, 2*b, a])) &&
    decide (a ≠ 0 ∧ 0 < k ∧ k = a*c - b^2 ∧ s * |a| = a)

theorem cauchy_mass {f : ℝ → Option ℝ} {p : List ℚ} (c b a k s : ℚ)
    (src : PolynomialOn (fun _ => True) f p) (check : cauchyCheck p c b a k s = true)
    {sign pi disc : Option ℝ} (hs : sign = some (Numeric.denote (s := .real) s))
    (hpi : pi = some Functions.pi) (hk : disc = some (Numeric.denote (s := .real) k)) :
    massValue (weightValue (some fun x => Value.inv (f x)) lebesgueValue) =
      Value.mul (Value.mul sign pi) (Value.inv (Functions.sqrtR.apply disc)) := by
  simp only [cauchyCheck, Bool.and_eq_true, decide_eq_true_eq] at check
  obtain ⟨coeff, ha, pos, he, sg⟩ := check
  have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hp : (0 : ℝ) < k := by exact_mod_cast pos
  have key : (k : ℝ) = a*c - b^2 := by exact_mod_cast he
  have hsg : (s : ℝ) * |(a : ℝ)| = a := by exact_mod_cast sg
  let q := fun x : ℝ => (c : ℝ) + 2*b*x + a*x^2
  have eq (x : ℝ) : f x = some (q x) := quadratic_source c b a src coeff x
  have total (x : ℝ) : Value.inv (f x) = some ((q x)⁻¹) := by
    have nz : q x ≠ 0 := quadratic_nonzero hp key x
    rw [eq x]
    simp [Value.inv, nz]
  obtain ⟨hi, hv⟩ := quadratic_integral hn hp key
  have vals : (fun x => (Value.inv (f x)).getD 0) = fun x => (q x)⁻¹ :=
    funext fun x => by rw [total]; rfl
  rw [weighted_lebesgue_mass_bridge, Model.densityMassValue_eq]
  change partialIntegral volume (fun x => Value.inv (f x)) = _
  rw [partialIntegral_valid _ _ (fun x => ⟨_, total x⟩) (by rw [vals]; exact hi), vals]
  change some (∫ x : ℝ, ((c : ℝ) + 2*b*x + a*x^2)⁻¹) = _
  rw [hv, hs, hpi, hk]
  change some (((a : ℝ) / |(a : ℝ)|) * Real.pi / √(k : ℝ)) =
    Value.mul (Value.mul (some (s : ℝ)) (some Real.pi)) (Value.inv (Functions.sqrtR.apply (some (k : ℝ))))
  rw [← (eq_div_iff (abs_ne_zero.mpr hn)).mpr hsg]
  simp [Function1.apply, Functions.sqrtR, Value.mul, Value.inv, hp.le, (Real.sqrt_pos.2 hp).ne', div_eq_mul_inv]

/-- A scalar may be partial or zero. A finite inner mass lets either order
of strict multiplication move outside the integral. -/
theorem factor_finite_mass {f : ℝ → Option ℝ} {out : Option ℝ} (c : Option ℝ) (right : Bool)
    (mass : massValue (weightValue (some f) lebesgueValue) = out) (finite : Value.Defined out) :
    massValue (weightValue (some fun x => if right then Value.mul (f x) c else Value.mul c (f x))
      lebesgueValue) = Value.mul c out := by
  rw [weighted_lebesgue_mass_bridge, Model.densityMassValue_eq] at mass ⊢
  change partialIntegral volume f = out at mass
  subst out
  have order (x : ℝ) : (if right then Value.mul (f x) c else Value.mul c (f x)) = Value.mul c (f x) := by
    cases right <;> cases c <;> cases f x <;> simp [Value.mul, mul_comm]
  change partialIntegral volume (fun x => if right then _ else _) = _
  simp_rw [order]
  cases c with
  | none => simp [Value.mul, partialIntegral, Value.Defined]
  | some v => exact partialIntegral_scale_defined volume v f finite

theorem cauchy_scaled_mass {f : ℝ → Option ℝ} {p : List ℚ} (scale : Option ℝ) (right : Bool)
    (c b a k s : ℚ) (src : PolynomialOn (fun _ => True) f p) (check : cauchyCheck p c b a k s = true)
    {sign pi disc : Option ℝ} (hs : sign = some (Numeric.denote (s := .real) s))
    (hpi : pi = some Functions.pi) (hk : disc = some (Numeric.denote (s := .real) k)) :
    massValue (weightValue (some fun x => if right then Value.mul (Value.inv (f x)) scale
      else Value.mul scale (Value.inv (f x))) lebesgueValue) =
      Value.mul scale (Value.mul (Value.mul sign pi) (Value.inv (Functions.sqrtR.apply disc))) := by
  apply factor_finite_mass scale right (cauchy_mass c b a k s src check hs hpi hk)
  simp only [cauchyCheck, Bool.and_eq_true, decide_eq_true_eq] at check
  have hp : (0 : ℝ) < k := by exact_mod_cast check.2.2.1
  rw [hs, hpi, hk]
  change Value.Defined (Value.mul (Value.mul (some (s : ℝ)) (some Real.pi))
    (Value.inv (Functions.sqrtR.apply (some (k : ℝ)))))
  simp [Value.Defined, Value.mul, Value.inv, Function1.apply, Functions.sqrtR, hp.le, (Real.sqrt_pos.2 hp).ne']

/-- The antiderivative used at either partial endpoint of a root-free
reciprocal quadratic. The sign comes from the slope of the arctangent. -/
def cauchyPrimitive (a b k t : Option ℝ) : Option ℝ :=
  let w := Value.inv (Functions.sqrtR.apply k)
  Value.mul w (Functions.atanR.apply (Value.mul w (Value.add (Value.mul a t) b)))

private def primitiveReal (a b k x : ℝ) : ℝ := (√k)⁻¹ * Real.arctan ((a*x+b)/√k)

private theorem primitiveReal_deriv {a b c k : ℝ} (ha : a ≠ 0) (hk : 0 < k) (he : k = a*c-b^2) (x : ℝ) :
    HasDerivAt (primitiveReal a b k) ((c + 2*b*x + a*x^2)⁻¹) x := by
  have arg : HasDerivAt (fun t : ℝ => (a*t+b)/√k) (a/√k) x := by
    simpa using (((hasDerivAt_id x).const_mul a).add_const b).div_const (√k)
  have d := ((Real.hasDerivAt_arctan' _).comp x arg).const_mul ((√k)⁻¹)
  have hw := (Real.sqrt_pos.2 hk).ne'
  have width : (√k)⁻¹*(a/√k) = a/k := by
    field_simp [hw, hk.ne']
  have rearrange : (a*x+b)/√k = a/√k*x+b/√k := by ring
  have slope : (√k)⁻¹ * ((1+((a*x+b)/√k)^2)⁻¹ * (a/√k)) = (c+2*b*x+a*x^2)⁻¹ := by
    rw [quadratic_kernel ha hk he x, rearrange]
    unfold kernel
    rw [← width]
    ring
  simpa only [primitiveReal, slope, Function.comp_def] using d

private theorem cauchy_calculus {f p} (c b a k : ℚ)
    (src : PolynomialOn (fun _ => True) f p)
    (shape : polyZero (polyAdd p (polyScale (-1) [c, 2*b, a])) = true)
    (check : decide (a ≠ 0 ∧ 0 < k ∧ k = a*c-b^2) = true) {A B K : Option ℝ}
    (hA : A = some (Numeric.denote (s := .real) a)) (hB : B = some (Numeric.denote (s := .real) b))
    (hK : K = some (Numeric.denote (s := .real) k)) :
    let g := fun x : ℝ => ((c : ℝ)+2*b*x+a*x^2)⁻¹
    (∀ x, Value.inv (f x) = some (g x)) ∧
    (∀ t, cauchyPrimitive A B K (some t) = some (primitiveReal a b k t)) ∧ Continuous g ∧
    ∀ x, HasDerivAt (primitiveReal a b k) (g x) x := by
  obtain ⟨ha, hk, he⟩ := of_decide_eq_true check
  have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hp : 0 < (k : ℝ) := by exact_mod_cast hk
  have key : (k : ℝ) = a*c-b^2 := by exact_mod_cast he
  have nz := quadratic_nonzero hp key
  refine ⟨fun x => ?_, fun t => ?_, ?_, primitiveReal_deriv hn hp key⟩
  · rw [quadratic_source c b a src shape x]
    simp [Value.inv, nz x]
  · rw [hA, hB, hK]
    change cauchyPrimitive (some (a : ℝ)) (some (b : ℝ)) (some (k : ℝ)) (some t) = _
    simp [cauchyPrimitive, primitiveReal, Value.inv, Value.mul, Value.add, Function1.apply,
      Functions.sqrtR, Functions.atanR, hp.le, (Real.sqrt_pos.2 hp).ne', div_eq_mul_inv, mul_comm]
  · exact (by fun_prop : Continuous (fun x : ℝ => (c : ℝ)+2*b*x+a*x^2)).inv₀ nz

theorem IntervalTerms.cauchy {f p} (c b a k : ℚ) {l u m A B K : Option ℝ}
    (src : PolynomialOn (fun _ => True) f p)
    (shape : polyZero (polyAdd p (polyScale (-1) [c, 2*b, a])) = true)
    (check : decide (a ≠ 0 ∧ 0 < k ∧ k = a*c-b^2) = true)
    (hA : A = some (Numeric.denote (s := .real) a)) (hB : B = some (Numeric.denote (s := .real) b))
    (hK : K = some (Numeric.denote (s := .real) k)) :
    IntervalTerms l u m (fun x => Value.inv (f x))
      (Value.add (cauchyPrimitive A B K u) (Value.mul m (cauchyPrimitive A B K l))) := by
  obtain ⟨v, endpoints, cont, deriv⟩ := cauchy_calculus c b a k src shape check hA hB hK
  exact .primitive v endpoints cont deriv

theorem IntervalTerms.cauchy_scaled {f p} (scale : Option ℝ) (right : Bool) (c b a k : ℚ) {l u m A B K : Option ℝ}
    (src : PolynomialOn (fun _ => True) f p)
    (shape : polyZero (polyAdd p (polyScale (-1) [c, 2*b, a])) = true)
    (check : decide (a ≠ 0 ∧ 0 < k ∧ k = a*c-b^2) = true)
    (hA : A = some (Numeric.denote (s := .real) a)) (hB : B = some (Numeric.denote (s := .real) b))
    (hK : K = some (Numeric.denote (s := .real) k)) :
    IntervalTerms l u m (fun x => if right then Value.mul (Value.inv (f x)) scale else Value.mul scale (Value.inv (f x)))
      (Value.mul scale (Value.add (cauchyPrimitive A B K u) (Value.mul m (cauchyPrimitive A B K l)))) := by
  obtain ⟨v, endpoints, cont, deriv⟩ := cauchy_calculus c b a k src shape check hA hB hK
  apply IntervalTerms.scaledPrimitive (c := scale) _ endpoints cont deriv
  intro x
  rw [v x]
  cases scale <;> cases right <;> simp [Value.mul, mul_comm]

end QSym.Distribution.StepSource
