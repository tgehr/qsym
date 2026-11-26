import QSym.DistributionNonvanishing
import QSym.DistributionGaussian
import QSym.DistributionSymbolicPolynomial

/-! Gaussian integrals whose exponent has coefficients that do not mention the
variable. The constant and linear coefficients are partial values, the
curvature is a negative rational. By integration by parts the moments of a
polynomial relative to the Gaussian integral are a polynomial in the linear
coefficient; the exponent is a quadratic by its structure. -/
namespace QSym.Distribution.StepSource
open MeasureTheory Filter Topology

/-- A quadratic with negative curvature stays below its vertex. -/
private theorem quadratic_le (c0 b : ℝ) {c2 : ℝ} (h : c2 < 0) (x : ℝ) :
    c0 + b * x + c2 * x ^ 2 ≤ c0 - b ^ 2 / (4 * c2) := by
  have hc : c2 ≠ 0 := h.ne
  have he : c0 + b * x + c2 * x ^ 2 = c0 - b ^ 2 / (4 * c2) + c2 * (x + b / (2 * c2)) ^ 2 := by
    field_simp
    ring
  rw [he]
  have := mul_nonpos_of_nonpos_of_nonneg h.le (sq_nonneg (x + b / (2 * c2)))
  linarith

/-- Every power times the exponential of such a quadratic vanishes at `+∞`. -/
theorem pow_gaussian_atTop (c0 c1 : ℝ) {c2 : ℝ} (h : c2 < 0) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (c0 + c1 * x + c2 * x ^ 2)) atTop (𝓝 0) := by
  have hb := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).abs.const_mul
    (Real.exp (c0 - (c1 + 1) ^ 2 / (4 * c2)))
  rw [abs_zero, mul_zero] at hb
  refine squeeze_zero_norm (fun x => ?_) hb
  have hx : Real.exp (c0 + c1 * x + c2 * x ^ 2) =
      Real.exp (-x) * Real.exp (c0 + (c1 + 1) * x + c2 * x ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hle := Real.exp_le_exp.2 (quadratic_le c0 (c1 + 1) h x)
  rw [Real.norm_eq_abs, hx, ← mul_assoc, abs_mul, abs_of_pos (Real.exp_pos (c0 + (c1 + 1) * x + c2 * x ^ 2)),
    mul_comm]
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

/-- And at `-∞`, by reflection. -/
theorem pow_gaussian_atBot (c0 c1 : ℝ) {c2 : ℝ} (h : c2 < 0) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (c0 + c1 * x + c2 * x ^ 2)) atBot (𝓝 0) := by
  have ht := ((pow_gaussian_atTop c0 (-c1) h n).const_mul ((-1 : ℝ) ^ n)).comp tendsto_neg_atBot_atTop
  rw [mul_zero] at ht
  refine ht.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [← mul_assoc, ← mul_pow]
  congr 2
  · ring
  · ring

/-- So it is integrable: half the exponential bounds the power. -/
theorem pow_gaussian_integrable (c0 c1 : ℝ) {c2 : ℝ} (h : c2 < 0) (n : ℕ) :
    Integrable fun x : ℝ => x ^ n * Real.exp (c0 + c1 * x + c2 * x ^ 2) := by
  have hh : c2 / 2 < 0 := by linarith
  have hcont : Continuous fun x : ℝ => x ^ n * Real.exp (c0 / 2 + c1 / 2 * x + c2 / 2 * x ^ 2) := by
    fun_prop
  obtain ⟨M, hM⟩ := bounded_of_vanishing hcont (pow_gaussian_atTop _ _ hh n)
    (pow_gaussian_atBot _ _ hh n)
  have hi := (gaussian_integrable (c0 / 2) (c1 / 2) (c2 / 2) hh).const_mul M
  have hmeas : Continuous fun x : ℝ => x ^ n * Real.exp (c0 + c1 * x + c2 * x ^ 2) := by fun_prop
  refine hi.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hs : Real.exp (c0 + c1 * x + c2 * x ^ 2) =
      Real.exp (c0 / 2 + c1 / 2 * x + c2 / 2 * x ^ 2) *
        Real.exp (c0 / 2 + c1 / 2 * x + c2 / 2 * x ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hs, ← mul_assoc, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hM x) (Real.exp_pos _).le

/-- Integration by parts: the derivative of a power times the exponential
integrates to zero. -/
theorem pow_gaussian_recurrence (c0 c1 : ℝ) {c2 : ℝ} (h : c2 < 0) (n : ℕ) :
    (n : ℝ) * (∫ x : ℝ, x ^ (n - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
      c1 * (∫ x : ℝ, x ^ n * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
      2 * c2 * (∫ x : ℝ, x ^ (n + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) = 0 := by
  have hI := fun k => pow_gaussian_integrable c0 c1 h k
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ n * Real.exp (c0 + c1 * y + c2 * y ^ 2))
      ((n : ℝ) * (x ^ (n - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
        c1 * (x ^ n * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
        2 * c2 * (x ^ (n + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2))) x := fun x => by
    have hq : HasDerivAt (fun y : ℝ => c0 + c1 * y + c2 * y ^ 2) (c1 + c2 * (2 * x)) x := by
      have h1 := ((hasDerivAt_id x).const_mul c1).const_add c0
      have h2 := ((hasDerivAt_pow 2 x).const_mul c2)
      convert h1.add h2 using 1
      simp
    have hd := (hasDerivAt_pow n x).mul hq.exp
    convert hd using 1
    ring
  have hint : Integrable fun x : ℝ =>
      (n : ℝ) * (x ^ (n - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
        c1 * (x ^ n * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
        2 * c2 * (x ^ (n + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) :=
    (((hI (n - 1)).const_mul _).add ((hI n).const_mul _)).add ((hI (n + 1)).const_mul _)
  have hzero := integral_of_hasDerivAt_of_tendsto hderiv hint (pow_gaussian_atBot c0 c1 h n)
    (pow_gaussian_atTop c0 c1 h n)
  have hA := (hI (n - 1)).const_mul (n : ℝ)
  have hB := (hI n).const_mul c1
  have hC := (hI (n + 1)).const_mul (2 * c2)
  have e1 := integral_add (hA.add hB) hC
  have e2 := integral_add hA hB
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul] at hzero
  linarith

/-- The moments of the exponential of `c₀ + c₁·x + c₂·x²` relative to its
integral, weighted by the coefficients of a polynomial: a polynomial in `c₁`.
The moment of degree `j + 1` is `h·(c₁·μⱼ + j·μⱼ₋₁)` for `h = -1/(2·c₂)`. -/
def gaussMoments (h : ℚ) : List ℚ → ℕ → List ℚ → List ℚ → List ℚ
  | [], _, _, _ => []
  | a :: P, j, μ, μ' =>
    polyAdd (polyScale a μ)
      (gaussMoments h P (j + 1) (polyScale h (polyAdd (polyMul [0, 1] μ) (polyScale j μ'))) μ)

/-- The step of the moments: from degrees `j` and `j - 1` to `j + 1` and `j`. -/
theorem moment_next (c0 c1 : ℝ) {c2 : ℝ} (hc : c2 < 0) {h : ℚ}
    (hh : (h : ℝ) * (2 * c2) = -1) (G : ℝ) (j : ℕ) (μ μ' : List ℚ)
    (h1 : (∫ x : ℝ, x ^ j * Real.exp (c0 + c1 * x + c2 * x ^ 2)) = polyEval μ c1 * G)
    (h2 : (j : ℝ) * (∫ x : ℝ, x ^ (j - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
      j * (polyEval μ' c1 * G)) :
    (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        polyEval (polyScale h (polyAdd (polyMul [0, 1] μ) (polyScale j μ'))) c1 * G ∧
      ((j + 1 : ℕ) : ℝ) * (∫ x : ℝ, x ^ (j + 1 - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        ((j + 1 : ℕ) : ℝ) * (polyEval μ c1 * G) := by
  have hrec := pow_gaussian_recurrence c0 c1 hc j
  refine ⟨?_, by rw [Nat.add_sub_cancel, h1]⟩
  rw [polyEval_scale, polyEval_add, polyEval_mul, polyEval_scale]
  simp only [polyEval, Rat.cast_zero, Rat.cast_one, mul_zero, add_zero, _root_.zero_add,
    mul_one, Rat.cast_natCast]
  have h3 : 2 * c2 * (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
      -((j : ℝ) * (polyEval μ' c1 * G) + c1 * (polyEval μ c1 * G)) := by
    rw [← h1, ← h2]; linarith
  calc (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2))
      = -((h : ℝ) * (2 * c2)) * (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) := by
        rw [hh]; ring
    _ = -(h : ℝ) * (2 * c2 * (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2))) := by
        ring
    _ = _ := by rw [h3]; ring

/-- From the moments of degrees `j` and `j - 1` on, the polynomials `μ`, `μ'`
are the moments relative to the integral `G`, and the list is the integral
of `xʲ` times the polynomial. -/
theorem gaussMoments_integral (c0 c1 : ℝ) {c2 : ℝ} (hc : c2 < 0) {h : ℚ}
    (hh : (h : ℝ) * (2 * c2) = -1) (G : ℝ) :
    ∀ (P : List ℚ) (j : ℕ) (μ μ' : List ℚ),
      (∫ x : ℝ, x ^ j * Real.exp (c0 + c1 * x + c2 * x ^ 2)) = polyEval μ c1 * G →
      (j : ℝ) * (∫ x : ℝ, x ^ (j - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        j * (polyEval μ' c1 * G) →
      Integrable (fun x : ℝ => x ^ j * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) ∧
        (∫ x : ℝ, x ^ j * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
          polyEval (gaussMoments h P j μ μ') c1 * G := by
  intro P
  induction P with
  | nil =>
    intro j μ μ' _ _
    simp [polyEval, gaussMoments]
  | cons a P ih =>
    intro j μ μ' h1 h2
    have hI := pow_gaussian_integrable c0 c1 hc
    obtain ⟨hnext, hprev⟩ := moment_next c0 c1 hc hh G j μ μ' h1 h2
    obtain ⟨hi, hv⟩ := ih (j + 1) _ μ hnext hprev
    have hsplit : (fun x : ℝ => x ^ j * polyEval (a :: P) x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        fun x => (a : ℝ) * (x ^ j * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
          x ^ (j + 1) * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2) := by
      funext x
      simp only [polyEval]
      ring
    refine ⟨by rw [hsplit]; exact ((hI j).const_mul _).add hi, ?_⟩
    rw [hsplit, integral_add ((hI j).const_mul _) hi, integral_const_mul, h1, hv]
    simp only [gaussMoments, polyEval_add, polyEval_scale]
    ring

/-- The integral of a polynomial times the exponential of a quadratic with
real constant and linear coefficients and negative rational curvature. -/
theorem gaussian_moments (c0 c1 : ℝ) {q2 : ℚ} (hc : q2 < 0) (P : List ℚ) :
    Integrable (fun x : ℝ => polyEval P x * Real.exp (c0 + c1 * x + q2 * x ^ 2)) ∧
      (∫ x : ℝ, polyEval P x * Real.exp (c0 + c1 * x + q2 * x ^ 2)) =
        polyEval (gaussMoments (-1 / (2 * q2)) P 0 [1] []) c1 *
          (Real.exp (c0 - c1 ^ 2 / (4 * q2)) * √(Real.pi / (-q2))) := by
  have hcR : ((q2 : ℚ) : ℝ) < 0 := by exact_mod_cast hc
  have hh : (((-1 / (2 * q2) : ℚ)) : ℝ) * (2 * (q2 : ℝ)) = -1 := by
    have hne : (q2 : ℝ) ≠ 0 := hcR.ne
    push_cast
    field_simp
  have h := gaussMoments_integral c0 c1 hcR hh
    (Real.exp (c0 - c1 ^ 2 / (4 * q2)) * √(Real.pi / (-q2))) P 0 [1] []
    (by simp [polyEval, gaussian_integral c0 c1 (q2 : ℝ) hcR]) (by simp)
  simpa using h

/-- The exponential part of a factor; a factor without one has none. -/
noncomputable def expPart : Option (ℝ → Option ℝ) → ℝ → Option ℝ
  | none, _ => some 1
  | some e, x => Functions.expR.apply (e x)

/-- The exponents of two factors add. -/
def joinExp : Option (ℝ → Option ℝ) → Option (ℝ → Option ℝ) → Option (ℝ → Option ℝ)
  | none, e => e
  | some e, none => some e
  | some e, some e' => some fun x => Value.add (e x) (e' x)

/-- A scale that does not mention the axis; a factor without one has none. -/
def scaleBy : Option (Option ℝ) → Option ℝ → Option ℝ
  | none, v => v
  | some c, v => Value.mul c v

/-- The scales of two factors multiply. -/
def joinScale : Option (Option ℝ) → Option (Option ℝ) → Option (Option ℝ)
  | none, s => s
  | some c, none => some c
  | some c, some d => some (Value.mul c d)

/-- The polynomial of a factor whose coefficients do not mention the
variable; a factor without one has none. -/
def symPart : Option (List (Option (Option ℝ))) → ℝ → Option ℝ
  | none, _ => some 1
  | some cs, x => symEval cs x

/-- The polynomials of two factors multiply. -/
def joinSym : Option (List (Option (Option ℝ))) → Option (List (Option (Option ℝ))) →
    Option (List (Option (Option ℝ)))
  | none, a => a
  | some a, none => some a
  | some a, some b => some (symMul a b)

/-- A polynomial that is there has a coefficient. -/
def symPresent : Option (List (Option (Option ℝ))) → Bool
  | none => true
  | some cs => symSupport cs

/-- A factor of a density: a scale, a polynomial whose coefficients do not
mention the variable, a polynomial with rational coefficients and an
exponential, each of which may be absent. -/
structure Bell (v : ℝ → Option ℝ) (S : Option (Option ℝ))
    (A : Option (List (Option (Option ℝ)))) (p : List ℚ) (E : Option (ℝ → Option ℝ)) : Prop where
  equation : ∀ x, v x = scaleBy S
    (Value.mul (Value.mul (symPart A x) (some (polyEval p x))) (expPart E x))
  support : symPresent A = true

/-- Without the first polynomial the factor is the rest. -/
theorem Bell.plain {v : ℝ → Option ℝ} {S : Option (Option ℝ)} {p : List ℚ}
    {E : Option (ℝ → Option ℝ)} (h : Bell v S none p E) (x : ℝ) :
    v x = scaleBy S (Value.mul (some (polyEval p x)) (expPart E x)) := by
  rw [h.equation]
  simp [symPart, Value.mul]

theorem bell_polynomial {v : ℝ → Option ℝ} {p : List ℚ}
    (h : PolynomialOn (fun _ => True) v p) : Bell v none none p none :=
  ⟨fun x => by rw [h.equation x trivial]; simp [scaleBy, symPart, expPart, Value.mul], rfl⟩

theorem bell_exp (g : ℝ → Option ℝ) :
    Bell (fun x => Functions.expR.apply (g x)) none none [1] (some g) :=
  ⟨fun x => by
    show Functions.expR.apply (g x) = _
    cases hg : g x <;>
      simp [scaleBy, symPart, expPart, Value.mul, polyEval, Function1.apply, Functions.expR, hg],
    rfl⟩

theorem bell_constant (c : Option ℝ) : Bell (fun _ => c) (some c) none [1] none :=
  ⟨fun x => by cases c <;> simp [scaleBy, symPart, expPart, Value.mul, polyEval], rfl⟩

/-- A polynomial whose coefficients do not mention the variable. -/
theorem bell_symbolic {v : ℝ → Option ℝ} {cs : List (Option (Option ℝ))} (h : Symbolic v cs) :
    Bell v none (some cs) [1] none :=
  ⟨fun x => by
    rw [h.equation]
    cases hs : symEval cs x <;> simp [scaleBy, symPart, expPart, Value.mul, polyEval, hs],
    h.support⟩

/-- The same factor with the coefficients of that polynomial written out. A
certificate writes them out after a product of two such polynomials. -/
theorem Bell.cast {v : ℝ → Option ℝ} {S : Option (Option ℝ)} {cs : List (Option (Option ℝ))}
    {p : List ℚ} {E : Option (ℝ → Option ℝ)} (ds : List (Option (Option ℝ)))
    (h : Bell v S (some cs) p E) (e : cs = ds) : Bell v S (some ds) p E :=
  e ▸ h

private theorem expPart_join (E E' : Option (ℝ → Option ℝ)) (x : ℝ) :
    expPart (joinExp E E') x = Value.mul (expPart E x) (expPart E' x) := by
  rcases E with _ | e <;> rcases E' with _ | e'
  · simp [joinExp, expPart, Value.mul]
  · cases h : e' x <;> simp [joinExp, expPart, Value.mul, Function1.apply, Functions.expR, h]
  · cases h : e x <;> simp [joinExp, expPart, Value.mul, Function1.apply, Functions.expR, h]
  · cases h : e x <;> cases h' : e' x <;>
      simp [joinExp, expPart, Value.mul, Value.add, Function1.apply, Functions.expR, h, h',
        Real.exp_add]

private theorem scaleBy_join (S S' : Option (Option ℝ)) (a b : Option ℝ) :
    scaleBy (joinScale S S') (Value.mul a b) = Value.mul (scaleBy S a) (scaleBy S' b) := by
  rcases S with _ | c <;> rcases S' with _ | d
  · rfl
  · cases a <;> cases b <;> cases d <;> (simp [joinScale, scaleBy, Value.mul]; first | done | ring)
  · cases a <;> cases b <;> cases c <;> (simp [joinScale, scaleBy, Value.mul]; first | done | ring)
  · cases a <;> cases b <;> cases c <;> cases d <;>
      (simp [joinScale, scaleBy, Value.mul]; first | done | ring)

private theorem symPart_join {A A' : Option (List (Option (Option ℝ)))}
    (hA : symPresent A = true) (hA' : symPresent A' = true) (x : ℝ) :
    symPart (joinSym A A') x = Value.mul (symPart A x) (symPart A' x) := by
  rcases A with _ | a <;> rcases A' with _ | b
  · simp [joinSym, symPart, Value.mul]
  · cases h : symEval b x <;> simp [joinSym, symPart, Value.mul, h]
  · cases h : symEval a x <;> simp [joinSym, symPart, Value.mul, h]
  · exact symEval_mul hA hA' x

/-- Factors multiply part by part. -/
theorem bell_mul {v w : ℝ → Option ℝ} {S S' : Option (Option ℝ)}
    {A A' : Option (List (Option (Option ℝ)))} {p p' : List ℚ} {E E' : Option (ℝ → Option ℝ)}
    (hv : Bell v S A p E) (hw : Bell w S' A' p' E') :
    Bell (fun x => Value.mul (v x) (w x)) (joinScale S S') (joinSym A A') (polyMul p p')
      (joinExp E E') := by
  refine ⟨fun x => ?_, ?_⟩
  · show Value.mul (v x) (w x) = _
    rw [hv.equation, hw.equation, ← scaleBy_join, expPart_join,
      symPart_join hv.support hw.support, polyEval_mul]
    congr 1
    cases symPart A x <;> cases symPart A' x <;> cases expPart E x <;> cases expPart E' x <;>
      (simp [Value.mul]; first | done | ring)
  · have h1 := hv.support
    have h2 := hw.support
    rcases A with _ | a <;> rcases A' with _ | b <;> simp_all [joinSym, symPresent, symMul_support]

/-- A polynomial of degree at most two in the variable with such
coefficients, of which at least one is present. It is defined where every
present coefficient is. -/
structure Quadratic (f : ℝ → Option ℝ) (c0 c1 c2 : Option (Option ℝ)) : Prop where
  equation : ∀ x, f x = Value.add (coefValue c0)
    (Value.add (Value.mul (coefValue c1) (some x)) (Value.mul (coefValue c2) (some (x ^ 2))))
  support : (c0.isSome || c1.isSome || c2.isSome) = true

theorem Quadratic.constant (c : Option ℝ) : Quadratic (fun _ => c) (some c) none none :=
  ⟨fun x => by cases c <;> simp [coefValue, Value.add, Value.mul], rfl⟩

/-- The variable itself: its coefficient is a literal one. -/
theorem Quadratic.variable {one : Option ℝ}
    (h : one = some (Numeric.denote (s := .real) (1 : ℚ))) :
    Quadratic (fun x => some x) none (some one) none :=
  ⟨fun x => by rw [h]; simp [coefValue, Value.add, Value.mul, Numeric.denote], rfl⟩

theorem Quadratic.add {f g : ℝ → Option ℝ} {a0 a1 a2 b0 b1 b2 : Option (Option ℝ)}
    (hf : Quadratic f a0 a1 a2) (hg : Quadratic g b0 b1 b2) :
    Quadratic (fun x => Value.add (f x) (g x)) (coefAdd a0 b0) (coefAdd a1 b1) (coefAdd a2 b2) := by
  refine ⟨fun x => ?_, ?_⟩
  · show Value.add (f x) (g x) = _
    rw [hf.equation, hg.equation, coefValue_add, coefValue_add, coefValue_add]
    generalize coefValue a0 = A0
    generalize coefValue a1 = A1
    generalize coefValue a2 = A2
    generalize coefValue b0 = B0
    generalize coefValue b1 = B1
    generalize coefValue b2 = B2
    cases A0 <;> cases A1 <;> cases A2 <;> cases B0 <;> cases B1 <;> cases B2 <;>
      (simp [Value.add, Value.mul]; first | done | ring)
  · have h := hf.support
    rcases a0 with _ | a0 <;> rcases a1 with _ | a1 <;> rcases a2 with _ | a2 <;>
      rcases b0 with _ | b0 <;> rcases b1 with _ | b1 <;> rcases b2 with _ | b2 <;>
      simp_all [coefAdd]

private theorem constant_eq {k : ℝ → Option ℝ} {c : Option ℝ}
    (h : Quadratic k (some c) none none) (x : ℝ) : k x = c := by
  rw [h.equation]
  cases c <;> simp [coefValue, Value.add, Value.mul]

/-- A factor that does not mention the variable scales every coefficient. -/
theorem Quadratic.scale {k f : ℝ → Option ℝ} {c : Option ℝ} {a0 a1 a2 : Option (Option ℝ)}
    (hc : Quadratic k (some c) none none) (hf : Quadratic f a0 a1 a2) :
    Quadratic (fun x => Value.mul (k x) (f x)) (coefMul (some c) a0) (coefMul (some c) a1)
      (coefMul (some c) a2) := by
  have hs := hf.support
  refine ⟨fun x => ?_, ?_⟩
  · show Value.mul (k x) (f x) = _
    rw [constant_eq hc, hf.equation]
    rcases a0 with _ | a0 <;> rcases a1 with _ | a1 <;> rcases a2 with _ | a2 <;>
      simp only [coefValue, coefMul] <;> first
      | (simp at hs; done)
      | (cases c <;> (try cases a0) <;> (try cases a1) <;> (try cases a2) <;>
          simp [Value.add, Value.mul] <;> ring)
  · rcases a0 with _ | a0 <;> rcases a1 with _ | a1 <;> rcases a2 with _ | a2 <;>
      simp_all [coefMul]

/-- The same with the factor on the right. -/
theorem Quadratic.scaled {k f : ℝ → Option ℝ} {c : Option ℝ} {a0 a1 a2 : Option (Option ℝ)}
    (hf : Quadratic f a0 a1 a2) (hc : Quadratic k (some c) none none) :
    Quadratic (fun x => Value.mul (f x) (k x)) (coefMul a0 (some c)) (coefMul a1 (some c))
      (coefMul a2 (some c)) := by
  have hs := hf.support
  refine ⟨fun x => ?_, ?_⟩
  · show Value.mul (f x) (k x) = _
    rw [constant_eq hc, hf.equation]
    rcases a0 with _ | a0 <;> rcases a1 with _ | a1 <;> rcases a2 with _ | a2 <;>
      simp only [coefValue, coefMul] <;> first
      | (simp at hs; done)
      | (cases c <;> (try cases a0) <;> (try cases a1) <;> (try cases a2) <;>
          simp [Value.add, Value.mul] <;> ring)
  · rcases a0 with _ | a0 <;> rcases a1 with _ | a1 <;> rcases a2 with _ | a2 <;>
      simp_all [coefMul]

/-- The product of two polynomials of degree at most one. -/
theorem Quadratic.product {f g : ℝ → Option ℝ} {a0 a1 b0 b1 : Option (Option ℝ)}
    (hf : Quadratic f a0 a1 none) (hg : Quadratic g b0 b1 none) :
    Quadratic (fun x => Value.mul (f x) (g x)) (coefMul a0 b0)
      (coefAdd (coefMul a0 b1) (coefMul a1 b0)) (coefMul a1 b1) := by
  have hs := hf.support
  have ht := hg.support
  refine ⟨fun x => ?_, ?_⟩
  · show Value.mul (f x) (g x) = _
    rw [hf.equation, hg.equation]
    rcases a0 with _ | a0 <;> rcases a1 with _ | a1 <;> rcases b0 with _ | b0 <;>
      rcases b1 with _ | b1 <;> simp only [coefValue, coefMul, coefAdd] <;> first
      | (simp at hs; done)
      | (simp at ht; done)
      | ((try cases a0) <;> (try cases a1) <;> (try cases b0) <;> (try cases b1) <;>
          simp [Value.add, Value.mul] <;> ring)
  · rcases a0 with _ | a0 <;> rcases a1 with _ | a1 <;> rcases b0 with _ | b0 <;>
      rcases b1 with _ | b1 <;> simp_all [coefMul, coefAdd]

/-- The square of a polynomial of degree at most one is its product with
itself. -/
theorem Quadratic.square {f : ℝ → Option ℝ} {a0 a1 : Option (Option ℝ)}
    (hf : Quadratic f a0 a1 none) :
    Quadratic (fun x => Option.map (fun y : ℝ => y ^ 2) (f x)) (coefMul a0 a0)
      (coefAdd (coefMul a0 a1) (coefMul a1 a0)) (coefMul a1 a1) := by
  have h := hf.product hf
  refine ⟨fun x => ?_, h.support⟩
  rw [← h.equation]
  show Option.map (fun y : ℝ => y ^ 2) (f x) = Value.mul (f x) (f x)
  cases f x <;> simp [Value.mul, sq]

private theorem zero_of_literal {z : Option ℝ}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : z = some 0 := by
  rw [hz]; simp [Numeric.denote]

/-- An absent coefficient is a zero. -/
theorem Quadratic.fill0 {f : ℝ → Option ℝ} {z : Option ℝ} {c1 c2 : Option (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) (h : Quadratic f none c1 c2) :
    Quadratic f (some z) c1 c2 :=
  ⟨fun x => by rw [h.equation, zero_of_literal hz]; rfl, rfl⟩

theorem Quadratic.fill1 {f : ℝ → Option ℝ} {z : Option ℝ} {c0 c2 : Option (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) (h : Quadratic f c0 none c2) :
    Quadratic f c0 (some z) c2 :=
  ⟨fun x => by rw [h.equation, zero_of_literal hz]; rfl, by simp⟩

/-- A coefficient that is absent is a literal zero. -/
theorem coefValue_absent : coefValue none = some (Numeric.denote (s := .real) (0 : ℚ)) := by
  simp [coefValue, Numeric.denote]

/-- The exponential of a polynomial of degree one with a rational slope: the
exponential of its constant coefficient is a scale. -/
theorem scaled_exp_offset {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (r : ℚ)
    (hE : Quadratic E (some c0) (some c1) none)
    (h1 : c1 = some (Numeric.denote (s := .real) r)) :
    Scaled (fun x => Functions.expR.apply (E x)) (Functions.expR.apply c0) [1] r :=
  ⟨fun x => by
    show Functions.expR.apply (E x) = _
    rw [hE.equation, h1]
    cases c0 <;>
      simp [coefValue, Value.add, Value.mul, Function1.apply, Functions.expR, polyEval,
        Numeric.denote, Real.exp_add]⟩

/-- A coefficient times a power of a partial value: `z`, `z·c` or `z·cⁱ`. -/
def powerValue (c : Option ℝ) : ℕ → Option ℝ → Option ℝ
  | 0, z => z
  | 1, z => Value.mul z c
  | i + 2, z => Value.mul z (Option.map (fun x : ℝ => x ^ (i + 2)) c)

/-- The same under a factor that may be absent. -/
def monomial : Option (Option ℝ) → Option ℝ → Option ℝ
  | none, v => v
  | some a, v => Value.mul a v

/-- The real value of a factor that may be absent. -/
def factorReal : Option (Option ℝ) → ℝ
  | none => 1
  | some (some a) => a
  | some none => 0

/-- The value of a list of terms as a sum. -/
def listSum : List (Option ℝ) → Option ℝ
  | [] => some 0
  | v :: vs => Value.add v (listSum vs)

/-- A sum of the terms of a list in the shape of a tree. A certificate gives a
balanced one: the sum of many terms is then shallow. -/
inductive Sums : List (Option ℝ) → Option ℝ → Prop
  | one {v : Option ℝ} : Sums [v] v
  | add {l r : List (Option ℝ)} {a b : Option ℝ} (h1 : Sums l a) (h2 : Sums r b) :
      Sums (l ++ r) (Value.add a b)

private theorem listSum_append (l r : List (Option ℝ)) :
    listSum (l ++ r) = Value.add (listSum l) (listSum r) := by
  induction l with
  | nil => cases h : listSum r <;> simp [listSum, Value.add, h]
  | cons v l ih =>
    simp only [List.cons_append, listSum, ih]
    cases v <;> cases listSum l <;> cases listSum r <;> simp [Value.add, add_assoc]

theorem Sums.value {l : List (Option ℝ)} {k : Option ℝ} (h : Sums l k) : k = listSum l := by
  induction h with
  | @one v => cases v <;> simp [listSum, Value.add]
  | add _ _ ih1 ih2 => rw [listSum_append, ← ih1, ← ih2]

/-- A polynomial with rational coefficients at a partial value, as the list
of its monomials from a degree on, each under the factor, before the terms
that follow. The first term is always there; a later one is skipped where
its coefficient is zero, or where the value is a literal zero. -/
inductive RowTerms (a : Option (Option ℝ)) (c : Option ℝ) :
    List ℚ → ℕ → List (Option ℝ) → List (Option ℝ) → Prop
  | done {rest : List (Option ℝ)} {i : ℕ} : RowTerms a c [] i rest rest
  | zero {rest out : List (Option ℝ)} {qs : List ℚ} {i : ℕ}
      (h : RowTerms a c qs (i + 2) rest out) : RowTerms a c (0 :: qs) (i + 1) rest out
  | vanish {rest out : List (Option ℝ)} {q : ℚ} {qs : List ℚ} {i : ℕ}
      (hc : c = some (Numeric.denote (s := .real) (0 : ℚ)))
      (h : RowTerms a c qs (i + 2) rest out) : RowTerms a c (q :: qs) (i + 1) rest out
  | term {rest out : List (Option ℝ)} {qs : List ℚ} {i : ℕ} {z : Option ℝ} (q : ℚ)
      (hz : z = some (Numeric.denote (s := .real) q))
      (h : RowTerms a c qs (i + 1) rest out) :
      RowTerms a c (q :: qs) i rest (monomial a (powerValue c i z) :: out)

private theorem powerValue_some (b : ℝ) (i : ℕ) (q : ℝ) :
    powerValue (some b) i (some q) = some (q * b ^ i) := by
  rcases i with _ | _ | i <;> simp [powerValue, Value.mul]

theorem RowTerms.value {a : Option (Option ℝ)} {c : Option ℝ} {rest out : List (Option ℝ)}
    {qs : List ℚ} {i : ℕ} (h : RowTerms a c qs i rest out) (b : ℝ) (hc : c = some b)
    (ha : a ≠ some none) :
    listSum out = Value.add (some (factorReal a * (b ^ i * polyEval qs b))) (listSum rest) := by
  induction h with
  | @done rest i => cases listSum rest <;> simp [polyEval, Value.add]
  | zero _ ih =>
    rw [ih]
    congr 2
    simp only [polyEval, Rat.cast_zero]
    ring
  | vanish h0 _ ih =>
    have hb : b = 0 := by
      rw [hc] at h0
      simpa [Numeric.denote] using h0
    rw [ih, hb]
    congr 2
    simp
  | @term rest out qs i z q hz _ ih =>
    rw [listSum, ih, hz, hc, powerValue_some]
    rcases a with _ | _ | a
    · cases listSum rest <;> simp [monomial, factorReal, polyEval, Value.add, Numeric.denote]
      ring
    · exact absurd rfl ha
    · cases listSum rest <;> simp [monomial, factorReal, polyEval, Value.add, Value.mul,
        Numeric.denote]
      ring

/-- Terms that follow and are undefined leave the sum undefined. -/
theorem RowTerms.missing {a : Option (Option ℝ)} {c : Option ℝ} {rest out : List (Option ℝ)}
    {qs : List ℚ} {i : ℕ} (h : RowTerms a c qs i rest out) (hu : listSum rest = none) :
    listSum out = none := by
  induction h with
  | done => exact hu
  | zero _ ih => exact ih hu
  | vanish _ _ ih => exact ih hu
  | @term rest out qs i z q hz _ ih =>
    rw [listSum, ih hu]
    cases monomial a (powerValue c i z) <;> rfl

/-- An undefined factor leaves the sum undefined: its first term is there. -/
theorem RowTerms.undefined {c : Option ℝ} {rest out : List (Option ℝ)} {q : ℚ} {qs : List ℚ}
    (h : RowTerms (some none) c (q :: qs) 0 rest out) : listSum out = none := by
  cases h with
  | term q hz h => rfl

/-- The integral of a scaled integrable function: the scale times its
integral, and undefined with the scale. -/
theorem partialIntegral_scaleBy {f : ℝ → Option ℝ} {S : Option (Option ℝ)} {F : ℝ → ℝ}
    (hf : ∀ x, f x = scaleBy S (some (F x))) (hi : Integrable F) :
    partialIntegral volume f = scaleBy S (some (∫ x, F x)) := by
  rcases S with _ | _ | s
  · have he : (fun x => (f x).getD 0) = F := by funext x; rw [hf]; rfl
    rw [partialIntegral_valid volume f (fun x => ⟨_, hf x⟩) (by rw [he]; exact hi), he]
    rfl
  · apply if_neg
    intro hd
    obtain ⟨r, hr⟩ := hd.1 0
    rw [hf] at hr
    cases hr
  · have he : (fun x => (f x).getD 0) = fun x => s * F x := by funext x; rw [hf]; rfl
    rw [partialIntegral_valid volume f (fun x => ⟨_, hf x⟩) (by rw [he]; exact hi.const_mul s),
      he, integral_const_mul]
    rfl

/-- The checks of a Gaussian integral with coefficients that do not mention
the variable: the curvature is negative, `κ` is the polynomial of the
moments, and `γ`, `δ` are `-1/(4·c₂)` and `-1/c₂`. -/
def symbolicCheck (P κ : List ℚ) (q2 γ δ : ℚ) : Bool :=
  decide (q2 < 0) &&
    polyZero (polyAdd κ (polyScale (-1) (gaussMoments (-1 / (2 * q2)) P 0 [1] []))) &&
    decide (γ * (4 * q2) = -1) && decide (δ * q2 = -1)

/-- The integral is `κ(c₁)·exp(c₀ - c₁²/(4·c₂))·√(π·(-1/c₂))` under the scale. A
coefficient that is undefined leaves the integrand undefined everywhere, and
the exponential of the result undefined with it. -/
theorem gaussian_partialIntegral_symbolic {f : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ : List ℚ) (q2 γ δ : ℚ)
    (hf : Bell f S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : symbolicCheck P κ q2 γ δ = true) {k g d pi : Option ℝ}
    {ms : List (Option ℝ)} (hm : RowTerms none c1 κ 0 [] ms) (hk : Sums ms k)
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    partialIntegral volume f = scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply (Value.add c0 (Value.mul g (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi d)))) := by
  simp only [symbolicCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hq, hκ⟩, hγ⟩, hδ⟩ := h
  have undefined : (∀ x, E x = none) → c0 = none ∨ c1 = none → partialIntegral volume f =
      scaleBy S (Value.mul k (Value.mul
        (Functions.expR.apply (Value.add c0 (Value.mul g (Value.mul c1 c1))))
        (Functions.sqrtR.apply (Value.mul pi d)))) := fun hn hc => by
    have hr : Value.mul k (Value.mul
        (Functions.expR.apply (Value.add c0 (Value.mul g (Value.mul c1 c1))))
        (Functions.sqrtR.apply (Value.mul pi d))) = none := by
      rcases hc with hc | hc <;> rw [hc] <;> cases k <;> cases g <;> (try cases c0) <;>
        (try cases c1) <;> simp [Value.mul, Value.add, Function1.apply]
    have hs : scaleBy S none = none := by
      rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
    rw [hr, hs]
    apply if_neg
    intro hdef
    obtain ⟨r, hr⟩ := hdef.1 0
    rw [hf.plain, expPart, hn] at hr
    have : scaleBy S (Value.mul (some (polyEval P 0)) (Functions.expR.apply none)) = none := by
      rcases S with _ | _ | s <;> simp [scaleBy, Value.mul, Function1.apply]
    rw [this] at hr
    cases hr
  rcases c0 with _ | a
  · exact undefined (fun x => by rw [hE.equation]; simp [coefValue, Value.add]) (Or.inl rfl)
  rcases c1 with _ | b
  · exact undefined (fun x => by rw [hE.equation]; simp [coefValue, Value.add, Value.mul])
      (Or.inr rfl)
  have hE' : ∀ x, E x = some (a + b * x + q2 * x ^ 2) := fun x => by
    rw [hE.equation, h2]
    simp [coefValue, Value.add, Value.mul, Numeric.denote]
    ring
  obtain ⟨hi, hv⟩ := gaussian_moments a b hq P
  have hfx : ∀ x, f x = scaleBy S (some (polyEval P x * Real.exp (a + b * x + q2 * x ^ 2))) :=
    fun x => by
      rw [hf.plain, expPart, hE']
      simp [Value.mul, Function1.apply, Functions.expR]
  rw [partialIntegral_scaleBy hfx hi, hv]
  congr 1
  have hcR : ((q2 : ℚ) : ℝ) < 0 := by exact_mod_cast hq
  have hc : ((q2 : ℚ) : ℝ) ≠ 0 := hcR.ne
  have hγR : (γ : ℝ) * (4 * q2) = -1 := by exact_mod_cast hγ
  have hδR : (δ : ℝ) * q2 = -1 := by exact_mod_cast hδ
  have hz := polyEval_zero hκ b
  rw [polyEval_add, polyEval_scale] at hz
  have hκ' : polyEval (gaussMoments (-1 / (2 * q2)) P 0 [1] []) b = polyEval κ b := by
    push_cast at hz
    linarith
  have hγ' : a - b ^ 2 / (4 * (q2 : ℝ)) = a + γ * (b * b) := by
    have : (γ : ℝ) = -1 / (4 * q2) := by
      rw [eq_div_iff (mul_ne_zero four_ne_zero hc)]
      exact hγR
    rw [this]; ring
  have hδ' : Real.pi / (-(q2 : ℝ)) = Real.pi * δ := by
    have : (δ : ℝ) = 1 / (-q2) := by
      rw [eq_div_iff (neg_ne_zero.2 hc)]
      linarith
    rw [this]; ring
  have hpos : 0 ≤ Real.pi * (δ : ℝ) := by
    rw [← hδ']
    exact div_nonneg Real.pi_pos.le (by linarith)
  have hkv : k = some (polyEval κ b) := by
    rw [hk.value, hm.value b rfl (by simp)]
    simp [listSum, factorReal, Value.add]
  rw [hκ', hγ', hδ', hkv, hg, hd, hpi]
  simp [Value.mul, Value.add, Function1.apply, Functions.expR, Functions.sqrtR, Functions.pi,
    Numeric.denote, hpos]

/-- The rows of moments: row `j` is the polynomial of the moments of `xʲ·P`. -/
def momentRows (h : ℚ) (P : List ℚ) : List (List ℚ) → ℕ → List ℚ → List ℚ → Bool
  | [], _, _, _ => true
  | κ :: κs, j, μ, μ' =>
    polyZero (polyAdd κ (polyScale (-1) (gaussMoments h P j μ μ'))) &&
      momentRows h P κs (j + 1) (polyScale h (polyAdd (polyMul [0, 1] μ) (polyScale j μ'))) μ

/-- The sum of the coefficients times their rows at the linear coefficient. -/
def momentValue (b : ℝ) : List (Option (Option ℝ)) → List (List ℚ) → ℝ
  | c :: cs, κ :: κs => coefReal c * polyEval κ b + momentValue b cs κs
  | _, _ => 0

/-- The moments of a polynomial with such coefficients times a rational one:
coefficient by coefficient, each against its row. -/
theorem momentRows_integral (c0 c1 : ℝ) {c2 : ℝ} (hc : c2 < 0) {h : ℚ}
    (hh : (h : ℝ) * (2 * c2) = -1) (G : ℝ) (P : List ℚ) :
    ∀ (cs : List (Option (Option ℝ))) (κs : List (List ℚ)) (j : ℕ) (μ μ' : List ℚ),
      cs.length = κs.length → momentRows h P κs j μ μ' = true →
      (∫ x : ℝ, x ^ j * Real.exp (c0 + c1 * x + c2 * x ^ 2)) = polyEval μ c1 * G →
      (j : ℝ) * (∫ x : ℝ, x ^ (j - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        j * (polyEval μ' c1 * G) →
      Integrable (fun x : ℝ => x ^ j * realEval cs x * polyEval P x *
          Real.exp (c0 + c1 * x + c2 * x ^ 2)) ∧
        (∫ x : ℝ, x ^ j * realEval cs x * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
          momentValue c1 cs κs * G := by
  intro cs
  induction cs with
  | nil =>
    intro κs j μ μ' _ _ _ _
    simp [realEval, momentValue]
  | cons c cs ih =>
    intro κs j μ μ' hlen hrows h1 h2
    cases κs with
    | nil => simp at hlen
    | cons κ κs =>
      simp only [momentRows, Bool.and_eq_true] at hrows
      obtain ⟨hκ, hrest⟩ := hrows
      obtain ⟨hn1, hn2⟩ := moment_next c0 c1 hc hh G j μ μ' h1 h2
      obtain ⟨hi, hv⟩ := ih κs (j + 1) _ μ (by simpa using hlen) hrest hn1 hn2
      obtain ⟨hpi, hpv⟩ := gaussMoments_integral c0 c1 hc hh G P j μ μ' h1 h2
      have hz := polyEval_zero hκ c1
      rw [polyEval_add, polyEval_scale] at hz
      have hκ' : polyEval (gaussMoments h P j μ μ') c1 = polyEval κ c1 := by
        push_cast at hz
        linarith
      have hsplit : (fun x : ℝ => x ^ j * realEval (c :: cs) x * polyEval P x *
          Real.exp (c0 + c1 * x + c2 * x ^ 2)) = fun x =>
          coefReal c * (x ^ j * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
            x ^ (j + 1) * realEval cs x * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2) := by
        funext x
        simp only [realEval]
        ring
      refine ⟨by rw [hsplit]; exact (hpi.const_mul _).add hi, ?_⟩
      rw [hsplit, integral_add (hpi.const_mul _) hi, integral_const_mul, hpv, hv, hκ']
      simp only [momentValue]
      ring

/-- The monomials of the present coefficients times their rows at the linear
coefficient, in order. The row of a coefficient that is one may be bare. -/
inductive MomentTerms (c1 : Option ℝ) :
    List (Option (Option ℝ)) → List (List ℚ) → List (Option ℝ) → Prop
  | done : MomentTerms c1 [] [] []
  | absent {out : List (Option ℝ)} {cs : List (Option (Option ℝ))} {κs : List (List ℚ)}
      (κ : List ℚ) (h : MomentTerms c1 cs κs out) : MomentTerms c1 (none :: cs) (κ :: κs) out
  | present {rest out : List (Option ℝ)} {cs : List (Option (Option ℝ))}
      {κs : List (List ℚ)} {a : Option ℝ} {q : ℚ} {qs : List ℚ}
      (hr : RowTerms (some a) c1 (q :: qs) 0 rest out) (h : MomentTerms c1 cs κs rest) :
      MomentTerms c1 (some a :: cs) ((q :: qs) :: κs) out
  | bare {rest out : List (Option ℝ)} {cs : List (Option (Option ℝ))}
      {κs : List (List ℚ)} {q : ℚ} {qs : List ℚ}
      (hr : RowTerms none c1 (q :: qs) 0 rest out) (h : MomentTerms c1 cs κs rest) :
      MomentTerms c1 (some (some 1) :: cs) ((q :: qs) :: κs) out

theorem MomentTerms.length {c1 : Option ℝ} {out : List (Option ℝ)}
    {cs : List (Option (Option ℝ))} {κs : List (List ℚ)} (h : MomentTerms c1 cs κs out) :
    cs.length = κs.length := by
  induction h with
  | done => rfl
  | absent _ _ ih => simp [ih]
  | present _ _ ih => simp [ih]
  | bare _ _ ih => simp [ih]

/-- An undefined coefficient leaves the sum undefined. -/
theorem MomentTerms.undefined {c1 : Option ℝ} {out : List (Option ℝ)}
    {cs : List (Option (Option ℝ))} {κs : List (List ℚ)} (h : MomentTerms c1 cs κs out)
    (hu : some none ∈ cs) : listSum out = none := by
  induction h with
  | done => simp at hu
  | absent _ _ ih => exact ih (by simpa using hu)
  | @present rest out cs κs a q qs hr _ ih =>
    rcases List.mem_cons.1 hu with hu | hu
    · have ha : a = none := by simpa using hu.symm
      subst ha
      exact hr.undefined
    · exact hr.missing (ih hu)
  | bare hr _ ih =>
    rcases List.mem_cons.1 hu with hu | hu
    · simp at hu
    · exact hr.missing (ih hu)

theorem MomentTerms.value {c1 : Option ℝ} {out : List (Option ℝ)}
    {cs : List (Option (Option ℝ))} {κs : List (List ℚ)} (h : MomentTerms c1 cs κs out) (b : ℝ)
    (hc : c1 = some b) (hd : some none ∉ cs) : listSum out = some (momentValue b cs κs) := by
  induction h with
  | done => rfl
  | absent κ _ ih =>
    rw [ih (fun hm => hd (by simp [hm]))]
    simp [momentValue, coefReal]
  | @present rest out cs κs a q qs hr _ ih =>
    have ha : a ≠ none := fun ha => hd (by simp [ha])
    rw [hr.value b hc (by simpa using ha), ih (fun hm => hd (by simp [hm]))]
    rcases a with _ | a
    · exact absurd rfl ha
    · simp [momentValue, coefReal, factorReal, Value.add]
  | bare hr _ ih =>
    rw [hr.value b hc (by simp), ih (fun hm => hd (by simp [hm]))]
    simp [momentValue, coefReal, factorReal, Value.add]

/-- The checks of a Gaussian integral under a polynomial whose coefficients
do not mention the variable: the curvature is negative, the rows are the
moments of the powers times the rational polynomial, and `γ`, `δ` are
`-1/(4·c₂)` and `-1/c₂`. -/
def momentsCheck (P : List ℚ) (κs : List (List ℚ)) (q2 γ δ : ℚ) : Bool :=
  decide (q2 < 0) && momentRows (-1 / (2 * q2)) P κs 0 [1] [] &&
    decide (γ * (4 * q2) = -1) && decide (δ * q2 = -1)

/-- The same under a polynomial whose coefficients do not mention the
variable: the integral is linear in them, and each meets the moments of its
power. A coefficient that is undefined leaves the integrand undefined
everywhere, and the sum with it. -/
theorem gaussian_partialIntegral_moments {f : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {cs : List (Option (Option ℝ))} {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ}
    (κs : List (List ℚ)) (q2 γ δ : ℚ) (hf : Bell f S (some cs) P (some E))
    (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : momentsCheck P κs q2 γ δ = true) {k g d pi : Option ℝ}
    {ms : List (Option ℝ)} (hm : MomentTerms c1 cs κs ms) (hk : Sums ms k)
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    partialIntegral volume f = scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply (Value.add c0 (Value.mul g (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi d)))) := by
  simp only [momentsCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hq, hrows⟩, hγ⟩, hδ⟩ := h
  have missing : (∀ x, f x = none) → ∀ r : Option ℝ, r = none →
      partialIntegral volume f = scaleBy S r := fun hn r hr => by
    have hs : scaleBy S none = none := by
      rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
    rw [hr, hs]
    apply if_neg
    intro hdef
    obtain ⟨v, hv⟩ := hdef.1 0
    rw [hn] at hv
    cases hv
  have hfn : ∀ x, (symEval cs x = none ∨ E x = none) → f x = none := fun x hx => by
    rw [hf.equation, symPart, expPart]
    rcases hx with hx | hx <;> rw [hx] <;> rcases S with _ | _ | s <;>
      simp [scaleBy, Value.mul, Function1.apply]
  rcases c0 with _ | a
  · exact missing (fun x => hfn x (Or.inr (by rw [hE.equation]; simp [coefValue, Value.add])))
      _ (by cases k <;> cases g <;> cases c1 <;> simp [Value.mul, Value.add, Function1.apply])
  rcases c1 with _ | b
  · exact missing
      (fun x => hfn x (Or.inr (by rw [hE.equation]; simp [coefValue, Value.add, Value.mul])))
      _ (by cases k <;> cases g <;> simp [Value.mul, Value.add, Function1.apply])
  by_cases hu : some none ∈ cs
  · have hk' : k = none := by rw [hk.value, hm.undefined hu]
    exact missing (fun x => hfn x (Or.inl ((symEval_none_iff cs x).2 hu))) _
      (by rw [hk']; rfl)
  have hE' : ∀ x, E x = some (a + b * x + q2 * x ^ 2) := fun x => by
    rw [hE.equation, h2]
    simp [coefValue, Value.add, Value.mul, Numeric.denote]
    ring
  have hcR : ((q2 : ℚ) : ℝ) < 0 := by exact_mod_cast hq
  have hc : ((q2 : ℚ) : ℝ) ≠ 0 := hcR.ne
  have hh : (((-1 / (2 * q2) : ℚ)) : ℝ) * (2 * (q2 : ℝ)) = -1 := by
    push_cast
    field_simp
  obtain ⟨hi, hv⟩ := momentRows_integral a b hcR hh
    (Real.exp (a - b ^ 2 / (4 * q2)) * √(Real.pi / (-q2))) P cs κs 0 [1] [] hm.length hrows
    (by simp [polyEval, gaussian_integral a b (q2 : ℝ) hcR]) (by simp)
  simp only [pow_zero, one_mul] at hi hv
  have hfx : ∀ x, f x = scaleBy S
      (some (realEval cs x * polyEval P x * Real.exp (a + b * x + q2 * x ^ 2))) := fun x => by
    rw [hf.equation, symPart, expPart, hE', symEval_real hu]
    simp [Value.mul, Function1.apply, Functions.expR]
  rw [partialIntegral_scaleBy hfx hi, hv]
  congr 1
  have hkv : k = some (momentValue b cs κs) := by rw [hk.value, hm.value b rfl hu]
  have hγR : (γ : ℝ) * (4 * q2) = -1 := by exact_mod_cast hγ
  have hδR : (δ : ℝ) * q2 = -1 := by exact_mod_cast hδ
  have hγ' : a - b ^ 2 / (4 * (q2 : ℝ)) = a + γ * (b * b) := by
    have : (γ : ℝ) = -1 / (4 * q2) := by
      rw [eq_div_iff (mul_ne_zero four_ne_zero hc)]
      exact hγR
    rw [this]; ring
  have hδ' : Real.pi / (-(q2 : ℝ)) = Real.pi * δ := by
    have : (δ : ℝ) = 1 / (-q2) := by
      rw [eq_div_iff (neg_ne_zero.2 hc)]
      linarith
    rw [this]; ring
  have hpos : 0 ≤ Real.pi * (δ : ℝ) := by
    rw [← hδ']
    exact div_nonneg Real.pi_pos.le (by linarith)
  rw [hγ', hδ', hkv, hg, hd, hpi]
  simp [Value.mul, Value.add, Function1.apply, Functions.expR, Functions.sqrtR, Functions.pi,
    Numeric.denote, hpos]

/-! A curvature that is a term. The moments are then polynomials in two
values, the linear coefficient and `h = -1/(2·c₂)`: lists of rows, one for each
power of `h`, each a polynomial in the linear coefficient. -/

/-- The value of such a polynomial. -/
def poly2Eval : List (List ℚ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p :: P, b, h => polyEval p b + h * poly2Eval P b h

def poly2Add : List (List ℚ) → List (List ℚ) → List (List ℚ)
  | [], Q => Q
  | p :: P, [] => p :: P
  | p :: P, q :: Q => polyAdd p q :: poly2Add P Q

def poly2Scale (c : ℚ) : List (List ℚ) → List (List ℚ)
  | [] => []
  | p :: P => polyScale c p :: poly2Scale c P

/-- Times the linear coefficient. -/
def poly2Shift : List (List ℚ) → List (List ℚ)
  | [] => []
  | p :: P => (0 :: p) :: poly2Shift P

theorem poly2Eval_add (P Q : List (List ℚ)) (b h : ℝ) :
    poly2Eval (poly2Add P Q) b h = poly2Eval P b h + poly2Eval Q b h := by
  induction P generalizing Q with
  | nil => simp [poly2Add, poly2Eval]
  | cons p P ih =>
    cases Q with
    | nil => simp [poly2Add, poly2Eval]
    | cons q Q =>
      simp only [poly2Add, poly2Eval, polyEval_add, ih]
      ring

theorem poly2Eval_scale (c : ℚ) (P : List (List ℚ)) (b h : ℝ) :
    poly2Eval (poly2Scale c P) b h = c * poly2Eval P b h := by
  induction P with
  | nil => simp [poly2Scale, poly2Eval]
  | cons p P ih =>
    simp only [poly2Scale, poly2Eval, polyEval_scale, ih]
    ring

theorem poly2Eval_shift (P : List (List ℚ)) (b h : ℝ) :
    poly2Eval (poly2Shift P) b h = b * poly2Eval P b h := by
  induction P with
  | nil => simp [poly2Shift, poly2Eval]
  | cons p P ih =>
    simp only [poly2Shift, poly2Eval, polyEval, ih, Rat.cast_zero, _root_.zero_add]
    ring

/-- The moments of the exponential of `c₀ + c₁·x + c₂·x²` relative to its
integral, weighted by the coefficients of a polynomial, as a polynomial in
`c₁` and `h`: the moment of degree `j + 1` is `h·(c₁·μⱼ + j·μⱼ₋₁)`. -/
def gaussMoments2 : List ℚ → ℕ → List (List ℚ) → List (List ℚ) → List (List ℚ)
  | [], _, _, _ => []
  | a :: P, j, μ, μ' =>
    poly2Add (poly2Scale a μ)
      (gaussMoments2 P (j + 1) ([] :: poly2Add (poly2Shift μ) (poly2Scale j μ')) μ)

theorem moment_next2 (c0 c1 : ℝ) {c2 : ℝ} (hc : c2 < 0) {h : ℝ} (hh : h * (2 * c2) = -1)
    (G : ℝ) (j : ℕ) (μ μ' : List (List ℚ))
    (h1 : (∫ x : ℝ, x ^ j * Real.exp (c0 + c1 * x + c2 * x ^ 2)) = poly2Eval μ c1 h * G)
    (h2 : (j : ℝ) * (∫ x : ℝ, x ^ (j - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
      j * (poly2Eval μ' c1 h * G)) :
    (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        poly2Eval ([] :: poly2Add (poly2Shift μ) (poly2Scale j μ')) c1 h * G ∧
      ((j + 1 : ℕ) : ℝ) * (∫ x : ℝ, x ^ (j + 1 - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        ((j + 1 : ℕ) : ℝ) * (poly2Eval μ c1 h * G) := by
  have hrec := pow_gaussian_recurrence c0 c1 hc j
  refine ⟨?_, by rw [Nat.add_sub_cancel, h1]⟩
  simp only [poly2Eval, polyEval, poly2Eval_add, poly2Eval_shift, poly2Eval_scale,
    Rat.cast_natCast, _root_.zero_add]
  have h3 : 2 * c2 * (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
      -((j : ℝ) * (poly2Eval μ' c1 h * G) + c1 * (poly2Eval μ c1 h * G)) := by
    rw [← h1, ← h2]; linarith
  calc (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2))
      = -(h * (2 * c2)) * (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) := by
        rw [hh]; ring
    _ = -h * (2 * c2 * (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2))) := by
        ring
    _ = _ := by rw [h3]; ring

theorem gaussMoments2_integral (c0 c1 : ℝ) {c2 : ℝ} (hc : c2 < 0) {h : ℝ}
    (hh : h * (2 * c2) = -1) (G : ℝ) :
    ∀ (P : List ℚ) (j : ℕ) (μ μ' : List (List ℚ)),
      (∫ x : ℝ, x ^ j * Real.exp (c0 + c1 * x + c2 * x ^ 2)) = poly2Eval μ c1 h * G →
      (j : ℝ) * (∫ x : ℝ, x ^ (j - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        j * (poly2Eval μ' c1 h * G) →
      Integrable (fun x : ℝ => x ^ j * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) ∧
        (∫ x : ℝ, x ^ j * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
          poly2Eval (gaussMoments2 P j μ μ') c1 h * G := by
  intro P
  induction P with
  | nil =>
    intro j μ μ' _ _
    simp [polyEval, gaussMoments2, poly2Eval]
  | cons a P ih =>
    intro j μ μ' h1 h2
    have hI := pow_gaussian_integrable c0 c1 hc
    obtain ⟨hnext, hprev⟩ := moment_next2 c0 c1 hc hh G j μ μ' h1 h2
    obtain ⟨hi, hv⟩ := ih (j + 1) _ μ hnext hprev
    have hsplit : (fun x : ℝ => x ^ j * polyEval (a :: P) x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        fun x => (a : ℝ) * (x ^ j * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
          x ^ (j + 1) * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2) := by
      funext x
      simp only [polyEval]
      ring
    refine ⟨by rw [hsplit]; exact ((hI j).const_mul _).add hi, ?_⟩
    rw [hsplit, integral_add ((hI j).const_mul _) hi, integral_const_mul, h1, hv]
    simp only [gaussMoments2, poly2Eval_add, poly2Eval_scale]
    ring

/-- The integral of a polynomial times the exponential of a quadratic with
real coefficients and negative curvature. -/
theorem gaussian_moments2 (c0 c1 : ℝ) {c2 : ℝ} (hc : c2 < 0) (P : List ℚ) :
    Integrable (fun x : ℝ => polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) ∧
      (∫ x : ℝ, polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        poly2Eval (gaussMoments2 P 0 [[1]] []) c1 (-1 / (2 * c2)) *
          (Real.exp (c0 - c1 ^ 2 / (4 * c2)) * √(Real.pi / (-c2))) := by
  have hh : (-1 / (2 * c2)) * (2 * c2) = -1 := by
    have hne : c2 ≠ 0 := hc.ne
    field_simp
  have h := gaussMoments2_integral c0 c1 hc hh
    (Real.exp (c0 - c1 ^ 2 / (4 * c2)) * √(Real.pi / (-c2))) P 0 [[1]] []
    (by simp [poly2Eval, polyEval, gaussian_integral c0 c1 c2 hc]) (by simp)
  simpa using h

/-- A scale that is absent, or not zero where it is defined. -/
def scaleNonvanishing : Option (Option ℝ) → Prop
  | none => True
  | some c => Nonvanishing c

/-- The exponential of a quadratic is not integrable over the line unless its
curvature is negative: on a half-line it stays above a positive constant. -/
theorem exp_quadratic_not_integrable (a b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ¬ Integrable (fun x : ℝ => Real.exp (a + b * x + c * x ^ 2)) volume := by
  intro hi
  have above : ∀ x : ℝ, 0 ≤ b * x → ‖Real.exp a‖ ≤ Real.exp (a + b * x + c * x ^ 2) := fun x hx => by
    rw [Real.norm_of_nonneg (Real.exp_pos a).le]
    apply Real.exp_le_exp.2
    have h2 : 0 ≤ c * x ^ 2 := mul_nonneg hc (sq_nonneg x)
    linarith
  by_cases hb : 0 ≤ b
  · have hs : IntegrableOn (fun _ : ℝ => Real.exp a) (Set.Ici 0) volume := by
      refine Integrable.mono' hi.integrableOn aestronglyMeasurable_const ?_
      exact (ae_restrict_iff' measurableSet_Ici).2
        (Filter.Eventually.of_forall fun x hx => above x (mul_nonneg hb hx))
    rw [integrableOn_const] at hs
    rcases hs with h0 | hfin
    · exact (Real.exp_pos a).ne' h0
    · rw [Real.volume_Ici] at hfin
      exact lt_irrefl _ hfin
  · have hs : IntegrableOn (fun _ : ℝ => Real.exp a) (Set.Iic 0) volume := by
      refine Integrable.mono' hi.integrableOn aestronglyMeasurable_const ?_
      exact (ae_restrict_iff' measurableSet_Iic).2
        (Filter.Eventually.of_forall fun x hx =>
          above x (mul_nonneg_of_nonpos_of_nonpos (not_le.1 hb).le hx))
    rw [integrableOn_const] at hs
    rcases hs with h0 | hfin
    · exact (Real.exp_pos a).ne' h0
    · rw [Real.volume_Iic] at hfin
      exact lt_irrefl _ hfin

/-- A polynomial that is not zero stays away from zero towards infinity. -/
theorem eval_eventually_away {q : Polynomial ℝ} (hq : q ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in atTop, δ ≤ |q.eval x| := by
  by_cases hd : 0 < q.degree
  · exact ⟨1, one_pos, (q.abs_tendsto_atTop hd).eventually_ge_atTop 1⟩
  · have hc := Polynomial.eq_C_of_degree_le_zero (not_lt.1 hd)
    have hne : q.coeff 0 ≠ 0 := fun h => hq (by rw [hc, h, Polynomial.C_0])
    refine ⟨|q.coeff 0|, abs_pos.2 hne, Filter.Eventually.of_forall fun x => ?_⟩
    rw [hc, Polynomial.eval_C, Polynomial.coeff_C_zero]

/-- A polynomial that is not zero times the exponential of a quadratic is not
integrable over the line unless the curvature is negative. -/
theorem real_polynomial_exp_quadratic_not_integrable {q : Polynomial ℝ} (hq : q ≠ 0)
    (a b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ¬ Integrable (fun x : ℝ => q.eval x * Real.exp (a + b * x + c * x ^ 2)) volume := by
  intro hi
  have above : ∀ (δ x : ℝ), 0 ≤ δ → δ ≤ |q.eval x| → 0 ≤ b * x →
      ‖δ * Real.exp a‖ ≤ ‖q.eval x * Real.exp (a + b * x + c * x ^ 2)‖ := fun δ x h0 hx hbx => by
    rw [norm_mul, norm_mul, Real.norm_of_nonneg h0, Real.norm_of_nonneg (Real.exp_pos a).le,
      Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h2 : 0 ≤ c * x ^ 2 := mul_nonneg hc (sq_nonneg x)
    exact mul_le_mul hx (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos a).le (abs_nonneg _)
  by_cases hb : 0 ≤ b
  · obtain ⟨δ, hδ, hev⟩ := eval_eventually_away hq
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
    have hs : IntegrableOn (fun _ : ℝ => δ * Real.exp a) (Set.Ici (max M 0)) volume := by
      refine Integrable.mono' hi.norm.integrableOn aestronglyMeasurable_const ?_
      refine (ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hx' : max M 0 ≤ x := hx
      exact above δ x hδ.le (hM x (le_trans (le_max_left _ _) hx'))
        (mul_nonneg hb (le_trans (le_max_right _ _) hx'))
    rw [integrableOn_const] at hs
    rcases hs with h0 | hfin
    · exact (mul_pos hδ (Real.exp_pos a)).ne' h0
    · rw [Real.volume_Ici] at hfin
      exact lt_irrefl _ hfin
  · have hq' : q.comp (-Polynomial.X) ≠ 0 := fun h0 => hq (by
      have h1 := congrArg (fun r : Polynomial ℝ => r.comp (-Polynomial.X)) h0
      simpa [Polynomial.comp_assoc] using h1)
    obtain ⟨δ, hδ, hev⟩ := eval_eventually_away hq'
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
    have hs : IntegrableOn (fun _ : ℝ => δ * Real.exp a) (Set.Iic (min (-M) 0)) volume := by
      refine Integrable.mono' hi.norm.integrableOn aestronglyMeasurable_const ?_
      refine (ae_restrict_iff' measurableSet_Iic).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hx' : x ≤ min (-M) 0 := hx
      have hxM : M ≤ -x := by linarith [le_trans hx' (min_le_left _ _)]
      have h1 := hM (-x) hxM
      rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, neg_neg] at h1
      exact above δ x hδ.le h1
        (mul_nonneg_of_nonpos_of_nonpos (not_le.1 hb).le (le_trans hx' (min_le_right _ _)))
    rw [integrableOn_const] at hs
    rcases hs with h0 | hfin
    · exact (mul_pos hδ (Real.exp_pos a)).ne' h0
    · rw [Real.volume_Iic] at hfin
      exact lt_irrefl _ hfin

/-- The same for a polynomial with rational coefficients. -/
theorem polynomial_exp_quadratic_not_integrable {P : List ℚ} (hP : polyZero P = false)
    (a b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ¬ Integrable (fun x : ℝ => polyEval P x * Real.exp (a + b * x + c * x ^ 2)) volume := by
  have h := real_polynomial_exp_quadratic_not_integrable (QSym.Limit.toPoly_ne_zero hP) a b hc
  simpa only [QSym.Limit.eval_toPoly] using h

/-- Every row is zero. -/
def poly2Zero : List (List ℚ) → Bool
  | [] => true
  | p :: P => polyZero p && poly2Zero P

theorem poly2Eval_zero {P : List (List ℚ)} (h : poly2Zero P = true) (b x : ℝ) :
    poly2Eval P b x = 0 := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    simp only [poly2Zero, Bool.and_eq_true] at h
    simp [poly2Eval, polyEval_zero h.1, ih h.2]

/-- The power of `h` in front of a row: one, the value itself, or a power of it. -/
def curvaturePower (h : Option ℝ) : ℕ → Option ℝ
  | 0 => some 1
  | 1 => h
  | l + 2 => Option.map (fun x : ℝ => x ^ (l + 2)) h

/-- The coefficients of the rows: the powers of `h`, absent in front of a row
that is zero. -/
def curvatureCoefs (h : Option ℝ) : List (List ℚ) → ℕ → List (Option (Option ℝ))
  | [], _ => []
  | κ :: K, l => (if polyZero κ then none else some (curvaturePower h l)) :: curvatureCoefs h K (l + 1)

theorem curvaturePower_some (h : ℝ) (l : ℕ) : curvaturePower (some h) l = some (h ^ l) := by
  rcases l with _ | _ | l <;> simp [curvaturePower]

theorem curvatureCoefs_defined (h : ℝ) (K : List (List ℚ)) (l : ℕ) :
    some none ∉ curvatureCoefs (some h) K l := by
  induction K generalizing l with
  | nil => simp [curvatureCoefs]
  | cons κ K ih =>
    simp only [curvatureCoefs, List.mem_cons, not_or]
    refine ⟨?_, ih (l + 1)⟩
    split_ifs <;> simp [curvaturePower_some]

theorem momentValue_curvature (b h : ℝ) (K : List (List ℚ)) (l : ℕ) :
    momentValue b (curvatureCoefs (some h) K l) K = h ^ l * poly2Eval K b h := by
  induction K generalizing l with
  | nil => simp [curvatureCoefs, momentValue, poly2Eval]
  | cons κ K ih =>
    simp only [curvatureCoefs, momentValue, poly2Eval, ih (l + 1)]
    by_cases hz : polyZero κ = true
    · rw [if_pos hz, polyEval_zero hz]
      simp [coefReal]
      ring
    · rw [if_neg hz, curvaturePower_some]
      simp only [coefReal]
      ring

/-- A quadratic is undefined where a coefficient is. -/
theorem Quadratic.missing {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ}
    (hE : Quadratic E (some c0) (some c1) (some c2)) (h : c0 = none ∨ c1 = none ∨ c2 = none)
    (x : ℝ) : E x = none := by
  rw [hE.equation]
  rcases h with rfl | rfl | rfl
  · simp [coefValue, Value.add]
  · cases c0 <;> simp [coefValue, Value.add, Value.mul]
  · cases c0 <;> cases c1 <;> simp [coefValue, Value.add, Value.mul]

/-- So is the closed form: in the exponent or under the root. -/
private theorem curvature_missing (S : Option (Option ℝ)) (k g m pi : Option ℝ)
    {c0 c1 c2 : Option ℝ} (h : c0 = none ∨ c1 = none ∨ c2 = none) :
    scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply
        (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))) = none := by
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  have right : ∀ X : Option ℝ, Value.mul k (Value.mul X none) = none := fun X => by
    cases k <;> cases X <;> rfl
  have left : ∀ X : Option ℝ, Value.mul k (Value.mul (Functions.expR.apply none) X) = none :=
    fun X => by cases k <;> simp [Value.mul, Function1.apply]
  rcases h with rfl | rfl | rfl
  · have : Value.add (none : Option ℝ)
        (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1)) = none := rfl
    rw [this, left, hnone]
  · have : Value.add c0
        (Value.mul (Value.mul g (Value.inv c2)) (Value.mul (none : Option ℝ) none)) = none := by
      cases c0 <;> cases Value.mul g (Value.inv c2) <;> rfl
    rw [this, left, hnone]
  · have : Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv (none : Option ℝ)))) =
        none := by
      cases pi <;> cases m <;> simp [Value.mul, Value.inv, Function1.apply]
    rw [this, right, hnone]

/-- A scale that is not zero times a real function times the exponential of a
quadratic with real coefficients. Where the curvature is negative the function
has the moment `k` relative to the Gaussian integral; elsewhere the product is
not integrable, and the closed form is missing with the observation: the
inverse at zero, the root above it. -/
private theorem curvature_scaled {f : ℝ → Option ℝ} (Q : ℝ → ℝ) {a b c : ℝ}
    {k g m pi : Option ℝ} {s : ℝ} (hs : s ≠ 0)
    (hfs : ∀ x, f x = some (s * (Q x * Real.exp (a + b * x + c * x ^ 2))))
    (hneg : c < 0 → ∃ κ : ℝ, k = some κ ∧
      Integrable (fun x : ℝ => Q x * Real.exp (a + b * x + c * x ^ 2)) volume ∧
      (∫ x : ℝ, Q x * Real.exp (a + b * x + c * x ^ 2)) =
        κ * (Real.exp (a - b ^ 2 / (4 * c)) * √(Real.pi / (-c))))
    (hpos : 0 ≤ c → ¬ Integrable (fun x : ℝ => Q x * Real.exp (a + b * x + c * x ^ 2)) volume)
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hmn : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    partialIntegral volume f = Value.mul (some s) (Value.mul k (Value.mul
      (Functions.expR.apply (Value.add (some a)
        (Value.mul (Value.mul g (Value.inv (some c))) (Value.mul (some b) (some b)))))
      (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv (some c))))))) := by
  have he : (fun x => (f x).getD 0) =
      fun x => s * (Q x * Real.exp (a + b * x + c * x ^ 2)) := by
    funext x
    rw [hfs]
    rfl
  by_cases hc : c < 0
  · obtain ⟨κ, hkv, hi0, hv⟩ := hneg hc
    have hi := hi0.const_mul s
    have hne : c ≠ 0 := hc.ne
    rw [partialIntegral_valid volume f (fun x => ⟨_, hfs x⟩) (by rw [he]; exact hi), he,
      integral_const_mul, hv, hkv, hg, hmn, hpi]
    have hinv : 0 < -c⁻¹ := by
      have := inv_lt_zero.2 hc
      linarith
    have hle : Real.pi * c⁻¹ ≤ 0 := by nlinarith [Real.pi_pos]
    have h1 : a - b ^ 2 / (4 * c) = a + -1 / 4 * c⁻¹ * (b * b) := by
      field_simp
      ring
    have h2 : Real.pi / -c = Real.pi * (-1 * c⁻¹) := by
      rw [div_eq_mul_inv, inv_neg]
      ring
    rw [h1, h2]
    simp [Value.mul, Value.add, Value.inv, hne, Function1.apply, Functions.expR,
      Functions.sqrtR, Functions.pi, Numeric.denote, hle]
  · have hc' : 0 ≤ c := not_lt.1 hc
    have hn : partialIntegral volume f = none := by
      apply if_neg
      rintro ⟨_, hi⟩
      rw [he] at hi
      have hi' := hi.const_mul s⁻¹
      have he2 : (fun x => s⁻¹ * (s * (Q x * Real.exp (a + b * x + c * x ^ 2)))) =
          fun x => Q x * Real.exp (a + b * x + c * x ^ 2) := by
        funext x
        rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
      rw [he2] at hi'
      exact hpos hc' hi'
    have hroot : Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv (some c)))) =
        none := by
      rw [hmn, hpi]
      rcases hc'.eq_or_lt with h0 | hlt
      · subst h0
        simp [Value.inv, Value.mul, Function1.apply]
      · have hneg' : ¬ Real.pi * c⁻¹ ≤ 0 := not_le.2 (mul_pos Real.pi_pos (inv_pos.2 hlt))
        simp [Value.inv, hlt.ne', Value.mul, Function1.apply, Functions.sqrtR, Functions.pi,
          Numeric.denote, hneg']
    have right : ∀ X : Option ℝ, Value.mul k (Value.mul X none) = none := fun X => by
      cases k <;> cases X <;> rfl
    rw [hn, hroot, right]
    rfl

/-- The checks of a Gaussian integral under a rational polynomial where the
curvature is a term: the polynomial is not zero, and the rows are its moments
as a polynomial in the linear coefficient and in `h = -1/(2·c₂)`. -/
def curvatureCheck (P : List ℚ) (K : List (List ℚ)) : Bool :=
  !polyZero P && poly2Zero (poly2Add K (poly2Scale (-1) (gaussMoments2 P 0 [[1]] [])))

/-- The integral of a rational polynomial times the exponential of a quadratic
whose curvature does not mention the variable either: the moments at the
linear coefficient and at `h = -1/(2·c₂)`, times
`exp(c₀ - c₁²/(4·c₂))·√(-π/c₂)`, under a scale that is not zero where it is
defined. Where the curvature is not negative the integrand is defined but not
integrable, and the result is missing with it: the inverse at zero, the root
above it. A factor that vanishes would leave the zero function there, which
has an integral. -/
theorem gaussian_partialIntegral_curvature {f : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (K : List (List ℚ))
    (hf : Bell f S none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (hK : curvatureCheck P K = true) (hS : scaleNonvanishing S)
    {k g m u pi : Option ℝ} {ms : List (Option ℝ)}
    (hm : MomentTerms c1 (curvatureCoefs (Value.mul u (Value.inv c2)) K 0) K ms) (hk : Sums ms k)
    (hu : u = some (Numeric.denote (s := .real) (-1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hmn : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    partialIntegral volume f = scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply
        (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))) := by
  simp only [curvatureCheck, Bool.and_eq_true, Bool.not_eq_true'] at hK
  obtain ⟨hP, hKz⟩ := hK
  have hfx : ∀ x, f x = scaleBy S (Value.mul (some (polyEval P x)) (Functions.expR.apply (E x))) :=
    fun x => hf.plain x
  have undefined : (∀ x, E x = none) → partialIntegral volume f = none := fun hn => by
    apply if_neg
    intro hdef
    obtain ⟨r, hr⟩ := hdef.1 0
    rw [hfx, hn] at hr
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul, Function1.apply] at hr
  rcases c0 with _ | a
  · rw [undefined (hE.missing (Or.inl rfl)), curvature_missing S k g m pi (Or.inl rfl)]
  rcases c1 with _ | b
  · rw [undefined (hE.missing (Or.inr (Or.inl rfl))),
      curvature_missing S k g m pi (Or.inr (Or.inl rfl))]
  rcases c2 with _ | c
  · rw [undefined (hE.missing (Or.inr (Or.inr rfl))),
      curvature_missing S k g m pi (Or.inr (Or.inr rfl))]
  have hE' : ∀ x, E x = some (a + b * x + c * x ^ 2) := fun x => by
    rw [hE.equation]
    show some (a + (b * x + c * x ^ 2)) = some (a + b * x + c * x ^ 2)
    congr 1
    ring
  have hneg : c < 0 → ∃ κ : ℝ, k = some κ ∧
      Integrable (fun x : ℝ => polyEval P x * Real.exp (a + b * x + c * x ^ 2)) volume ∧
      (∫ x : ℝ, polyEval P x * Real.exp (a + b * x + c * x ^ 2)) =
        κ * (Real.exp (a - b ^ 2 / (4 * c)) * √(Real.pi / (-c))) := fun hc => by
    obtain ⟨hi, hv⟩ := gaussian_moments2 a b hc P
    have hne : c ≠ 0 := hc.ne
    have hhv : Value.mul u (Value.inv (some c)) = some (-1 / (2 * c)) := by
      rw [hu]
      simp [Value.mul, Value.inv, hne, Numeric.denote]
      field_simp
    rw [hhv] at hm
    have hkv : k = some (poly2Eval K b (-1 / (2 * c))) := by
      rw [hk.value, hm.value b rfl (curvatureCoefs_defined _ K 0), momentValue_curvature]
      simp
    have hz := poly2Eval_zero hKz b (-1 / (2 * c))
    rw [poly2Eval_add, poly2Eval_scale] at hz
    have hK' : poly2Eval (gaussMoments2 P 0 [[1]] []) b (-1 / (2 * c)) =
        poly2Eval K b (-1 / (2 * c)) := by
      push_cast at hz
      linarith
    exact ⟨_, hkv, hi, by rw [hv, hK']⟩
  have hpos : 0 ≤ c →
      ¬ Integrable (fun x : ℝ => polyEval P x * Real.exp (a + b * x + c * x ^ 2)) volume :=
    fun hc => polynomial_exp_quadratic_not_integrable hP a b hc
  rcases S with _ | _ | s
  · have h := curvature_scaled (f := f) (fun x => polyEval P x) one_ne_zero (fun x => by
      rw [hfx, hE']
      simp [scaleBy, Value.mul, Function1.apply, Functions.expR]) hneg hpos hg hmn hpi
    rw [h]
    exact Value.mul_one_left _
  · apply if_neg
    intro hdef
    obtain ⟨r, hr⟩ := hdef.1 0
    rw [hfx] at hr
    simp [scaleBy, Value.mul] at hr
  · exact curvature_scaled (fun x => polyEval P x) (hS s rfl) (fun x => by
      rw [hfx, hE']
      simp [scaleBy, Value.mul, Function1.apply, Functions.expR]) hneg hpos hg hmn hpi

/-! The same under a polynomial whose coefficients do not mention the
variable: the integral is linear in them, and each meets the moments of its
power, a table of rows. -/

/-- The polynomial of the real values of the coefficients. -/
noncomputable def realPoly : List (Option (Option ℝ)) → Polynomial ℝ
  | [] => 0
  | c :: cs => Polynomial.C (coefReal c) + Polynomial.X * realPoly cs

theorem eval_realPoly (cs : List (Option (Option ℝ))) (x : ℝ) :
    (realPoly cs).eval x = realEval cs x := by
  induction cs with
  | nil => simp [realPoly, realEval]
  | cons c cs ih => simp [realPoly, realEval, ih]

/-- A coefficient that is present and not zero where it is defined. -/
inductive SomeNonvanishing : List (Option (Option ℝ)) → Prop
  | here {c : Option ℝ} {cs : List (Option (Option ℝ))} (h : Nonvanishing c) :
      SomeNonvanishing (some c :: cs)
  | later {c : Option (Option ℝ)} {cs : List (Option (Option ℝ))} (h : SomeNonvanishing cs) :
      SomeNonvanishing (c :: cs)

/-- Such a polynomial is not zero where its coefficients are defined. -/
theorem SomeNonvanishing.realPoly_ne_zero {cs : List (Option (Option ℝ))}
    (h : SomeNonvanishing cs) (hd : some none ∉ cs) : realPoly cs ≠ 0 := by
  induction h with
  | @here c cs hn =>
    intro h0
    rcases c with _ | v
    · exact hd (by simp)
    · have h1 := congrArg (fun p : Polynomial ℝ => p.coeff 0) h0
      simp [realPoly, coefReal] at h1
      exact hn v rfl h1
  | @later c cs _ ih =>
    intro h0
    have hz : realPoly cs = 0 := by
      ext n
      have h1 := congrArg (fun p : Polynomial ℝ => p.coeff (n + 1)) h0
      simpa [realPoly, Polynomial.coeff_C] using h1
    exact ih (fun hm => hd (by simp [hm])) hz

/-- The sum of the coefficients times their tables at the linear coefficient
and at `h`. -/
def momentValue2 (b h : ℝ) : List (Option (Option ℝ)) → List (List (List ℚ)) → ℝ
  | c :: cs, K :: Ks => coefReal c * poly2Eval K b h + momentValue2 b h cs Ks
  | _, _ => 0

/-- The tables of moments: table `j` is the polynomial of the moments of
`xʲ·P`, and it has a row that is not zero. -/
def curvatureRows (P : List ℚ) : List (List (List ℚ)) → ℕ → List (List ℚ) → List (List ℚ) → Bool
  | [], _, _, _ => true
  | K :: Ks, j, μ, μ' =>
    poly2Zero (poly2Add K (poly2Scale (-1) (gaussMoments2 P j μ μ'))) && !poly2Zero K &&
      curvatureRows P Ks (j + 1) ([] :: poly2Add (poly2Shift μ) (poly2Scale j μ')) μ

theorem curvatureRows_nonzero (P : List ℚ) :
    ∀ (Ks : List (List (List ℚ))) (j : ℕ) (μ μ' : List (List ℚ)),
      curvatureRows P Ks j μ μ' = true → ∀ K ∈ Ks, poly2Zero K = false := by
  intro Ks
  induction Ks with
  | nil => intro _ _ _ _ K hK; simp at hK
  | cons K Ks ih =>
    intro j μ μ' h K' hK'
    simp only [curvatureRows, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases List.mem_cons.1 hK' with rfl | hmem
    · exact h.1.2
    · exact ih _ _ _ h.2 K' hmem

/-- The moments of a polynomial with such coefficients times a rational one:
coefficient by coefficient, each against its table. -/
theorem curvatureRows_integral (c0 c1 : ℝ) {c2 : ℝ} (hc : c2 < 0) {h : ℝ}
    (hh : h * (2 * c2) = -1) (G : ℝ) (P : List ℚ) :
    ∀ (cs : List (Option (Option ℝ))) (Ks : List (List (List ℚ))) (j : ℕ) (μ μ' : List (List ℚ)),
      cs.length = Ks.length → curvatureRows P Ks j μ μ' = true →
      (∫ x : ℝ, x ^ j * Real.exp (c0 + c1 * x + c2 * x ^ 2)) = poly2Eval μ c1 h * G →
      (j : ℝ) * (∫ x : ℝ, x ^ (j - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        j * (poly2Eval μ' c1 h * G) →
      Integrable (fun x : ℝ => x ^ j * realEval cs x * polyEval P x *
          Real.exp (c0 + c1 * x + c2 * x ^ 2)) ∧
        (∫ x : ℝ, x ^ j * realEval cs x * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
          momentValue2 c1 h cs Ks * G := by
  intro cs
  induction cs with
  | nil =>
    intro Ks j μ μ' _ _ _ _
    simp [realEval, momentValue2]
  | cons c cs ih =>
    intro Ks j μ μ' hlen hrows h1 h2
    cases Ks with
    | nil => simp at hlen
    | cons K Ks =>
      simp only [curvatureRows, Bool.and_eq_true] at hrows
      obtain ⟨⟨hK, _⟩, hrest⟩ := hrows
      obtain ⟨hn1, hn2⟩ := moment_next2 c0 c1 hc hh G j μ μ' h1 h2
      obtain ⟨hi, hv⟩ := ih Ks (j + 1) _ μ (by simpa using hlen) hrest hn1 hn2
      obtain ⟨hpi, hpv⟩ := gaussMoments2_integral c0 c1 hc hh G P j μ μ' h1 h2
      have hz := poly2Eval_zero hK c1 h
      rw [poly2Eval_add, poly2Eval_scale] at hz
      have hK' : poly2Eval (gaussMoments2 P j μ μ') c1 h = poly2Eval K c1 h := by
        push_cast at hz
        linarith
      have hsplit : (fun x : ℝ => x ^ j * realEval (c :: cs) x * polyEval P x *
          Real.exp (c0 + c1 * x + c2 * x ^ 2)) = fun x =>
          coefReal c * (x ^ j * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) +
            x ^ (j + 1) * realEval cs x * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2) := by
        funext x
        simp only [realEval]
        ring
      refine ⟨by rw [hsplit]; exact (hpi.const_mul _).add hi, ?_⟩
      rw [hsplit, integral_add (hpi.const_mul _) hi, integral_const_mul, hpv, hv, hK']
      simp only [momentValue2]
      ring

/-- A coefficient times the power of `h` in front of a row; the first row has
none. -/
def scaledPower (c h : Option ℝ) : ℕ → Option ℝ
  | 0 => c
  | l + 1 => Value.mul c (curvaturePower h (l + 1))

/-- The coefficients of the rows of a table: its coefficient times the powers
of `h`, absent in front of a row that is zero and where the coefficient is. -/
def tableCoefs (h : Option ℝ) : Option (Option ℝ) → List (List ℚ) → ℕ → List (Option (Option ℝ))
  | _, [], _ => []
  | none, _ :: K, l => none :: tableCoefs h none K (l + 1)
  | some c, κ :: K, l =>
    (if polyZero κ then none else some (scaledPower c h l)) :: tableCoefs h (some c) K (l + 1)

/-- The coefficients of the rows of all the tables, in order. -/
def momentCoefs (h : Option ℝ) :
    List (Option (Option ℝ)) → List (List (List ℚ)) → List (Option (Option ℝ))
  | c :: cs, K :: Ks => tableCoefs h c K 0 ++ momentCoefs h cs Ks
  | _, _ => []

private theorem scaledPower_some (a h : ℝ) (l : ℕ) :
    scaledPower (some a) (some h) l = some (a * h ^ l) := by
  rcases l with _ | l
  · simp [scaledPower]
  · simp [scaledPower, curvaturePower_some, Value.mul]

private theorem scaledPower_none (h : Option ℝ) (l : ℕ) : scaledPower none h l = none := by
  rcases l with _ | l <;> rfl

private theorem tableCoefs_length (h : Option ℝ) (c : Option (Option ℝ)) (K : List (List ℚ))
    (l : ℕ) : (tableCoefs h c K l).length = K.length := by
  induction K generalizing l with
  | nil => cases c <;> rfl
  | cons κ K ih => cases c <;> simp [tableCoefs, ih]

private theorem momentValue_append (b : ℝ) {cs : List (Option (Option ℝ))} {κs : List (List ℚ)}
    (hl : cs.length = κs.length) (cs' : List (Option (Option ℝ))) (κs' : List (List ℚ)) :
    momentValue b (cs ++ cs') (κs ++ κs') = momentValue b cs κs + momentValue b cs' κs' := by
  induction cs generalizing κs with
  | nil =>
    cases κs with
    | nil => simp [momentValue]
    | cons κ κs => simp at hl
  | cons c cs ih =>
    cases κs with
    | nil => simp at hl
    | cons κ κs =>
      simp only [List.cons_append, momentValue, ih (by simpa using hl)]
      ring

private theorem momentValue_table (b h : ℝ) {c : Option (Option ℝ)} (hc : c ≠ some none)
    (K : List (List ℚ)) (l : ℕ) :
    momentValue b (tableCoefs (some h) c K l) K = coefReal c * (h ^ l * poly2Eval K b h) := by
  induction K generalizing l with
  | nil => cases c <;> simp [tableCoefs, momentValue, poly2Eval]
  | cons κ K ih =>
    rcases c with _ | _ | a
    · simp [tableCoefs, momentValue, coefReal, ih]
    · exact absurd rfl hc
    · simp only [tableCoefs, momentValue, poly2Eval, ih (l + 1)]
      by_cases hz : polyZero κ = true
      · rw [if_pos hz, polyEval_zero hz]
        simp only [coefReal]
        ring
      · rw [if_neg hz, scaledPower_some]
        simp only [coefReal]
        ring

theorem momentValue_coefs (b h : ℝ) :
    ∀ (cs : List (Option (Option ℝ))) (Ks : List (List (List ℚ))), some none ∉ cs →
      momentValue b (momentCoefs (some h) cs Ks) Ks.flatten = momentValue2 b h cs Ks := by
  intro cs
  induction cs with
  | nil => intro Ks _; cases Ks <;> simp [momentCoefs, momentValue, momentValue2]
  | cons c cs ih =>
    intro Ks hd
    cases Ks with
    | nil => simp [momentCoefs, momentValue, momentValue2]
    | cons K Ks =>
      have hc : c ≠ some none := fun hc => hd (by simp [hc])
      have hcs : some none ∉ cs := fun hm => hd (by simp [hm])
      rw [momentCoefs, List.flatten_cons, momentValue_append b (tableCoefs_length _ _ _ _),
        momentValue_table b h hc, ih Ks hcs]
      simp [momentValue2]

private theorem tableCoefs_defined (h : ℝ) {c : Option (Option ℝ)} (hc : c ≠ some none)
    (K : List (List ℚ)) (l : ℕ) : some none ∉ tableCoefs (some h) c K l := by
  induction K generalizing l with
  | nil => cases c <;> simp [tableCoefs]
  | cons κ K ih =>
    rcases c with _ | _ | a
    · simp only [tableCoefs, List.mem_cons, not_or]
      exact ⟨by simp, ih (l + 1)⟩
    · exact absurd rfl hc
    · simp only [tableCoefs, List.mem_cons, not_or]
      refine ⟨?_, ih (l + 1)⟩
      split_ifs <;> simp [scaledPower_some]

theorem momentCoefs_defined (h : ℝ) :
    ∀ (cs : List (Option (Option ℝ))) (Ks : List (List (List ℚ))), some none ∉ cs →
      some none ∉ momentCoefs (some h) cs Ks := by
  intro cs
  induction cs with
  | nil => intro Ks _; cases Ks <;> simp [momentCoefs]
  | cons c cs ih =>
    intro Ks hd
    cases Ks with
    | nil => simp [momentCoefs]
    | cons K Ks =>
      have hc : c ≠ some none := fun hc => hd (by simp [hc])
      have hcs : some none ∉ cs := fun hm => hd (by simp [hm])
      simp only [momentCoefs, List.mem_append, not_or]
      exact ⟨tableCoefs_defined h hc K 0, ih Ks hcs⟩

/-- An undefined coefficient is in front of a row of its table that is not
zero. -/
private theorem tableCoefs_undefined (h : Option ℝ) {K : List (List ℚ)}
    (hK : poly2Zero K = false) (l : ℕ) : some none ∈ tableCoefs h (some none) K l := by
  induction K generalizing l with
  | nil => simp [poly2Zero] at hK
  | cons κ K ih =>
    simp only [tableCoefs, List.mem_cons]
    by_cases hz : polyZero κ = true
    · right
      refine ih ?_ (l + 1)
      simpa [poly2Zero, hz] using hK
    · left
      rw [if_neg hz, scaledPower_none]

theorem momentCoefs_undefined (h : Option ℝ) :
    ∀ (cs : List (Option (Option ℝ))) (Ks : List (List (List ℚ))), cs.length = Ks.length →
      (∀ K ∈ Ks, poly2Zero K = false) → some none ∈ cs → some none ∈ momentCoefs h cs Ks := by
  intro cs
  induction cs with
  | nil => intro Ks _ _ hu; simp at hu
  | cons c cs ih =>
    intro Ks hl hK hu
    cases Ks with
    | nil => simp at hl
    | cons K Ks =>
      simp only [momentCoefs, List.mem_append]
      rcases List.mem_cons.1 hu with hu | hu
      · left
        rw [← hu]
        exact tableCoefs_undefined h (hK K (by simp)) 0
      · right
        exact ih Ks (by simpa using hl) (fun K' hK' => hK K' (by simp [hK'])) hu

/-- The checks of a Gaussian integral under a polynomial whose coefficients do
not mention the variable where the curvature is a term: the rational polynomial
is not zero, and the tables are the moments of the powers times it. -/
def curvatureMomentsCheck (P : List ℚ) (Ks : List (List (List ℚ))) : Bool :=
  !polyZero P && curvatureRows P Ks 0 [[1]] []

/-- The integral of a polynomial whose coefficients do not mention the
variable times a rational one and the exponential of a quadratic whose
curvature does not mention it either. One of the coefficients is not zero
where it is defined, by its form, so the polynomial is not zero where they are
all defined: where the curvature is not negative the integrand is then not
integrable, and the result is missing with it. A coefficient that is undefined
leaves the integrand undefined everywhere, and the sum with it. -/
theorem gaussian_partialIntegral_curvature_moments {f : ℝ → Option ℝ} {S : Option (Option ℝ)}
    {cs : List (Option (Option ℝ))} {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ}
    (Ks : List (List (List ℚ))) (hf : Bell f S (some cs) P (some E))
    (hE : Quadratic E (some c0) (some c1) (some c2))
    (hK : curvatureMomentsCheck P Ks = true) (hl : cs.length = Ks.length)
    (hS : scaleNonvanishing S) (hN : SomeNonvanishing cs)
    {k g m u pi : Option ℝ} {ms : List (Option ℝ)}
    (hm : MomentTerms c1 (momentCoefs (Value.mul u (Value.inv c2)) cs Ks) Ks.flatten ms)
    (hk : Sums ms k)
    (hu : u = some (Numeric.denote (s := .real) (-1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hmn : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    partialIntegral volume f = scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply
        (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))) := by
  simp only [curvatureMomentsCheck, Bool.and_eq_true, Bool.not_eq_true'] at hK
  obtain ⟨hP, hrows⟩ := hK
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  have missing : (∀ x, f x = none) → partialIntegral volume f = none := fun hn => by
    apply if_neg
    intro hdef
    obtain ⟨v, hv⟩ := hdef.1 0
    rw [hn] at hv
    cases hv
  have hfn : ∀ x, (symEval cs x = none ∨ E x = none) → f x = none := fun x hx => by
    rw [hf.equation, symPart, expPart]
    rcases hx with hx | hx <;> rw [hx] <;> rcases S with _ | _ | s <;>
      simp [scaleBy, Value.mul, Function1.apply]
  rcases c0 with _ | a
  · rw [missing fun x => hfn x (Or.inr (hE.missing (Or.inl rfl) x)),
      curvature_missing S k g m pi (Or.inl rfl)]
  rcases c1 with _ | b
  · rw [missing fun x => hfn x (Or.inr (hE.missing (Or.inr (Or.inl rfl)) x)),
      curvature_missing S k g m pi (Or.inr (Or.inl rfl))]
  rcases c2 with _ | c
  · rw [missing fun x => hfn x (Or.inr (hE.missing (Or.inr (Or.inr rfl)) x)),
      curvature_missing S k g m pi (Or.inr (Or.inr rfl))]
  by_cases hd : some none ∈ cs
  · have hk' : k = none := by
      rw [hk.value, hm.undefined
        (momentCoefs_undefined _ cs Ks hl (curvatureRows_nonzero P Ks 0 _ _ hrows) hd)]
    rw [missing fun x => hfn x (Or.inl ((symEval_none_iff cs x).2 hd)), hk']
    exact hnone.symm
  have hE' : ∀ x, E x = some (a + b * x + c * x ^ 2) := fun x => by
    rw [hE.equation]
    show some (a + (b * x + c * x ^ 2)) = some (a + b * x + c * x ^ 2)
    congr 1
    ring
  have hfx : ∀ x, f x = scaleBy S
      (some (realEval cs x * polyEval P x * Real.exp (a + b * x + c * x ^ 2))) := fun x => by
    rw [hf.equation, symPart, expPart, hE', symEval_real hd]
    simp [Value.mul, Function1.apply, Functions.expR]
  have hneg : c < 0 → ∃ κ : ℝ, k = some κ ∧
      Integrable (fun x : ℝ => realEval cs x * polyEval P x *
        Real.exp (a + b * x + c * x ^ 2)) volume ∧
      (∫ x : ℝ, realEval cs x * polyEval P x * Real.exp (a + b * x + c * x ^ 2)) =
        κ * (Real.exp (a - b ^ 2 / (4 * c)) * √(Real.pi / (-c))) := fun hc => by
    have hne : c ≠ 0 := hc.ne
    have hh : (-1 / (2 * c)) * (2 * c) = -1 := by field_simp
    obtain ⟨hi, hv⟩ := curvatureRows_integral a b hc hh
      (Real.exp (a - b ^ 2 / (4 * c)) * √(Real.pi / (-c))) P cs Ks 0 [[1]] [] hl hrows
      (by simp [poly2Eval, polyEval, gaussian_integral a b c hc]) (by simp)
    simp only [pow_zero, one_mul] at hi hv
    have hhv : Value.mul u (Value.inv (some c)) = some (-1 / (2 * c)) := by
      rw [hu]
      simp [Value.mul, Value.inv, hne, Numeric.denote]
      field_simp
    rw [hhv] at hm
    have hkv : k = some (momentValue2 b (-1 / (2 * c)) cs Ks) := by
      rw [hk.value, hm.value b rfl (momentCoefs_defined _ cs Ks hd),
        momentValue_coefs b _ cs Ks hd]
    exact ⟨_, hkv, hi, hv⟩
  have hpos : 0 ≤ c → ¬ Integrable (fun x : ℝ => realEval cs x * polyEval P x *
      Real.exp (a + b * x + c * x ^ 2)) volume := fun hc hi => by
    have hq : realPoly cs * QSym.Limit.toPoly P ≠ 0 :=
      mul_ne_zero (hN.realPoly_ne_zero hd) (QSym.Limit.toPoly_ne_zero hP)
    refine real_polynomial_exp_quadratic_not_integrable hq a b hc ?_
    simpa only [Polynomial.eval_mul, eval_realPoly, QSym.Limit.eval_toPoly] using hi
  rcases S with _ | _ | s
  · have h := curvature_scaled (f := f) (fun x => realEval cs x * polyEval P x) one_ne_zero
      (fun x => by
        rw [hfx]
        simp [scaleBy]) hneg hpos hg hmn hpi
    rw [h]
    exact Value.mul_one_left _
  · apply if_neg
    intro hdef
    obtain ⟨r, hr⟩ := hdef.1 0
    rw [hfx] at hr
    simp [scaleBy, Value.mul] at hr
  · exact curvature_scaled (fun x => realEval cs x * polyEval P x) (hS s rfl) (fun x => by
      rw [hfx]
      simp [scaleBy, Value.mul]) hneg hpos hg hmn hpi

/-! Factors that may vanish. Where a factor is zero the integrand is the zero
function, which has an integral whatever the curvature is: the closed form
stands under the mask of those factors. A mask that fails hides what is under
it, so the result comes after everything the integrand is strict in. -/

/-- After values that must be defined. -/
def after : List (Option ℝ) → Option ℝ → Option ℝ
  | [], y => y
  | p :: ps, y => p.bind fun _ => after ps y

theorem after_none {ps : List (Option ℝ)} (h : none ∈ ps) (y : Option ℝ) : after ps y = none := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    rcases p with _ | v
    · rfl
    · show after ps y = none
      exact ih (by simpa using h)

theorem after_defined {ps : List (Option ℝ)} (h : none ∉ ps) (y : Option ℝ) : after ps y = y := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with _ | v
    · exact absurd (by simp) h
    · show after ps y = y
      exact ih fun hm => h (by simp [hm])

/-- A function that is zero everywhere has the integral zero. -/
theorem partialIntegral_zero {f : ℝ → Option ℝ} (h : ∀ x, f x = some 0) :
    partialIntegral volume f = some 0 := by
  have he : (fun x => (f x).getD 0) = fun _ : ℝ => (0 : ℝ) := by
    funext x
    rw [h]
    rfl
  rw [partialIntegral_valid volume f (fun x => ⟨_, h x⟩) (by rw [he]; exact integrable_zero _ _ _),
    he]
  simp

/-- The same integral under a scale that may vanish: under the mask of the
scale, after the scale and the coefficients of the exponent. -/
theorem gaussian_partialIntegral_curvature_masked {f : ℝ → Option ℝ} {c : Option ℝ}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (K : List (List ℚ))
    (hf : Bell f (some c) none P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (hK : curvatureCheck P K = true) {k g m u pi : Option ℝ} {ms : List (Option ℝ)}
    (hm : MomentTerms c1 (curvatureCoefs (Value.mul u (Value.inv c2)) K 0) K ms) (hk : Sums ms k)
    (hu : u = some (Numeric.denote (s := .real) (-1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hmn : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    partialIntegral volume f = after [c, c0, c1, c2] (Value.mask (Value.nonzero c)
      (Value.mul c (Value.mul k (Value.mul
        (Functions.expR.apply
          (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
        (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))))) := by
  have hfx : ∀ x, f x =
      Value.mul c (Value.mul (some (polyEval P x)) (Functions.expR.apply (E x))) :=
    fun x => hf.plain x
  have missing : (∀ x, f x = none) → partialIntegral volume f = none := fun hn => by
    apply if_neg
    intro hdef
    obtain ⟨v, hv⟩ := hdef.1 0
    rw [hn] at hv
    cases hv
  have hexp : ∀ x, E x = none → f x = none := fun x hx => by
    rw [hfx, hx]
    cases c <;> simp [Value.mul, Function1.apply]
  rcases c with _ | s
  · rw [missing fun x => by rw [hfx]; rfl]
    rfl
  rcases c0 with _ | a
  · rw [missing fun x => hexp x (hE.missing (Or.inl rfl) x)]
    rfl
  rcases c1 with _ | b
  · rw [missing fun x => hexp x (hE.missing (Or.inr (Or.inl rfl)) x)]
    rfl
  rcases c2 with _ | q
  · rw [missing fun x => hexp x (hE.missing (Or.inr (Or.inr rfl)) x)]
    rfl
  show partialIntegral volume f = Value.mask (Value.nonzero (some s)) _
  by_cases hs : s = 0
  · subst hs
    have hEx : ∀ x, E x = some (a + (b * x + q * x ^ 2)) := fun x => by
      rw [hE.equation]
      rfl
    rw [partialIntegral_zero fun x => by
      rw [hfx, hEx]
      simp [Value.mul, Function1.apply, Functions.expR]]
    simp [Value.nonzero, Value.mask]
  · rw [gaussian_partialIntegral_curvature K hf hE hK (fun t ht => by cases ht; exact hs) hm hk hu
      hg hmn hpi]
    simp [Value.nonzero, hs, Value.mask, scaleBy]

/-- The scale as a list of values. -/
def scaleList : Option (Option ℝ) → List (Option ℝ)
  | none => []
  | some c => [c]

/-- The coefficients that are present. -/
def presentCoefs : List (Option (Option ℝ)) → List (Option ℝ)
  | [] => []
  | none :: cs => presentCoefs cs
  | some c :: cs => c :: presentCoefs cs

theorem mem_presentCoefs (cs : List (Option (Option ℝ))) (c : Option ℝ) :
    c ∈ presentCoefs cs ↔ some c ∈ cs := by
  induction cs with
  | nil => simp [presentCoefs]
  | cons d cs ih => rcases d with _ | d <;> simp [presentCoefs, ih]

/-- The test that a coefficient that is present is not zero; none where none
is present. -/
noncomputable def anyNonzero : List (Option (Option ℝ)) → Option (Option Bool)
  | [] => none
  | none :: cs => anyNonzero cs
  | some c :: cs =>
    match anyNonzero cs with
    | none => some (Value.nonzero c)
    | some g => some (Value.or (Value.nonzero c) g)

private theorem anyNonzero_absent :
    ∀ cs : List (Option (Option ℝ)), anyNonzero cs = none → ∀ c : Option ℝ, some c ∉ cs := by
  intro cs
  induction cs with
  | nil => intro _ c hc; simp at hc
  | cons d cs ih =>
    intro h c hc
    rcases d with _ | d
    · exact ih h c (by simpa using hc)
    · simp only [anyNonzero] at h
      split at h <;> cases h

/-- Where the coefficients are defined that test says whether one of them is
not zero. -/
private theorem anyNonzero_value :
    ∀ (cs : List (Option (Option ℝ))) (g : Option Bool), some none ∉ cs → anyNonzero cs = some g →
      ∃ b : Bool, g = some b ∧ (b = true ↔ ∃ v : ℝ, some (some v) ∈ cs ∧ v ≠ 0) := by
  intro cs
  induction cs with
  | nil => intro g _ h; cases h
  | cons d cs ih =>
    intro g hd h
    have hcs : some none ∉ cs := fun hm => hd (by simp [hm])
    rcases d with _ | _ | v0
    · obtain ⟨b, hb, hiff⟩ := ih g hcs h
      exact ⟨b, hb, by simpa using hiff⟩
    · exact absurd (by simp) hd
    · simp only [anyNonzero] at h
      cases hrest : anyNonzero cs with
      | none =>
        rw [hrest] at h
        refine ⟨decide (v0 ≠ 0), by rw [← Option.some.inj h]; simp [Value.nonzero], ?_⟩
        constructor
        · intro hv
          exact ⟨v0, by simp, of_decide_eq_true hv⟩
        · rintro ⟨v, hv, hv0⟩
          rcases List.mem_cons.1 hv with he | hm
          · have : v = v0 := by simpa using he
            rw [← this]
            exact decide_eq_true hv0
          · exact absurd hm (anyNonzero_absent cs hrest (some v))
      | some g' =>
        rw [hrest] at h
        obtain ⟨b, hb, hiff⟩ := ih g' hcs hrest
        refine ⟨decide (v0 ≠ 0) || b, by
          rw [← Option.some.inj h, hb]
          by_cases hz : v0 = 0 <;> cases b <;> simp [Value.nonzero, Value.or, hz], ?_⟩
        constructor
        · intro hv
          rcases Bool.or_eq_true_iff.1 hv with h1 | h1
          · exact ⟨v0, by simp, of_decide_eq_true h1⟩
          · obtain ⟨v, hv', hv0⟩ := hiff.1 h1
            exact ⟨v, by simp [hv'], hv0⟩
        · rintro ⟨v, hv, hv0⟩
          rcases List.mem_cons.1 hv with he | hm
          · have : v = v0 := by simpa using he
            rw [← this]
            simp [hv0]
          · simp [hiff.2 ⟨v, hm, hv0⟩]

theorem SomeNonvanishing.exists {cs : List (Option (Option ℝ))} (h : SomeNonvanishing cs)
    (hd : some none ∉ cs) : ∃ v : ℝ, some (some v) ∈ cs ∧ v ≠ 0 := by
  induction h with
  | @here c cs hn =>
    rcases c with _ | v
    · exact absurd (by simp) hd
    · exact ⟨v, by simp, hn v rfl⟩
  | @later c cs _ ih =>
    obtain ⟨v, hv, hv0⟩ := ih fun hm => hd (by simp [hm])
    exact ⟨v, by simp [hv], hv0⟩

theorem SomeNonvanishing.of_mem : ∀ {cs : List (Option (Option ℝ))} {v : ℝ},
    some (some v) ∈ cs → v ≠ 0 → SomeNonvanishing cs := by
  intro cs
  induction cs with
  | nil => intro v hv; simp at hv
  | cons c cs ih =>
    intro v hv hv0
    rcases List.mem_cons.1 hv with he | hm
    · rw [← he]
      exact .here fun t ht => by cases ht; exact hv0
    · exact .later (ih hm hv0)

/-- A polynomial whose coefficients are all zero is zero. -/
private theorem realEval_eq_zero {cs : List (Option (Option ℝ))}
    (h : ∀ v : ℝ, some (some v) ∈ cs → v = 0) (x : ℝ) : realEval cs x = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : coefReal c = 0 := by
      rcases c with _ | _ | v
      · rfl
      · rfl
      · exact h v (by simp)
    simp only [realEval, hc, ih fun v hv => h v (by simp [hv])]
    ring

/-- The real value of a scale; one where there is none. -/
def scaleReal : Option (Option ℝ) → ℝ
  | some (some s) => s
  | _ => 1

/-- The mask of the factors that may vanish: a scale in front of a polynomial
with a coefficient that cannot, the coefficients under a scale that cannot,
or both. -/
inductive VanishMask : Option (Option ℝ) → List (Option (Option ℝ)) → Option Bool → Prop
  | scale {c : Option ℝ} {cs : List (Option (Option ℝ))} (h : SomeNonvanishing cs) :
      VanishMask (some c) cs (Value.nonzero c)
  | polynomial {S : Option (Option ℝ)} {cs : List (Option (Option ℝ))} {g : Option Bool}
      (hS : scaleNonvanishing S) (h : anyNonzero cs = some g) : VanishMask S cs g
  | both {c : Option ℝ} {cs : List (Option (Option ℝ))} {g : Option Bool}
      (h : anyNonzero cs = some g) : VanishMask (some c) cs (Value.and (Value.nonzero c) g)

/-- Where the scale and the coefficients are defined the mask says whether the
scale and one of the coefficients are not zero. -/
theorem VanishMask.value {S : Option (Option ℝ)} {cs : List (Option (Option ℝ))} {G : Option Bool}
    (h : VanishMask S cs G) (hS : S ≠ some none) (hd : some none ∉ cs) :
    ∃ b : Bool, G = some b ∧
      (b = true ↔ scaleReal S ≠ 0 ∧ ∃ v : ℝ, some (some v) ∈ cs ∧ v ≠ 0) := by
  cases h with
  | @scale c _ hN =>
    rcases c with _ | s
    · exact absurd rfl hS
    · refine ⟨decide (s ≠ 0), by simp [Value.nonzero], ?_⟩
      constructor
      · intro hs
        exact ⟨of_decide_eq_true hs, hN.exists hd⟩
      · rintro ⟨hs, _⟩
        exact decide_eq_true hs
  | polynomial hSn hg =>
    obtain ⟨b, hb, hiff⟩ := anyNonzero_value cs G hd hg
    refine ⟨b, hb, ?_⟩
    have hs : scaleReal S ≠ 0 := by
      rcases S with _ | _ | s
      · simp [scaleReal]
      · exact absurd rfl hS
      · exact hSn s rfl
    constructor
    · intro hbt
      exact ⟨hs, hiff.1 hbt⟩
    · rintro ⟨_, hv⟩
      exact hiff.2 hv
  | @both c _ g hg =>
    obtain ⟨b, hb, hiff⟩ := anyNonzero_value cs g hd hg
    rcases c with _ | s
    · exact absurd rfl hS
    · refine ⟨decide (s ≠ 0) && b, by
        rw [hb]
        by_cases hz : s = 0 <;> cases b <;> simp [Value.nonzero, Value.and, hz], ?_⟩
      constructor
      · intro hbt
        obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hbt
        exact ⟨of_decide_eq_true h1, hiff.1 h2⟩
      · rintro ⟨hs, hv⟩
        simp [scaleReal] at hs
        simp [hs, hiff.2 hv]

/-- The same under a polynomial whose coefficients may all vanish, or a scale
that may: under the mask of those factors, after the scale, the coefficients
and the coefficients of the exponent. -/
theorem gaussian_partialIntegral_curvature_moments_masked {f : ℝ → Option ℝ}
    {S : Option (Option ℝ)} {cs : List (Option (Option ℝ))} {P : List ℚ} {E : ℝ → Option ℝ}
    {c0 c1 c2 : Option ℝ} (Ks : List (List (List ℚ))) (hf : Bell f S (some cs) P (some E))
    (hE : Quadratic E (some c0) (some c1) (some c2))
    (hK : curvatureMomentsCheck P Ks = true) (hl : cs.length = Ks.length)
    {G : Option Bool} (hG : VanishMask S cs G)
    {k g m u pi : Option ℝ} {ms : List (Option ℝ)}
    (hm : MomentTerms c1 (momentCoefs (Value.mul u (Value.inv c2)) cs Ks) Ks.flatten ms)
    (hk : Sums ms k)
    (hu : u = some (Numeric.denote (s := .real) (-1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hmn : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    partialIntegral volume f = after (scaleList S ++ presentCoefs cs ++ [c0, c1, c2])
      (Value.mask G (scaleBy S (Value.mul k (Value.mul
        (Functions.expR.apply
          (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
        (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))))) := by
  have missing : (∀ x, f x = none) → partialIntegral volume f = none := fun hn => by
    apply if_neg
    intro hdef
    obtain ⟨v, hv⟩ := hdef.1 0
    rw [hn] at hv
    cases hv
  have hfn : ∀ x, (symEval cs x = none ∨ E x = none) → f x = none := fun x hx => by
    rw [hf.equation, symPart, expPart]
    rcases hx with hx | hx <;> rw [hx] <;> rcases S with _ | _ | s <;>
      simp [scaleBy, Value.mul, Function1.apply]
  by_cases hd : none ∈ scaleList S ++ presentCoefs cs ++ [c0, c1, c2]
  · rw [after_none hd]
    apply missing
    intro x
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      mem_presentCoefs] at hd
    rcases hd with (hS | hcs) | h0 | h1 | h2
    · rcases S with _ | _ | s
      · simp [scaleList] at hS
      · rw [hf.equation]
        rfl
      · simp [scaleList] at hS
    · exact hfn x (Or.inl ((symEval_none_iff cs x).2 hcs))
    · exact hfn x (Or.inr (hE.missing (Or.inl h0.symm) x))
    · exact hfn x (Or.inr (hE.missing (Or.inr (Or.inl h1.symm)) x))
    · exact hfn x (Or.inr (hE.missing (Or.inr (Or.inr h2.symm)) x))
  rw [after_defined hd]
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    mem_presentCoefs, not_or] at hd
  obtain ⟨⟨hS, hcs⟩, h0, h1, h2⟩ := hd
  have hS' : S ≠ some none := fun h => hS (by rw [h]; simp [scaleList])
  obtain ⟨b, hGb, hb⟩ := hG.value hS' hcs
  cases b with
  | false =>
    have hne : ¬(scaleReal S ≠ 0 ∧ ∃ v : ℝ, some (some v) ∈ cs ∧ v ≠ 0) := fun h => by
      simpa using hb.2 h
    obtain ⟨a, rfl⟩ : ∃ a, c0 = some a := Option.ne_none_iff_exists'.1 (Ne.symm h0)
    obtain ⟨b1, rfl⟩ : ∃ b1, c1 = some b1 := Option.ne_none_iff_exists'.1 (Ne.symm h1)
    obtain ⟨q, rfl⟩ : ∃ q, c2 = some q := Option.ne_none_iff_exists'.1 (Ne.symm h2)
    have hzero : ∀ x, f x = some 0 := fun x => by
      have hEx : E x = some (a + (b1 * x + q * x ^ 2)) := by
        rw [hE.equation]
        rfl
      rw [hf.equation, symPart, expPart, hEx, symEval_real hcs]
      by_cases hs0 : scaleReal S = 0
      · rcases S with _ | _ | s
        · simp [scaleReal] at hs0
        · exact absurd rfl hS'
        · simp only [scaleReal] at hs0
          subst hs0
          simp [scaleBy, Value.mul, Function1.apply, Functions.expR]
      · have hall : ∀ v : ℝ, some (some v) ∈ cs → v = 0 := fun v hv =>
          by_contra fun hv0 => hne ⟨hs0, v, hv, hv0⟩
        rw [realEval_eq_zero hall]
        rcases S with _ | _ | s
        · simp [scaleBy, Value.mul, Function1.apply, Functions.expR]
        · exact absurd rfl hS'
        · simp [scaleBy, Value.mul, Function1.apply, Functions.expR]
    rw [partialIntegral_zero hzero, hGb]
    rfl
  | true =>
    obtain ⟨hs0, v, hv, hv0⟩ := hb.1 rfl
    have hSn : scaleNonvanishing S := by
      rcases S with _ | _ | s
      · trivial
      · exact absurd rfl hS'
      · intro t ht
        cases ht
        simpa [scaleReal] using hs0
    rw [gaussian_partialIntegral_curvature_moments Ks hf hE hK hl hSn
      (SomeNonvanishing.of_mem hv hv0) hm hk hu hg hmn hpi, hGb]
    rfl

end QSym.Distribution.StepSource

namespace QSym.Distribution.DensityProgram
open MeasureTheory

/-- The mass of a density that is a polynomial times the exponential of a
quadratic whose constant and linear coefficients do not mention the variable
and whose curvature is a negative rational, under an optional scale. -/
theorem presentation_mass_gaussian_symbolic (p : DensityProgram) {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ : List ℚ) (q2 γ δ : ℚ)
    (hf : StepSource.Bell p.density S none P (some E))
    (hE : StepSource.Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : StepSource.symbolicCheck P κ q2 γ δ = true) {k g d pi : Option ℝ}
    {ms : List (Option ℝ)} (hm : StepSource.RowTerms none c1 κ 0 [] ms) (hk : StepSource.Sums ms k)
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    massValue p.presentation = StepSource.scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply (Value.add c0 (Value.mul g (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi d)))) := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.gaussian_partialIntegral_symbolic κ q2 γ δ hf hE h2 h hm hk hg hd hpi

/-- The same under a polynomial whose coefficients do not mention the
variable. -/
theorem presentation_mass_gaussian_moments (p : DensityProgram) {S : Option (Option ℝ)}
    {cs : List (Option (Option ℝ))} {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ}
    (κs : List (List ℚ)) (q2 γ δ : ℚ) (hf : StepSource.Bell p.density S (some cs) P (some E))
    (hE : StepSource.Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : StepSource.momentsCheck P κs q2 γ δ = true) {k g d pi : Option ℝ}
    {ms : List (Option ℝ)} (hm : StepSource.MomentTerms c1 cs κs ms) (hk : StepSource.Sums ms k)
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    massValue p.presentation = StepSource.scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply (Value.add c0 (Value.mul g (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi d)))) := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.gaussian_partialIntegral_moments κs q2 γ δ hf hE h2 h hm hk hg hd hpi

/-- The mass of a density that is a rational polynomial times the exponential
of a quadratic whose coefficients do not mention the variable, under an
optional scale that is not zero where it is defined. It is missing where the
curvature is not negative. -/
theorem presentation_mass_gaussian_curvature (p : DensityProgram) {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (K : List (List ℚ))
    (hf : StepSource.Bell p.density S none P (some E))
    (hE : StepSource.Quadratic E (some c0) (some c1) (some c2))
    (hK : StepSource.curvatureCheck P K = true) (hS : StepSource.scaleNonvanishing S)
    {k g m u pi : Option ℝ} {ms : List (Option ℝ)}
    (hm : StepSource.MomentTerms c1
      (StepSource.curvatureCoefs (Value.mul u (Value.inv c2)) K 0) K ms)
    (hk : StepSource.Sums ms k)
    (hu : u = some (Numeric.denote (s := .real) (-1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hmn : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    massValue p.presentation = StepSource.scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply
        (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))) := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.gaussian_partialIntegral_curvature K hf hE hK hS hm hk hu hg hmn hpi

/-- The same under a polynomial whose coefficients do not mention the
variable, one of which is not zero where it is defined. -/
theorem presentation_mass_gaussian_curvature_moments (p : DensityProgram)
    {S : Option (Option ℝ)} {cs : List (Option (Option ℝ))} {P : List ℚ} {E : ℝ → Option ℝ}
    {c0 c1 c2 : Option ℝ} (Ks : List (List (List ℚ)))
    (hf : StepSource.Bell p.density S (some cs) P (some E))
    (hE : StepSource.Quadratic E (some c0) (some c1) (some c2))
    (hK : StepSource.curvatureMomentsCheck P Ks = true) (hl : cs.length = Ks.length)
    (hS : StepSource.scaleNonvanishing S) (hN : StepSource.SomeNonvanishing cs)
    {k g m u pi : Option ℝ} {ms : List (Option ℝ)}
    (hm : StepSource.MomentTerms c1
      (StepSource.momentCoefs (Value.mul u (Value.inv c2)) cs Ks) Ks.flatten ms)
    (hk : StepSource.Sums ms k)
    (hu : u = some (Numeric.denote (s := .real) (-1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hmn : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    massValue p.presentation = StepSource.scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply
        (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))) := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.gaussian_partialIntegral_curvature_moments Ks hf hE hK hl hS hN hm hk hu hg hmn
    hpi

/-- The mass of such a density under a scale that may vanish: under the mask
of the scale, after the scale and the coefficients of the exponent. -/
theorem presentation_mass_gaussian_curvature_masked (p : DensityProgram) {c : Option ℝ}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (K : List (List ℚ))
    (hf : StepSource.Bell p.density (some c) none P (some E))
    (hE : StepSource.Quadratic E (some c0) (some c1) (some c2))
    (hK : StepSource.curvatureCheck P K = true) {k g m u pi : Option ℝ} {ms : List (Option ℝ)}
    (hm : StepSource.MomentTerms c1
      (StepSource.curvatureCoefs (Value.mul u (Value.inv c2)) K 0) K ms)
    (hk : StepSource.Sums ms k)
    (hu : u = some (Numeric.denote (s := .real) (-1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hmn : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    massValue p.presentation = StepSource.after [c, c0, c1, c2] (Value.mask (Value.nonzero c)
      (Value.mul c (Value.mul k (Value.mul
        (Functions.expR.apply
          (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
        (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))))) := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.gaussian_partialIntegral_curvature_masked K hf hE hK hm hk hu hg hmn hpi

/-- The same under a polynomial whose coefficients do not mention the variable
where they may all vanish, or the scale may: under the mask of those factors. -/
theorem presentation_mass_gaussian_curvature_moments_masked (p : DensityProgram)
    {S : Option (Option ℝ)} {cs : List (Option (Option ℝ))} {P : List ℚ} {E : ℝ → Option ℝ}
    {c0 c1 c2 : Option ℝ} (Ks : List (List (List ℚ)))
    (hf : StepSource.Bell p.density S (some cs) P (some E))
    (hE : StepSource.Quadratic E (some c0) (some c1) (some c2))
    (hK : StepSource.curvatureMomentsCheck P Ks = true) (hl : cs.length = Ks.length)
    {G : Option Bool} (hG : StepSource.VanishMask S cs G)
    {k g m u pi : Option ℝ} {ms : List (Option ℝ)}
    (hm : StepSource.MomentTerms c1
      (StepSource.momentCoefs (Value.mul u (Value.inv c2)) cs Ks) Ks.flatten ms)
    (hk : StepSource.Sums ms k)
    (hu : u = some (Numeric.denote (s := .real) (-1 / 2 : ℚ)))
    (hg : g = some (Numeric.denote (s := .real) (-1 / 4 : ℚ)))
    (hmn : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (hpi : pi = some Functions.pi) :
    massValue p.presentation =
      StepSource.after (StepSource.scaleList S ++ StepSource.presentCoefs cs ++ [c0, c1, c2])
        (Value.mask G (StepSource.scaleBy S (Value.mul k (Value.mul
          (Functions.expR.apply
            (Value.add c0 (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1))))
          (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv c2)))))))) := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.gaussian_partialIntegral_curvature_moments_masked Ks hf hE hK hl hG hm hk hu hg
    hmn hpi

end QSym.Distribution.DensityProgram

namespace QSym.Limit
open QSym.Distribution.StepSource Filter Topology

/-- A polynomial times the exponential of a quadratic with negative curvature
vanishes at both ends. -/
theorem polynomial_gaussian_tendsto {l : Filter ℝ} (hl : Infinite l) (c0 c1 : ℝ) {c2 : ℝ}
    (h : c2 < 0) (P : List ℚ) :
    Tendsto (fun x : ℝ => polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) l (𝓝 0) := by
  have hpow : ∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (c0 + c1 * x + c2 * x ^ 2)) l (𝓝 0) :=
    fun n => by
      cases hl
      · exact pow_gaussian_atTop c0 c1 h n
      · exact pow_gaussian_atBot c0 c1 h n
  have hall : ∀ (P : List ℚ) (j : ℕ),
      Tendsto (fun x : ℝ => x ^ j * polyEval P x * Real.exp (c0 + c1 * x + c2 * x ^ 2)) l (𝓝 0) := by
    intro P
    induction P with
    | nil => intro j; simpa [polyEval] using tendsto_const_nhds
    | cons a P ih =>
      intro j
      have hs := ((hpow j).const_mul (a : ℝ)).add (ih (j + 1))
      rw [mul_zero, add_zero] at hs
      refine hs.congr fun x => ?_
      simp only [polyEval]
      ring
  simpa using hall P 0

/-- A coefficient that is present must be defined for the value after it. -/
def seqCoef : Option (Option ℝ) → Option ℝ → Option ℝ
  | none, v => v
  | some c, v => c.bind fun _ => v

/-- A scale times a polynomial times the exponential of a quadratic whose
curvature is a negative rational tends to zero under the scale at both ends,
whatever the other coefficients are; it is undefined with any of them. -/
theorem Exact.gaussian {l : Filter ℝ} (hl : Infinite l) {v : ℝ → Option ℝ}
    {S : Option (Option ℝ)} {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 : Option (Option ℝ)}
    {c2 : Option ℝ} (q2 : ℚ) (hv : Bell v S none P (some E)) (hE : Quadratic E c0 c1 (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2)) (hq : decide (q2 < 0) = true) {z : Option ℝ}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    Exact l v (seqCoef c0 (seqCoef c1 (scaleBy S z))) := by
  have hq' : ((q2 : ℚ) : ℝ) < 0 := by exact_mod_cast of_decide_eq_true hq
  have hz0 : z = some 0 := by rw [hz]; simp [Numeric.denote]
  have undefined : (∀ x, E x = none) → Exact l v none := fun hn =>
    Eventually.of_forall fun x => by
      rw [hv.plain, expPart, hn]
      rcases S with _ | _ | s <;> simp [scaleBy, Value.mul, Function1.apply]
  have defined : ∀ a b : ℝ, (∀ x, E x = some (a + b * x + q2 * x ^ 2)) →
      Exact l v (scaleBy S z) := fun a b he => by
    have hlim := polynomial_gaussian_tendsto hl a b hq' P
    have hvx : ∀ x, v x = scaleBy S (some (polyEval P x * Real.exp (a + b * x + q2 * x ^ 2))) :=
      fun x => by
        rw [hv.plain, expPart, he]
        simp [Value.mul, Function1.apply, Functions.expR]
    rw [hz0]
    rcases S with _ | _ | s
    · exact ⟨_, Eventually.of_forall hvx, hlim⟩
    · exact Eventually.of_forall hvx
    · refine ⟨fun x => s * (polyEval P x * Real.exp (a + b * x + q2 * x ^ 2)),
        Eventually.of_forall hvx, ?_⟩
      exact hlim.const_mul s
  rw [h2] at hE
  rcases c0 with _ | _ | a <;> rcases c1 with _ | _ | b
  · exact defined 0 0 fun x => by
      rw [hE.equation]; simp [coefValue, Value.add, Value.mul, Numeric.denote]
  · exact undefined fun x => by rw [hE.equation]; simp [coefValue, Value.add, Value.mul]
  · exact defined 0 b fun x => by
      rw [hE.equation]; simp [coefValue, Value.add, Value.mul, Numeric.denote]
  · exact undefined fun x => by rw [hE.equation]; simp [coefValue, Value.add]
  · exact undefined fun x => by rw [hE.equation]; simp [coefValue, Value.add]
  · exact undefined fun x => by rw [hE.equation]; simp [coefValue, Value.add]
  · exact defined a 0 fun x => by
      rw [hE.equation]; simp [coefValue, Value.add, Value.mul, Numeric.denote]
  · exact undefined fun x => by rw [hE.equation]; simp [coefValue, Value.add, Value.mul]
  · exact defined a b fun x => by
      rw [hE.equation]; simp [coefValue, Value.add, Value.mul, Numeric.denote]
      ring

/-- The same along a filter. -/
theorem EventualScaled.exp_offset (l : Filter ℝ) {E : ℝ → Option ℝ} {c0 c1 : Option ℝ} (r : ℚ)
    (hE : Quadratic E (some c0) (some c1) none)
    (h1 : c1 = some (Numeric.denote (s := .real) r)) :
    EventualScaled l (fun x => Functions.expR.apply (E x)) (Functions.expR.apply c0) [1] [0, r] :=
  Filter.Eventually.of_forall fun x => by
    show Functions.expR.apply (E x) = _
    have h := (scaled_exp_offset r hE h1).equation x
    rw [show Functions.expR.apply (E x) = _ from h]
    simp [polyEval, mul_comm]

/-- The same up to degree two: with rational coefficients above the constant
the exponential of that constant is a scale. A coefficient that is absent is
a zero. -/
theorem EventualScaled.exp_curve (l : Filter ℝ) {E : ℝ → Option ℝ} {c0 : Option ℝ}
    {c1 c2 : Option (Option ℝ)} (r1 r2 : ℚ) (hE : Quadratic E (some c0) c1 c2)
    (h1 : coefValue c1 = some (Numeric.denote (s := .real) r1))
    (h2 : coefValue c2 = some (Numeric.denote (s := .real) r2)) :
    EventualScaled l (fun x => Functions.expR.apply (E x)) (Functions.expR.apply c0) [1]
      [0, r1, r2] :=
  Filter.Eventually.of_forall fun x => by
    show Functions.expR.apply (E x) = _
    rw [hE.equation, h1, h2]
    cases c0 <;>
      simp [coefValue, Value.add, Value.mul, Function1.apply, Functions.expR, polyEval,
        Numeric.denote, ← Real.exp_add]
    ring

end QSym.Limit
