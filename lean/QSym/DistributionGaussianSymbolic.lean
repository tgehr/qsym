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

/-- A partial value that is not zero where it is defined. -/
def Nonvanishing (c : Option ℝ) : Prop := ∀ s, c = some s → s ≠ 0

theorem Nonvanishing.inv (c : Option ℝ) : Nonvanishing (Value.inv c) := by
  intro s hs
  rcases c with _ | v
  · cases hs
  · by_cases hv : v = 0
    · simp [Value.inv, hv] at hs
    · have he : (some v⁻¹ : Option ℝ) = some s := by simpa [Value.inv, hv] using hs
      rw [← Option.some.inj he]
      exact inv_ne_zero hv

theorem Nonvanishing.literal {c : Option ℝ} (q : ℚ)
    (h : c = some (Numeric.denote (s := .real) q)) (hq : decide (q ≠ 0) = true) :
    Nonvanishing c := by
  intro s hs
  rw [h] at hs
  rw [← Option.some.inj hs]
  have hr : (q : ℝ) ≠ 0 := by exact_mod_cast of_decide_eq_true hq
  simpa [Numeric.denote] using hr

theorem Nonvanishing.pi {c : Option ℝ} (h : c = some Functions.pi) : Nonvanishing c := by
  intro s hs
  rw [h] at hs
  rw [← Option.some.inj hs]
  exact Real.pi_pos.ne'

theorem Nonvanishing.mul {a b : Option ℝ} (ha : Nonvanishing a) (hb : Nonvanishing b) :
    Nonvanishing (Value.mul a b) := by
  intro s hs
  rcases a with _ | x
  · cases hs
  · rcases b with _ | y
    · cases hs
    · rw [← Option.some.inj hs]
      exact mul_ne_zero (ha x rfl) (hb y rfl)

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
private theorem eval_eventually_away {q : Polynomial ℝ} (hq : q ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in atTop, δ ≤ |q.eval x| := by
  by_cases hd : 0 < q.degree
  · exact ⟨1, one_pos, (q.abs_tendsto_atTop hd).eventually_ge_atTop 1⟩
  · have hc := Polynomial.eq_C_of_degree_le_zero (not_lt.1 hd)
    have hne : q.coeff 0 ≠ 0 := fun h => hq (by rw [hc, h, Polynomial.C_0])
    refine ⟨|q.coeff 0|, abs_pos.2 hne, Filter.Eventually.of_forall fun x => ?_⟩
    rw [hc, Polynomial.eval_C, Polynomial.coeff_C_zero]

/-- A polynomial that is not zero times the exponential of a quadratic is not
integrable over the line unless the curvature is negative. -/
theorem polynomial_exp_quadratic_not_integrable {P : List ℚ} (hP : polyZero P = false)
    (a b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ¬ Integrable (fun x : ℝ => polyEval P x * Real.exp (a + b * x + c * x ^ 2)) volume := by
  intro hi
  have hq := QSym.Limit.toPoly_ne_zero hP
  have above : ∀ (δ x : ℝ), 0 ≤ δ → δ ≤ |polyEval P x| → 0 ≤ b * x →
      ‖δ * Real.exp a‖ ≤ ‖polyEval P x * Real.exp (a + b * x + c * x ^ 2)‖ := fun δ x h0 hx hbx => by
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
      have h1 := hM x (le_trans (le_max_left _ _) hx')
      rw [QSym.Limit.eval_toPoly] at h1
      exact above δ x hδ.le h1 (mul_nonneg hb (le_trans (le_max_right _ _) hx'))
    rw [integrableOn_const] at hs
    rcases hs with h0 | hfin
    · exact (mul_pos hδ (Real.exp_pos a)).ne' h0
    · rw [Real.volume_Ici] at hfin
      exact lt_irrefl _ hfin
  · have hq' : (QSym.Limit.toPoly P).comp (-Polynomial.X) ≠ 0 := fun h0 => hq (by
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
      rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, neg_neg,
        QSym.Limit.eval_toPoly] at h1
      exact above δ x hδ.le h1
        (mul_nonneg_of_nonpos_of_nonpos (not_le.1 hb).le (le_trans hx' (min_le_right _ _)))
    rw [integrableOn_const] at hs
    rcases hs with h0 | hfin
    · exact (mul_pos hδ (Real.exp_pos a)).ne' h0
    · rw [Real.volume_Iic] at hfin
      exact lt_irrefl _ hfin

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

private theorem curvaturePower_some (h : ℝ) (l : ℕ) : curvaturePower (some h) l = some (h ^ l) := by
  rcases l with _ | _ | l <;> simp [curvaturePower]

private theorem curvatureCoefs_defined (h : ℝ) (K : List (List ℚ)) (l : ℕ) :
    some none ∉ curvatureCoefs (some h) K l := by
  induction K generalizing l with
  | nil => simp [curvatureCoefs]
  | cons κ K ih =>
    simp only [curvatureCoefs, List.mem_cons, not_or]
    refine ⟨?_, ih (l + 1)⟩
    split_ifs <;> simp [curvaturePower_some]

private theorem momentValue_curvature (b h : ℝ) (K : List (List ℚ)) (l : ℕ) :
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
  have hnone : scaleBy S none = none := by
    rcases S with _ | _ | s <;> simp [scaleBy, Value.mul]
  have undefined : (∀ x, E x = none) → partialIntegral volume f = none := fun hn => by
    apply if_neg
    intro hdef
    obtain ⟨r, hr⟩ := hdef.1 0
    rw [hfx, hn] at hr
    have : Value.mul (some (polyEval P 0)) (Functions.expR.apply (none : Option ℝ)) = none := by
      simp [Function1.apply, Value.mul]
    rw [this, hnone] at hr
    cases hr
  have right : ∀ X : Option ℝ, Value.mul k (Value.mul X none) = none := fun X => by
    cases k <;> cases X <;> rfl
  have left : ∀ X : Option ℝ, Value.mul k (Value.mul (Functions.expR.apply none) X) = none :=
    fun X => by cases k <;> simp [Value.mul, Function1.apply]
  rcases c0 with _ | a
  · rw [undefined fun x => by rw [hE.equation]; simp [coefValue, Value.add]]
    have : Value.add (none : Option ℝ)
        (Value.mul (Value.mul g (Value.inv c2)) (Value.mul c1 c1)) = none := rfl
    rw [this, left, hnone]
  rcases c1 with _ | b
  · rw [undefined fun x => by rw [hE.equation]; simp [coefValue, Value.add, Value.mul]]
    have : Value.add (some a)
        (Value.mul (Value.mul g (Value.inv c2)) (Value.mul (none : Option ℝ) none)) = none := by
      cases Value.mul g (Value.inv c2) <;> rfl
    rw [this, left, hnone]
  rcases c2 with _ | c
  · rw [undefined fun x => by rw [hE.equation]; simp [coefValue, Value.add, Value.mul]]
    have : Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv (none : Option ℝ)))) =
        none := by
      cases pi <;> cases m <;> simp [Value.mul, Value.inv, Function1.apply]
    rw [this, right, hnone]
  have hE' : ∀ x, E x = some (a + b * x + c * x ^ 2) := fun x => by
    rw [hE.equation]
    show some (a + (b * x + c * x ^ 2)) = some (a + b * x + c * x ^ 2)
    congr 1
    ring
  -- The result under a factor that is not zero.
  have key : ∀ s : ℝ, s ≠ 0 →
      (∀ x, f x = some (s * (polyEval P x * Real.exp (a + b * x + c * x ^ 2)))) →
      partialIntegral volume f = Value.mul (some s) (Value.mul k (Value.mul
        (Functions.expR.apply (Value.add (some a)
          (Value.mul (Value.mul g (Value.inv (some c))) (Value.mul (some b) (some b)))))
        (Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv (some c))))))) := by
    intro s hs hfs
    have he : (fun x => (f x).getD 0) =
        fun x => s * (polyEval P x * Real.exp (a + b * x + c * x ^ 2)) := by
      funext x
      rw [hfs]
      rfl
    by_cases hc : c < 0
    · obtain ⟨hi0, hv⟩ := gaussian_moments2 a b hc P
      have hi := hi0.const_mul s
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
      rw [partialIntegral_valid volume f (fun x => ⟨_, hfs x⟩) (by rw [he]; exact hi), he,
        integral_const_mul, hv, hK', hkv, hg, hmn, hpi]
      have hinv : 0 < -c⁻¹ := by
        have := inv_lt_zero.2 hc
        linarith
      have hpos : Real.pi * c⁻¹ ≤ 0 := by nlinarith [Real.pi_pos]
      have h1 : a - b ^ 2 / (4 * c) = a + -1 / 4 * c⁻¹ * (b * b) := by
        field_simp
        ring
      have h2 : Real.pi / -c = Real.pi * (-1 * c⁻¹) := by
        rw [div_eq_mul_inv, inv_neg]
        ring
      rw [h1, h2]
      simp [Value.mul, Value.add, Value.inv, hne, Function1.apply, Functions.expR,
        Functions.sqrtR, Functions.pi, Numeric.denote, hpos]
    · have hc' : 0 ≤ c := not_lt.1 hc
      have hn : partialIntegral volume f = none := by
        apply if_neg
        rintro ⟨_, hi⟩
        rw [he] at hi
        have hi' := hi.const_mul s⁻¹
        have he2 : (fun x => s⁻¹ * (s * (polyEval P x * Real.exp (a + b * x + c * x ^ 2)))) =
            fun x => polyEval P x * Real.exp (a + b * x + c * x ^ 2) := by
          funext x
          rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
        rw [he2] at hi'
        exact polynomial_exp_quadratic_not_integrable hP a b hc' hi'
      have hroot : Functions.sqrtR.apply (Value.mul pi (Value.mul m (Value.inv (some c)))) =
          none := by
        rw [hmn, hpi]
        rcases hc'.eq_or_lt with h0 | hpos
        · subst h0
          simp [Value.inv, Value.mul, Function1.apply]
        · have hneg : ¬ Real.pi * c⁻¹ ≤ 0 := not_le.2 (mul_pos Real.pi_pos (inv_pos.2 hpos))
          simp [Value.inv, hpos.ne', Value.mul, Function1.apply, Functions.sqrtR, Functions.pi,
            Numeric.denote, hneg]
      rw [hn, hroot, right]
      rfl
  rcases S with _ | _ | s
  · have h := key 1 one_ne_zero fun x => by
      rw [hfx, hE']
      simp [scaleBy, Value.mul, Function1.apply, Functions.expR]
    rw [h]
    exact Value.mul_one_left _
  · apply if_neg
    intro hdef
    obtain ⟨r, hr⟩ := hdef.1 0
    rw [hfx] at hr
    simp [scaleBy, Value.mul] at hr
  · exact key s (hS s rfl) fun x => by
      rw [hfx, hE']
      simp [scaleBy, Value.mul, Function1.apply, Functions.expR]

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
