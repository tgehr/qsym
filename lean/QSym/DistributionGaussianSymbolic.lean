import QSym.DistributionGaussian

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
    have hrec := pow_gaussian_recurrence c0 c1 hc j
    have hnext : (∫ x : ℝ, x ^ (j + 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
        polyEval (polyScale h (polyAdd (polyMul [0, 1] μ) (polyScale j μ'))) c1 * G := by
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
    have hprev : ((j + 1 : ℕ) : ℝ) *
        (∫ x : ℝ, x ^ (j + 1 - 1) * Real.exp (c0 + c1 * x + c2 * x ^ 2)) =
          ((j + 1 : ℕ) : ℝ) * (polyEval μ c1 * G) := by
      rw [Nat.add_sub_cancel, h1]
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

/-- A factor of a density: a scale, a polynomial with rational coefficients
and an exponential, each of which may be absent. -/
structure Bell (v : ℝ → Option ℝ) (S : Option (Option ℝ)) (p : List ℚ)
    (E : Option (ℝ → Option ℝ)) : Prop where
  equation : ∀ x, v x = scaleBy S (Value.mul (some (polyEval p x)) (expPart E x))

theorem bell_polynomial {v : ℝ → Option ℝ} {p : List ℚ}
    (h : PolynomialOn (fun _ => True) v p) : Bell v none p none :=
  ⟨fun x => by rw [h.equation x trivial]; simp [scaleBy, expPart, Value.mul]⟩

theorem bell_exp (g : ℝ → Option ℝ) : Bell (fun x => Functions.expR.apply (g x)) none [1] (some g) :=
  ⟨fun x => by
    show Functions.expR.apply (g x) = _
    cases hg : g x <;> simp [scaleBy, expPart, Value.mul, polyEval, Function1.apply, Functions.expR, hg]⟩

theorem bell_constant (c : Option ℝ) : Bell (fun _ => c) (some c) [1] none :=
  ⟨fun x => by cases c <;> simp [scaleBy, expPart, Value.mul, polyEval]⟩

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

/-- Factors multiply part by part. -/
theorem bell_mul {v w : ℝ → Option ℝ} {S S' : Option (Option ℝ)} {p p' : List ℚ}
    {E E' : Option (ℝ → Option ℝ)} (hv : Bell v S p E) (hw : Bell w S' p' E') :
    Bell (fun x => Value.mul (v x) (w x)) (joinScale S S') (polyMul p p') (joinExp E E') :=
  ⟨fun x => by
    show Value.mul (v x) (w x) = _
    rw [hv.equation, hw.equation, ← scaleBy_join, expPart_join, polyEval_mul]
    congr 1
    cases expPart E x <;> cases expPart E' x <;> simp [Value.mul]
    ring⟩


/-- A coefficient of a polynomial in the variable is a partial value that
does not mention it, or is absent; then it counts as zero. -/
def coefValue : Option (Option ℝ) → Option ℝ
  | none => some 0
  | some c => c

/-- Sums and products of coefficients; an absent one is skipped in a sum and
absorbs a product. -/
def coefAdd : Option (Option ℝ) → Option (Option ℝ) → Option (Option ℝ)
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Value.add a b)

def coefMul : Option (Option ℝ) → Option (Option ℝ) → Option (Option ℝ)
  | some a, some b => some (Value.mul a b)
  | _, _ => none

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

private theorem coefValue_add (a b : Option (Option ℝ)) :
    coefValue (coefAdd a b) = Value.add (coefValue a) (coefValue b) := by
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp [coefValue, coefAdd, Value.add]

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

/-- A polynomial with rational coefficients at a partial value, by Horner's
rule; its last coefficient stands alone. -/
inductive Horner : Option ℝ → List ℚ → Option ℝ → Prop
  | last {z c : Option ℝ} (q : ℚ) (hz : z = some (Numeric.denote (s := .real) q)) :
      Horner z [q] c
  | step {z k c : Option ℝ} {qs : List ℚ} (q : ℚ)
      (hz : z = some (Numeric.denote (s := .real) q)) (h : Horner k qs c) :
      Horner (Value.add z (Value.mul c k)) (q :: qs) c

theorem Horner.value {k c : Option ℝ} {κ : List ℚ} (h : Horner k κ c) (v : ℝ)
    (hc : c = some v) : k = some (polyEval κ v) := by
  induction h with
  | last q hz => rw [hz]; simp [polyEval, Numeric.denote]
  | step q hz _ ih => rw [hz, ih hc, hc]; simp [polyEval, Value.add, Value.mul, Numeric.denote]

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
    (hf : Bell f S P (some E)) (hE : Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : symbolicCheck P κ q2 γ δ = true) {k g d pi : Option ℝ} (hk : Horner k κ c1)
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
    rw [hf.equation, expPart, hn] at hr
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
      rw [hf.equation, expPart, hE']
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
  rw [hκ', hγ', hδ', hk.value b rfl, hg, hd, hpi]
  simp [Value.mul, Value.add, Function1.apply, Functions.expR, Functions.sqrtR, Functions.pi,
    Numeric.denote, hpos]

end QSym.Distribution.StepSource

namespace QSym.Distribution.DensityProgram
open MeasureTheory

/-- The mass of a density that is a polynomial times the exponential of a
quadratic whose constant and linear coefficients do not mention the variable
and whose curvature is a negative rational, under an optional scale. -/
theorem presentation_mass_gaussian_symbolic (p : DensityProgram) {S : Option (Option ℝ)}
    {P : List ℚ} {E : ℝ → Option ℝ} {c0 c1 c2 : Option ℝ} (κ : List ℚ) (q2 γ δ : ℚ)
    (hf : StepSource.Bell p.density S P (some E))
    (hE : StepSource.Quadratic E (some c0) (some c1) (some c2))
    (h2 : c2 = some (Numeric.denote (s := .real) q2))
    (h : StepSource.symbolicCheck P κ q2 γ δ = true) {k g d pi : Option ℝ}
    (hk : StepSource.Horner k κ c1)
    (hg : g = some (Numeric.denote (s := .real) γ)) (hd : d = some (Numeric.denote (s := .real) δ))
    (hpi : pi = some Functions.pi) :
    massValue p.presentation = StepSource.scaleBy S (Value.mul k (Value.mul
      (Functions.expR.apply (Value.add c0 (Value.mul g (Value.mul c1 c1))))
      (Functions.sqrtR.apply (Value.mul pi d)))) := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.gaussian_partialIntegral_symbolic κ q2 γ δ hf hE h2 h hk hg hd hpi

end QSym.Distribution.DensityProgram

namespace QSym.Limit
open QSym.Distribution.StepSource

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

end QSym.Limit
