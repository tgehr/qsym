import QSym.DistributionRatio
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
A polynomial times the logarithm of the axis, plus a polynomial, between two
bounds. The logarithm is defined on the positive axis only, so the value is
observed exactly where the guard of the bounds is on the positive axis: the
lower bound is positive, or it is zero and strict. Next to zero the value is
integrable, and its antiderivative `x·P₁(x)·log x + x·S₁(x)` continues there
with zero. The same around another point of the axis, for the logarithm of
the axis minus that point.
-/

namespace QSym.Distribution.StepSource
open MeasureTheory Set Filter Topology

/-- A polynomial times the logarithm of the axis plus a polynomial, on the
positive axis; undefined elsewhere. -/
structure LogOn (v : ℝ → Option ℝ) (p q : List ℚ) : Prop where
  equation : ∀ x : ℝ, 0 < x → v x = some (polyEval p x * Real.log x + polyEval q x)
  undefined : ∀ x : ℝ, x ≤ 0 → v x = none

theorem log_axis : LogOn (fun x => Functions.logR.apply (some x)) [1] [] :=
  ⟨fun x hx => by simp [Function1.apply, Functions.logR, hx, polyEval],
    fun x hx => by simp [Function1.apply, Functions.logR, not_lt.2 hx]⟩

theorem log_mul_left {f g : ℝ → Option ℝ} {r p q : List ℚ}
    (hf : PolynomialOn (fun _ => True) f r) (hg : LogOn g p q) :
    LogOn (fun x => Value.mul (f x) (g x)) (polyMul r p) (polyMul r q) :=
  ⟨fun x hx => by
    show Value.mul (f x) (g x) = _
    rw [hf.equation x trivial, hg.equation x hx, polyEval_mul, polyEval_mul]
    simp only [Value.mul, Option.some.injEq]
    ring, fun x hx => by
    show Value.mul (f x) (g x) = none
    rw [hf.equation x trivial, hg.undefined x hx]
    rfl⟩

theorem log_mul_right {f g : ℝ → Option ℝ} {r p q : List ℚ}
    (hg : LogOn g p q) (hf : PolynomialOn (fun _ => True) f r) :
    LogOn (fun x => Value.mul (g x) (f x)) (polyMul p r) (polyMul q r) :=
  ⟨fun x hx => by
    show Value.mul (g x) (f x) = _
    rw [hf.equation x trivial, hg.equation x hx, polyEval_mul, polyEval_mul]
    simp only [Value.mul, Option.some.injEq]
    ring, fun x hx => by
    show Value.mul (g x) (f x) = none
    rw [hg.undefined x hx]
    rfl⟩

theorem log_add_left {f g : ℝ → Option ℝ} {r p q : List ℚ}
    (hf : PolynomialOn (fun _ => True) f r) (hg : LogOn g p q) :
    LogOn (fun x => Value.add (f x) (g x)) p (polyAdd r q) :=
  ⟨fun x hx => by
    show Value.add (f x) (g x) = _
    rw [hf.equation x trivial, hg.equation x hx, polyEval_add]
    simp only [Value.add, Option.some.injEq]
    ring, fun x hx => by
    show Value.add (f x) (g x) = none
    rw [hf.equation x trivial, hg.undefined x hx]
    rfl⟩

theorem log_add_right {f g : ℝ → Option ℝ} {r p q : List ℚ}
    (hg : LogOn g p q) (hf : PolynomialOn (fun _ => True) f r) :
    LogOn (fun x => Value.add (g x) (f x)) p (polyAdd q r) :=
  ⟨fun x hx => by
    show Value.add (g x) (f x) = _
    rw [hf.equation x trivial, hg.equation x hx, polyEval_add]
    simp only [Value.add, Option.some.injEq]
    ring, fun x hx => by
    show Value.add (g x) (f x) = none
    rw [hg.undefined x hx]
    rfl⟩

theorem log_add {f g : ℝ → Option ℝ} {p q p' q' : List ℚ}
    (hf : LogOn f p q) (hg : LogOn g p' q') :
    LogOn (fun x => Value.add (f x) (g x)) (polyAdd p p') (polyAdd q q') :=
  ⟨fun x hx => by
    show Value.add (f x) (g x) = _
    rw [hf.equation x hx, hg.equation x hx, polyEval_add, polyEval_add]
    simp only [Value.add, Option.some.injEq]
    ring, fun x hx => by
    show Value.add (f x) (g x) = none
    rw [hf.undefined x hx]
    rfl⟩

/-- The logarithm of the axis minus a point, moved to zero. -/
theorem log_axis_shifted (s : ℚ) {c : Option ℝ}
    (hc : c = some (Numeric.denote (s := .real) (-s))) :
    LogOn (fun y => Functions.logR.apply (Value.add (some (y + s)) c)) [1] [] := by
  have hd : Numeric.denote (s := .real) (-s) = -(s : ℝ) := by simp [Numeric.denote]
  rw [hc, hd]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · simp [Function1.apply, Functions.logR, Value.add, hy, polyEval]
  · simp [Function1.apply, Functions.logR, Value.add, not_lt.2 hy]

theorem log_axis_shifted' (s : ℚ) {c : Option ℝ}
    (hc : c = some (Numeric.denote (s := .real) (-s))) :
    LogOn (fun y => Functions.logR.apply (Value.add c (some (y + s)))) [1] [] := by
  have hd : Numeric.denote (s := .real) (-s) = -(s : ℝ) := by simp [Numeric.denote]
  rw [hc, hd]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · simp [Function1.apply, Functions.logR, Value.add, hy, polyEval]
  · simp [Function1.apply, Functions.logR, Value.add, not_lt.2 hy]

/-- Under the guard of its domain the value is the same: the guard holds on
the positive axis, and elsewhere the value is undefined anyway. -/
theorem log_guard {v : ℝ → Option ℝ} {p q : List ℚ} {g : ℝ → Option Bool} (hv : LogOn v p q)
    (hg : ∀ x : ℝ, 0 < x → g x = some true) :
    LogOn (fun x => Binding.guardValue (g x) (v x)) p q :=
  ⟨fun x hx => by
    show Binding.guardValue (g x) (v x) = _
    rw [hg x hx, hv.equation x hx]
    rfl, fun x hx => by
    show Binding.guardValue (g x) (v x) = none
    rw [hv.undefined x hx]
    simp [Binding.guardValue]⟩

/-- The domain of the logarithm of the axis, and of the axis minus a point
moved to zero. -/
theorem axis_positive {c : Option ℝ} (hc : c = some (Numeric.denote (s := .real) (0 : ℚ)))
    (x : ℝ) (hx : 0 < x) : Value.lt c (some x) = some true := by
  rw [hc]
  simp [Value.lt, Numeric.denote, hx]

theorem shifted_positive (s : ℚ) {c : Option ℝ} (hc : c = some (Numeric.denote (s := .real) s))
    (y : ℝ) (hy : 0 < y) : Value.lt c (some (y + s)) = some true := by
  rw [hc]
  simp [Value.lt, Numeric.denote, hy]

/-- `x·P₁(x)·log x + x·S₁(x)` is an antiderivative of `p·log x + q`:
`(x·P₁)' = p` and `(x·S₁)' = q - P₁`. -/
def logCheck (p q P₁ S₁ : List ℚ) : Bool :=
  polyZero (polyAdd (polyDerivative (0 :: P₁)) (polyScale (-1) p)) &&
    polyZero (polyAdd (polyAdd (polyDerivative (0 :: S₁)) P₁) (polyScale (-1) q))

theorem log_hasDerivAt {p q P₁ S₁ : List ℚ} (h : logCheck p q P₁ S₁ = true) {x : ℝ}
    (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => t * polyEval P₁ t * Real.log t + t * polyEval S₁ t)
      (polyEval p x * Real.log x + polyEval q x) x := by
  simp only [logCheck, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := polyEval_zero h1 x
  have e2 := polyEval_zero h2 x
  simp only [polyEval_add, polyEval_scale] at e1 e2
  push_cast at e1 e2
  have hP := polyEval_hasDerivAt (0 :: P₁) x
  have hS := polyEval_hasDerivAt (0 :: S₁) x
  have hF := (hP.mul (Real.hasDerivAt_log hx)).add hS
  have he : (fun t : ℝ => t * polyEval P₁ t * Real.log t + t * polyEval S₁ t) =
      fun t => polyEval (0 :: P₁) t * Real.log t + polyEval (0 :: S₁) t := by
    funext t
    simp [polyEval]
  rw [he]
  refine hF.congr_deriv ?_
  have hx1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  have hP0 : polyEval (0 :: P₁) x = x * polyEval P₁ x := by simp [polyEval]
  rw [hP0]
  linear_combination (Real.log x) * e1 + e2 + (polyEval P₁ x) * hx1

theorem log_primitive_continuous (P₁ S₁ : List ℚ) :
    Continuous fun t : ℝ => t * polyEval P₁ t * Real.log t + t * polyEval S₁ t := by
  have h1 : Continuous fun t : ℝ => polyEval P₁ t * (t * Real.log t) :=
    (polyEval_continuous P₁).mul Real.continuous_mul_log
  have h2 : Continuous fun t : ℝ => t * polyEval S₁ t :=
    continuous_id.mul (polyEval_continuous S₁)
  have he : (fun t : ℝ => t * polyEval P₁ t * Real.log t + t * polyEval S₁ t) =
      fun t => polyEval P₁ t * (t * Real.log t) + t * polyEval S₁ t := by
    funext t
    ring
  rw [he]
  exact h1.add h2

theorem log_intervalIntegrable (p q : List ℚ) (l u : ℝ) :
    IntervalIntegrable (fun x : ℝ => polyEval p x * Real.log x + polyEval q x) volume l u :=
  (intervalIntegral.intervalIntegrable_log'.continuousOn_mul
    (polyEval_continuous p).continuousOn).add ((polyEval_continuous q).intervalIntegrable l u)

theorem log_integral {p q P₁ S₁ : List ℚ} (h : logCheck p q P₁ S₁ = true) {l u : ℝ}
    (hl : 0 ≤ l) (hlu : l ≤ u) :
    ∫ x in l..u, (polyEval p x * Real.log x + polyEval q x) =
      (u * polyEval P₁ u * Real.log u + u * polyEval S₁ u) -
        (l * polyEval P₁ l * Real.log l + l * polyEval S₁ l) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlu
    (log_primitive_continuous P₁ S₁).continuousOn
    (fun _ hx => log_hasDerivAt h (lt_of_le_of_lt hl hx.1).ne')
    (log_intervalIntegrable p q l u)

/-- The antiderivative at a bound: `o·P₁(o)·log(o) + o·S₁(o)`. At a lower
bound that is strict the first part is under the mask that the bound is not
zero: there the logarithm is undefined, and the antiderivative continues
with zero. -/
noncomputable def logPrimitive (masked : Bool) (p1 s1 o : Option ℝ) : Option ℝ :=
  match masked with
  | false => Value.add (Value.mul (Value.mul o p1) (Functions.logR.apply o)) (Value.mul o s1)
  | true => Value.add (Value.mask (Value.nonzero o)
      (Value.mul (Value.mul o p1) (Functions.logR.apply o))) (Value.mul o s1)

private theorem log_row {c p : Option ℝ} {Q : List ℚ} {qs : List (Option ℝ)}
    (hq : RowTerms none c Q 0 [] qs) (hp : Sums qs p) (t : ℝ) (hc : c = some t) :
    p = some (polyEval Q t) := by
  rw [hp.value, hq.value t hc (by simp)]
  simp [factorReal, listSum, Value.add]

private theorem logPrimitive_positive {P₁ S₁ : List ℚ} {p1 s1 o : Option ℝ}
    {msp mss : List (Option ℝ)} (hp : RowTerms none o P₁ 0 [] msp) (hsp : Sums msp p1)
    (hs : RowTerms none o S₁ 0 [] mss) (hss : Sums mss s1) (masked : Bool) {t : ℝ}
    (ho : o = some t) (ht : 0 < t) :
    logPrimitive masked p1 s1 o =
      some (t * polyEval P₁ t * Real.log t + t * polyEval S₁ t) := by
  subst ho
  rw [log_row hp hsp t rfl, log_row hs hss t rfl]
  cases masked <;>
    simp [logPrimitive, Value.add, Value.mul, Value.mask, Value.nonzero, Function1.apply,
      Functions.logR, ht, ht.ne']

private theorem logPrimitive_zero {P₁ S₁ : List ℚ} {p1 s1 o : Option ℝ}
    {msp mss : List (Option ℝ)} (hp : RowTerms none o P₁ 0 [] msp) (hsp : Sums msp p1)
    (hs : RowTerms none o S₁ 0 [] mss) (hss : Sums mss s1) (ho : o = some (0 : ℝ)) :
    logPrimitive true p1 s1 o = some (0 : ℝ) := by
  subst ho
  rw [log_row hp hsp 0 rfl, log_row hs hss 0 rfl]
  simp [logPrimitive, Value.add, Value.mul, Value.mask, Value.nonzero]

private theorem compare_real (s : Bool) (l u : ℝ) :
    compare s (some l) (some u) = some (decide (if s = true then l < u else l ≤ u)) := by
  cases s <;> simp [compare, Value.lt, Value.le]

/-- Between two bounds: under the mask of their comparison, the difference
of the antiderivative under the guard that the lower bound is positive, or
zero where it is strict. Otherwise a point of the guard is not positive, and
there the logarithm is undefined. -/
theorem log_between (swap sl su : Bool) {a b : Option ℝ} {v : ℝ → Option ℝ} {p q : List ℚ}
    (P₁ S₁ : List ℚ) (hv : LogOn v p q) (hc : logCheck p q P₁ S₁ = true)
    {z m p1b p1a s1b s1a : Option ℝ} {mspb mspa mssb mssa : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hpb : RowTerms none b P₁ 0 [] mspb) (hspb : Sums mspb p1b)
    (hsb : RowTerms none b S₁ 0 [] mssb) (hssb : Sums mssb s1b)
    (hpa : RowTerms none a P₁ 0 [] mspa) (hspa : Sums mspa p1a)
    (hsa : RowTerms none a S₁ 0 [] mssa) (hssa : Sums mssa s1a) :
    partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x) (v x)) =
      Value.mask (compare (sl || su) a b) (Binding.guardValue (compare (!sl) z a)
        (Value.add (logPrimitive false p1b s1b b) (Value.mul m (logPrimitive sl p1a s1a a)))) := by
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hMinus : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  subst hZ hMinus
  have missing : ∀ (f : ℝ → Option ℝ) (y : ℝ), f y = none → partialIntegral volume f = none := by
    intro f y hy
    apply if_neg
    intro hd
    obtain ⟨r, hr⟩ := hd.1 y
    rw [hy] at hr
    cases hr
  cases a with
  | none =>
    have hn : compare (sl || su) none b = none := by cases sl <;> cases su <;> rfl
    rw [hn]
    cases b with
    | none => exact missing _ 0 (by cases swap <;> cases sl <;> cases su <;> rfl)
    | some u =>
      refine missing _ (u - 1) ?_
      cases swap <;> cases sl <;> cases su <;>
        simp [intervalGuard, compare, Value.and, Value.lt, Value.le, Value.mask]
  | some l =>
    cases b with
    | none =>
      have hn : compare (sl || su) (some l) none = none := by cases sl <;> cases su <;> rfl
      rw [hn]
      refine missing _ (l + 1) ?_
      cases swap <;> cases sl <;> cases su <;>
        simp [intervalGuard, compare, Value.and, Value.lt, Value.le, Value.mask]
    | some u =>
      have hf : Masked (fun x => Value.mask (intervalGuard swap sl su (some l) (some u) x) (v x))
          (intervalGuard swap sl su (some l) (some u)) v := ⟨fun _ => rfl⟩
      rw [compare_real, compare_real]
      by_cases hT : (if (sl || su) = true then l < u else l ≤ u)
      · have hlu : l ≤ u := by
          split_ifs at hT
          · exact hT.le
          · exact hT
        rw [decide_eq_true hT]
        show _ = Binding.guardValue _ _
        by_cases hG : (if (!sl) = true then (0 : ℝ) < l else 0 ≤ l)
        · -- The guard is on the positive axis.
          have hl0 : 0 ≤ l := by
            split_ifs at hG
            · exact hG.le
            · exact hG
          have hpos : ∀ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
              (if su = true then x < u else x ≤ u)) → 0 < x := fun x hx => by
            obtain ⟨h1, _⟩ := hx
            cases sl
            · have h1' : l ≤ x := h1
              have hG' : 0 < l := hG
              linarith
            · have h1' : l < x := h1
              linarith
          have hu0 : 0 < u := by
            cases sl
            · have hG' : 0 < l := hG
              linarith
            · have hT' : l < u := hT
              linarith
          have hg : ∀ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
              (if su = true then x < u else x ≤ u)) →
              v x = some (polyEval p x * Real.log x + polyEval q x) := fun x hx =>
            hv.equation x (hpos x hx)
          have hint : IntegrableOn (fun x : ℝ => polyEval p x * Real.log x + polyEval q x)
              (Ioo l u) volume :=
            (intervalIntegrable_iff_integrableOn_Ioo_of_le hlu).1 (log_intervalIntegrable p q l u)
          rw [(interval_observation_value swap sl su l u hf hg).1 hint,
            ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlu,
            log_integral hc hl0 hlu, decide_eq_true hG,
            logPrimitive_positive hpb hspb hsb hssb false rfl hu0]
          rcases lt_or_eq_of_le hl0 with hlpos | hlzero
          · rw [logPrimitive_positive hpa hspa hsa hssa sl rfl hlpos]
            simp only [Binding.guardValue, Value.add, Value.mul]
            simp
            ring
          · subst hlzero
            have hsl : sl = true := by
              cases sl
              · exact absurd hG (lt_irrefl _)
              · rfl
            subst hsl
            rw [logPrimitive_zero hpa hspa hsa hssa rfl]
            simp only [Binding.guardValue, Value.add, Value.mul]
            simp
        · -- A point of the guard is not positive.
          rw [decide_eq_false hG]
          show _ = none
          have hl0 : l ≤ 0 := by
            cases sl
            · exact not_lt.1 hG
            · exact (not_le.1 hG).le
          have hstrict : sl = true → l < 0 := fun h => by
            subst h
            exact not_le.1 hG
          have hpoint : ∃ x : ℝ, ((if sl = true then l < x else l ≤ x) ∧
              (if su = true then x < u else x ≤ u)) ∧ x ≤ 0 := by
            by_cases hu : 0 < u
            · refine ⟨l / 2, ⟨?_, ?_⟩, by linarith⟩
              · split_ifs with h
                · have := hstrict h
                  linarith
                · linarith
              · split_ifs <;> linarith
            · have hu0 : u ≤ 0 := not_lt.1 hu
              rcases lt_or_eq_of_le hlu with hlt | heq
              · refine ⟨(l + u) / 2, ⟨?_, ?_⟩, by linarith⟩
                · split_ifs <;> linarith
                · split_ifs <;> linarith
              · subst heq
                have hns : sl = false ∧ su = false := by
                  cases sl <;> cases su <;> simp_all
                obtain ⟨rfl, rfl⟩ := hns
                exact ⟨l, ⟨le_refl l, le_refl l⟩, hl0⟩
          obtain ⟨x, hx, hx0⟩ := hpoint
          exact interval_observation_missing swap sl su l u hf hx (hv.undefined x hx0)
      · rw [interval_observation_empty swap sl su l u hf hT, decide_eq_false hT]
        rfl

/-! A factor that does not mention the axis, anywhere in a product with such a
value. Where the guard of the bounds is on the positive axis the value is
integrable whatever the factor is, so the factor stands in front of the
difference of the antiderivative, under the same guard. -/

/-- A polynomial times the logarithm plus a polynomial under an optional
factor that does not depend on the axis. With `log` the value is undefined
off the positive axis and the equation is for the positive axis; without it
there is no logarithm, and the equation holds everywhere. -/
structure LogFraction (v : ℝ → Option ℝ) (S : Option (Option ℝ)) (p q : List ℚ)
    (log : Bool) : Prop where
  equation : ∀ x : ℝ, (log = true → 0 < x) →
    v x = scaleBy S (some (polyEval p x * Real.log x + polyEval q x))
  undefined : log = true → ∀ x : ℝ, x ≤ 0 → v x = none
  plain : log = false → ∀ x : ℝ, polyEval p x = 0

theorem LogFraction.polynomial {f : ℝ → Option ℝ} {q : List ℚ}
    (hf : PolynomialOn (fun _ => True) f q) : LogFraction f none [] q false :=
  ⟨fun x _ => by
    rw [hf.equation x trivial]
    simp [scaleBy, polyEval], fun h => (by cases h), fun _ _ => rfl⟩

theorem LogFraction.log {f : ℝ → Option ℝ} {p q : List ℚ} (hf : LogOn f p q) :
    LogFraction f none p q true :=
  ⟨fun x hx => by
    rw [hf.equation x (hx rfl)]
    rfl, fun _ => hf.undefined, fun h => by cases h⟩

/-- A factor that does not depend on the axis. -/
theorem LogFraction.scale (c : Option ℝ) : LogFraction (fun _ => c) (some c) [] [1] false :=
  ⟨fun x _ => by cases c <;> simp [scaleBy, Value.mul, polyEval], fun h => (by cases h),
    fun _ _ => rfl⟩

/-- Products with a factor without a logarithm, on either side. -/
theorem LogFraction.mul_left {f g : ℝ → Option ℝ} {S T : Option (Option ℝ)} {p q p' q' : List ℚ}
    {b : Bool} (hf : LogFraction f S p q false) (hg : LogFraction g T p' q' b) :
    LogFraction (fun x => Value.mul (f x) (g x)) (joinScale S T) (polyMul q p') (polyMul q q')
      b :=
  ⟨fun x hx => by
    show Value.mul (f x) (g x) = _
    have hp := hf.plain rfl x
    rw [hf.equation x (fun h => by cases h), hg.equation x hx, polyEval_mul, polyEval_mul, hp]
    rcases S with _ | _ | s <;> rcases T with _ | _ | t <;>
      simp [scaleBy, joinScale, Value.mul] <;> ring, fun h x hx => by
    show Value.mul (f x) (g x) = none
    rw [hg.undefined h x hx]
    cases f x <;> rfl, fun h x => by
    rw [polyEval_mul, hg.plain h x, mul_zero]⟩

theorem LogFraction.mul_right {f g : ℝ → Option ℝ} {S T : Option (Option ℝ)}
    {p q p' q' : List ℚ} {b : Bool} (hg : LogFraction g T p' q' b)
    (hf : LogFraction f S p q false) :
    LogFraction (fun x => Value.mul (g x) (f x)) (joinScale T S) (polyMul p' q) (polyMul q' q)
      b :=
  ⟨fun x hx => by
    show Value.mul (g x) (f x) = _
    have hp := hf.plain rfl x
    rw [hf.equation x (fun h => by cases h), hg.equation x hx, polyEval_mul, polyEval_mul, hp]
    rcases S with _ | _ | s <;> rcases T with _ | _ | t <;>
      simp [scaleBy, joinScale, Value.mul] <;> ring, fun h x hx => by
    show Value.mul (g x) (f x) = none
    rw [hg.undefined h x hx]
    rfl, fun h x => by
    rw [polyEval_mul, hg.plain h x, zero_mul]⟩

/-- Under the guard of its domain it is the same. -/
theorem LogFraction.guard {v : ℝ → Option ℝ} {S : Option (Option ℝ)} {p q : List ℚ}
    {g : ℝ → Option Bool} (hv : LogFraction v S p q true)
    (hg : ∀ x : ℝ, 0 < x → g x = some true) :
    LogFraction (fun x => Binding.guardValue (g x) (v x)) S p q true :=
  ⟨fun x hx => by
    show Binding.guardValue (g x) (v x) = _
    rw [hg x (hx rfl), hv.equation x hx]
    rfl, fun _ x hx => by
    show Binding.guardValue (g x) (v x) = none
    rw [hv.undefined rfl x hx]
    simp [Binding.guardValue], fun h => by cases h⟩

/-- Under a factor the value is the factor times such a value, strictly. -/
private theorem LogFraction.split {v : ℝ → Option ℝ} {c : Option ℝ} {p q : List ℚ}
    (hv : LogFraction v (some c) p q true) :
    ∃ w : ℝ → Option ℝ, LogOn w p q ∧ ∀ x, v x = Value.mul c (w x) := by
  classical
  refine ⟨fun x => if 0 < x then some (polyEval p x * Real.log x + polyEval q x) else none,
    ⟨fun x hx => by simp [hx], fun x hx => by simp [not_lt.2 hx]⟩, fun x => ?_⟩
  by_cases hx : 0 < x
  · rw [hv.equation x (fun _ => hx)]
    simp [scaleBy, hx]
  · rw [hv.undefined rfl x (not_lt.1 hx)]
    cases c <;> simp [Value.mul, hx]

/-- Where the comparison of the bounds and the guard hold the bounds are on
the positive axis, the lower one possibly at zero where it is strict. -/
private theorem log_side {sl su : Bool} {l u : ℝ}
    (hT : if (sl || su) = true then l < u else l ≤ u)
    (hG : if (!sl) = true then (0 : ℝ) < l else 0 ≤ l) :
    0 < u ∧ (0 < l ∨ (l = 0 ∧ sl = true)) := by
  cases sl
  · have hG' : 0 < l := hG
    have hlu : l ≤ u := by
      split_ifs at hT
      · exact hT.le
      · exact hT
    exact ⟨lt_of_lt_of_le hG' hlu, Or.inl hG'⟩
  · have hG' : 0 ≤ l := hG
    have hT' : l < u := hT
    refine ⟨lt_of_le_of_lt hG' hT', ?_⟩
    rcases lt_or_eq_of_le hG' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.symm, rfl⟩

/-- The antiderivative at the bounds where they are on the positive axis. -/
private theorem logPrimitive_defined {P₁ S₁ : List ℚ} {sl : Bool} {l u : ℝ}
    {p1b s1b p1a s1a : Option ℝ} {mspb mssb mspa mssa : List (Option ℝ)}
    (hpb : RowTerms none (some u) P₁ 0 [] mspb) (hspb : Sums mspb p1b)
    (hsb : RowTerms none (some u) S₁ 0 [] mssb) (hssb : Sums mssb s1b)
    (hpa : RowTerms none (some l) P₁ 0 [] mspa) (hspa : Sums mspa p1a)
    (hsa : RowTerms none (some l) S₁ 0 [] mssa) (hssa : Sums mssa s1a)
    (hu : 0 < u) (hl : 0 < l ∨ (l = 0 ∧ sl = true)) :
    Value.add (logPrimitive false p1b s1b (some u))
        (Value.mul (some (-1 : ℝ)) (logPrimitive sl p1a s1a (some l))) =
      some (u * polyEval P₁ u * Real.log u + u * polyEval S₁ u +
        -1 * (l * polyEval P₁ l * Real.log l + l * polyEval S₁ l)) := by
  rw [logPrimitive_positive hpb hspb hsb hssb false rfl hu]
  rcases hl with hl | ⟨rfl, rfl⟩
  · rw [logPrimitive_positive hpa hspa hsa hssa sl rfl hl]
    rfl
  · rw [logPrimitive_zero hpa hspa hsa hssa rfl]
    simp [Value.add, Value.mul]

/-- Between two bounds under a factor `c`: the factor times the difference
of the antiderivative, under the same mask and guard. -/
theorem log_between_scaled (swap sl su : Bool) {a b c : Option ℝ} {v : ℝ → Option ℝ}
    {p q : List ℚ} (P₁ S₁ : List ℚ) (hv : LogFraction v (some c) p q true)
    (hc : logCheck p q P₁ S₁ = true) {z m p1b p1a s1b s1a : Option ℝ}
    {mspb mspa mssb mssa : List (Option ℝ)}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hpb : RowTerms none b P₁ 0 [] mspb) (hspb : Sums mspb p1b)
    (hsb : RowTerms none b S₁ 0 [] mssb) (hssb : Sums mssb s1b)
    (hpa : RowTerms none a P₁ 0 [] mspa) (hspa : Sums mspa p1a)
    (hsa : RowTerms none a S₁ 0 [] mssa) (hssa : Sums mssa s1a) :
    partialIntegral volume (fun x => Value.mask (intervalGuard swap sl su a b x) (v x)) =
      Value.mask (compare (sl || su) a b) (Binding.guardValue (compare (!sl) z a)
        (Value.mul c (Value.add (logPrimitive false p1b s1b b)
          (Value.mul m (logPrimitive sl p1a s1a a))))) := by
  obtain ⟨w, hw, hvw⟩ := hv.split
  have hI := log_between swap sl su P₁ S₁ hw hc hz hm hpb hspb hsb hssb hpa hspa hsa hssa
  have hZ : z = some (0 : ℝ) := by rw [hz]; simp [Numeric.denote]
  have hMinus : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  subst hZ hMinus
  have hfun : (fun x => Value.mask (intervalGuard swap sl su a b x) (v x)) =
      fun x => Value.mask (intervalGuard swap sl su a b x) (Value.mul c (w x)) :=
    funext fun x => by rw [hvw x]
  rw [hfun, scaled_observation]
  cases c with
  | none =>
    show partialIntegral volume
      (fun x => Value.mask (intervalGuard swap sl su a b x) (none : Option ℝ)) = _
    rw [between_undefined]
    have hn : ∀ (G : Option Bool) (X : Option ℝ),
        Binding.guardValue G (Value.mul (none : Option ℝ) X) = none := fun G X => by
      simp [Value.mul, Binding.guardValue]
    rw [hn]
  | some γ =>
    by_cases hγ : γ = 0
    · subst hγ
      show (if (0 : ℝ) = 0 then _ else _) = _
      rw [if_pos rfl]
      -- Under a factor of zero the value is zero on the positive axis.
      have hw0 : LogOn (fun x => (w x).map fun _ => (0 : ℝ)) [] [] :=
        ⟨fun x hx => by
          show (w x).map _ = _
          rw [hw.equation x hx]
          simp [polyEval], fun x hx => by
          show (w x).map _ = none
          rw [hw.undefined x hx]
          rfl⟩
      have hrow : ∀ o : Option ℝ, RowTerms none o [0] 0 []
          [monomial none (powerValue o 0 (some (0 : ℝ)))] := fun o =>
        RowTerms.term (0 : ℚ) hz RowTerms.done
      rw [log_between swap sl su [0] [0] hw0
        (by simp [logCheck, polyDerivative, polyAdd, polyScale, polyZero]) hz hm
        (hrow b) Sums.one (hrow b) Sums.one (hrow a) Sums.one (hrow a) Sums.one]
      by_cases h : a = none ∨ b = none
      · rw [compare_undefined _ h]
        rfl
      obtain ⟨l, rfl⟩ := Option.ne_none_iff_exists'.1 fun ha => h (Or.inl ha)
      obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 fun hb => h (Or.inr hb)
      rw [compare_real, compare_real]
      by_cases hT : (if (sl || su) = true then l < u else l ≤ u)
      swap
      · rw [decide_eq_false hT]
        rfl
      by_cases hG : (if (!sl) = true then (0 : ℝ) < l else 0 ≤ l)
      swap
      · rw [decide_eq_false hG]
        rfl
      obtain ⟨hu, hl⟩ := log_side hT hG
      rw [logPrimitive_defined hpb hspb hsb hssb hpa hspa hsa hssa hu hl,
        logPrimitive_defined (hrow (some u)) Sums.one (hrow (some u)) Sums.one
          (hrow (some l)) Sums.one (hrow (some l)) Sums.one hu hl]
      simp [polyEval, Value.mul]
    · show (if γ = 0 then _ else _) = _
      rw [if_neg hγ, hI, mul_mask_guard]

end QSym.Distribution.StepSource
