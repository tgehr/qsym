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

end QSym.Distribution.StepSource
