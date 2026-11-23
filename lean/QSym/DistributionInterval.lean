import QSym.DistributionPolynomialGrid
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Intervals with symbolic endpoints. The guard is one lower and one upper
comparison of the axis with two partial bounds, in either order, strict or
not. The masked value is a sum of polynomials with rational coefficients,
each optionally times an exponential of rational rate and optionally scaled
by a partial constant. The result is an equation of
partial values for every definedness pattern of the bounds and scales: the
conjunction and the mask are not strict, so an empty interval forgets a
missing scale, and exactly then the comparison of the bounds is false.

The antiderivative of every term is an expression of the frontend with its
own evidence of the same kind. The certificate only checks that its
derivative is the integrand, by kernel reduction on rational coefficient
lists: for Q·exp(r·x) this is Q' + r·Q = P. -/
noncomputable section
namespace QSym.Distribution.StepSource
open MeasureTheory Set

/-- Derivative of a coefficient list in Horner form. -/
def polyDerivative : List ℚ → List ℚ
  | [] => []
  | _ :: p => polyAdd p (0 :: polyDerivative p)

/-- The first list times exp(s·x) is an antiderivative of the second list
times exp(r·x): the rates agree and Q' + s·Q = P up to trailing zeros. -/
def expPrimitive (P p : List ℚ) (r s : ℚ) : Bool :=
  decide (r = s) &&
    polyZero (polyAdd (polyAdd (polyDerivative P) (polyScale s P)) (polyScale (-1) p))

theorem polyEval_hasDerivAt (p : List ℚ) (x : ℝ) :
    HasDerivAt (polyEval p) (polyEval (polyDerivative p) x) x := by
  induction p with
  | nil => exact hasDerivAt_const x (0 : ℝ)
  | cons c p ih =>
    have h := (hasDerivAt_const x (c : ℝ)).add ((hasDerivAt_id x).mul ih)
    have he : polyEval (c :: p) = fun y => (c : ℝ) + id y * polyEval p y := rfl
    rw [he]
    convert h using 1
    simp only [polyDerivative, polyEval_add, polyEval, Rat.cast_zero, id]
    ring

theorem expPrimitive_deriv {P p : List ℚ} {r s : ℚ} (h : expPrimitive P p r s = true) (x : ℝ) :
    HasDerivAt (fun y => polyEval P y * Real.exp ((s : ℝ) * y))
      (polyEval p x * Real.exp ((r : ℝ) * x)) x := by
  simp only [expPrimitive, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hr, hz⟩ := h
  subst hr
  have hz := polyEval_zero hz x
  rw [polyEval_add, polyEval_add, polyEval_scale, polyEval_scale] at hz
  have he : polyEval (polyDerivative P) x + (r : ℝ) * polyEval P x = polyEval p x := by
    push_cast at hz; linarith
  have hd := (polyEval_hasDerivAt P x).mul
    ((Real.hasDerivAt_exp ((r : ℝ) * x)).comp x ((hasDerivAt_id x).const_mul (r : ℝ)))
  convert hd using 1
  rw [← he]
  simp only [id, mul_one, Function.comp_apply]
  ring

theorem expPolynomial_continuous (p : List ℚ) (r : ℚ) :
    Continuous (fun x => polyEval p x * Real.exp ((r : ℝ) * x)) :=
  (polyEval_continuous p).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem expPrimitive_integral {P p : List ℚ} {r s : ℚ} (h : expPrimitive P p r s = true)
    (l u : ℝ) :
    ∫ x in l..u, polyEval p x * Real.exp ((r : ℝ) * x) =
      polyEval P u * Real.exp ((s : ℝ) * u) - polyEval P l * Real.exp ((s : ℝ) * l) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => expPrimitive_deriv h x)
    ((expPolynomial_continuous p r).intervalIntegrable _ _)

/-- A frontend comparison, strict or not. -/
def compare : Bool → Option ℝ → Option ℝ → Option Bool
  | true => Value.lt
  | false => Value.le

/-- One lower and one upper bound of the axis, in either order. -/
def intervalGuard (swap strictLower strictUpper : Bool) (a b : Option ℝ) (x : ℝ) : Option Bool :=
  match swap with
  | false => Value.and (compare strictLower a (some x)) (compare strictUpper (some x) b)
  | true => Value.and (compare strictUpper (some x) b) (compare strictLower a (some x))

/-- A polynomial times an exponential of rational rate, everywhere. A rate
of zero is a polynomial. -/
structure ExpPolynomial (v : ℝ → Option ℝ) (p : List ℚ) (r : ℚ) : Prop where
  equation : ∀ x, v x = some (polyEval p x * Real.exp ((r : ℝ) * x))

theorem exp_polynomial {v : ℝ → Option ℝ} {p : List ℚ}
    (h : PolynomialOn (fun _ => True) v p) : ExpPolynomial v p 0 :=
  ⟨fun x => by rw [h.equation x trivial]; simp⟩

/-- The exponential of a rational multiple of the axis. -/
theorem exp_affine {f : ℝ → Option ℝ} {r : ℚ} (hf : Affine f r 0) :
    ExpPolynomial (fun x => Functions.expR.apply (f x)) [1] r :=
  ⟨fun x => by rw [hf x]; simp [Function1.apply, Functions.expR, polyEval]⟩

theorem exp_mul {v w : ℝ → Option ℝ} {p q : List ℚ} {r s : ℚ}
    (hv : ExpPolynomial v p r) (hw : ExpPolynomial w q s) :
    ExpPolynomial (fun x => Value.mul (v x) (w x)) (polyMul p q) (r + s) :=
  ⟨fun x => by
    rw [hv.equation x, hw.equation x]
    simp only [Value.mul, polyEval_mul, Rat.cast_add, add_mul, Real.exp_add, Option.some.injEq]
    ring⟩

/-- The same, scaled by a partial constant. -/
structure Scaled (v : ℝ → Option ℝ) (c : Option ℝ) (p : List ℚ) (r : ℚ) : Prop where
  equation : ∀ x, v x = Value.mul c (some (polyEval p x * Real.exp ((r : ℝ) * x)))

theorem scaled_constant (c : Option ℝ) : Scaled (fun _ => c) c [1] 0 :=
  ⟨fun x => by cases c <;> simp [Value.mul, polyEval]⟩

/-- Total factors multiply the polynomial part on either side. -/
theorem scaled_times {v w : ℝ → Option ℝ} {c : Option ℝ} {p q : List ℚ} {r s : ℚ}
    (hv : Scaled v c p r) (hw : ExpPolynomial w q s) :
    Scaled (fun x => Value.mul (v x) (w x)) c (polyMul p q) (r + s) :=
  ⟨fun x => by
    rw [hv.equation x, hw.equation x]
    cases c <;>
      simp only [Value.mul, polyEval_mul, Rat.cast_add, add_mul, Real.exp_add, Option.some.injEq]
    ring⟩

theorem scaled_after {v w : ℝ → Option ℝ} {c : Option ℝ} {p q : List ℚ} {r s : ℚ}
    (hw : ExpPolynomial w q s) (hv : Scaled v c p r) :
    Scaled (fun x => Value.mul (w x) (v x)) c (polyMul q p) (s + r) :=
  ⟨fun x => by
    rw [hv.equation x, hw.equation x]
    cases c <;>
      simp only [Value.mul, polyEval_mul, Rat.cast_add, add_mul, Real.exp_add, Option.some.injEq]
    ring⟩

/-- Two scaled factors: the scales multiply, strictly. -/
theorem scaled_mul {v w : ℝ → Option ℝ} {c d : Option ℝ} {p q : List ℚ} {r s : ℚ}
    (hv : Scaled v c p r) (hw : Scaled w d q s) :
    Scaled (fun x => Value.mul (v x) (w x)) (Value.mul c d) (polyMul p q) (r + s) :=
  ⟨fun x => by
    rw [hv.equation x, hw.equation x]
    cases c <;> cases d <;>
      simp only [Value.mul, polyEval_mul, Rat.cast_add, add_mul, Real.exp_add, Option.some.injEq]
    ring⟩

theorem polynomial_unit (s : ℝ → Prop) : PolynomialOn s (fun _ => some (1 : ℝ)) [1] :=
  ⟨fun x _ => by simp [polyEval]⟩

/-- A cast Iverson bracket is a real mask of one. -/
theorem bracket_real (g : Option Bool) (one : Option ℕ) (h : one = some 1) :
    Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply (Value.mask g one))) =
      Value.mask g (some (1 : ℝ)) := by
  subst h
  rcases g with _ | _ | _ <;>
    simp [Value.mask, Function1.apply, Functions.castNZ, Functions.castZQ, Functions.castQR]

/-- Two nested masks are the mask of their conjunction, for every
definedness pattern: neither spelling is strict in what a false guard hides. -/
theorem mask_mask {α : Type} [Zero α] (p q : Option Bool) (v : Option α) :
    Value.mask p (Value.mask q v) = Value.mask (Value.and p q) v := by
  rcases p with _ | _ | _ <;> rfl

/-- The casts of an Iverson bracket commute with its mask. -/
theorem cast_mask (p : Option Bool) (n : Option ℕ) :
    Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply (Value.mask p n))) =
      Value.mask p (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))) := by
  rcases p with _ | _ | _ <;>
    simp [Value.mask, Function1.apply, Functions.castNZ, Functions.castZQ, Functions.castQR]

theorem cast_mask_and (p q : Option Bool) (n : Option ℕ) :
    Functions.castQR.apply (Functions.castZQ.apply
        (Functions.castNZ.apply (Value.mask (Value.and p q) n))) =
      Value.mask p (Functions.castQR.apply (Functions.castZQ.apply
        (Functions.castNZ.apply (Value.mask q n)))) := by
  rw [← mask_mask, cast_mask]

/-- The density of a program is a mask of the guard. -/
structure Masked (f : ℝ → Option ℝ) (g : ℝ → Option Bool) (v : ℝ → Option ℝ) : Prop where
  equation : ∀ x, f x = Value.mask (g x) (v x)

theorem masked_first {w : ℝ → Option ℝ} {g : ℝ → Option Bool} {v : ℝ → Option ℝ}
    (h : ∀ x, w x = Value.mask (g x) (v x)) :
    Masked (DensityProgram.density (.weight w .lebesgue)) g v :=
  ⟨fun x => by simp only [DensityProgram.density, Value.mul_one_left, h x]⟩

/-- A total factor moves below the mask. -/
theorem masked_times {f w : ℝ → Option ℝ} {g : ℝ → Option Bool} {v : ℝ → Option ℝ}
    {q : List ℚ} {s : ℚ} (hf : Masked f g v) (hw : ExpPolynomial w q s) :
    Masked (fun x => Value.mul (f x) (w x)) g (fun x => Value.mul (v x) (w x)) :=
  ⟨fun x => by
    rw [hf.equation x, hw.equation x]
    rcases g x with _ | _ | _ <;> simp [Value.mask, Value.mul]⟩

/-- The value below the mask and its integral between the bounds. Each
antiderivative is evaluated at the partial bounds themselves, so the result
contains no application. The last operand of the difference is the literal
minus one of the frontend. -/
inductive IntervalTerms (a b m : Option ℝ) : (ℝ → Option ℝ) → Option ℝ → Prop
  | pure {v : ℝ → Option ℝ} {G : Option ℝ → Option ℝ} {p P : List ℚ} {r s : ℚ}
      (hv : ExpPolynomial v p r) (hG : ExpPolynomial (fun t => G (some t)) P s)
      (hd : expPrimitive P p r s = true) :
      IntervalTerms a b m v (Value.add (G b) (Value.mul m (G a)))
  | scaled {v : ℝ → Option ℝ} {G : Option ℝ → Option ℝ} {c : Option ℝ} {p P : List ℚ}
      {r s : ℚ} (hv : Scaled v c p r) (hG : ExpPolynomial (fun t => G (some t)) P s)
      (hd : expPrimitive P p r s = true) :
      IntervalTerms a b m v (Value.mul c (Value.add (G b) (Value.mul m (G a))))
  | add {v w : ℝ → Option ℝ} {s t : Option ℝ} :
      IntervalTerms a b m v s → IntervalTerms a b m w t →
      IntervalTerms a b m (fun x => Value.add (v x) (w x)) (Value.add s t)

private theorem difference {G : Option ℝ → Option ℝ} {P p : List ℚ} {r s : ℚ}
    (hG : ExpPolynomial (fun t => G (some t)) P s) (hd : expPrimitive P p r s = true)
    (l u : ℝ) :
    Value.add (G (some u)) (Value.mul (some (-1)) (G (some l))) =
      some (∫ x in l..u, polyEval p x * Real.exp ((r : ℝ) * x)) := by
  rw [expPrimitive_integral hd, hG.equation u, hG.equation l]
  simp only [Value.mul, Value.add, Option.some.injEq]
  ring

/-- Either a continuous integrand with its integral, or nothing anywhere. -/
theorem IntervalTerms.sound {a b m : Option ℝ} {v : ℝ → Option ℝ} {out : Option ℝ}
    (h : IntervalTerms a b m v out) (hm : m = some (-1 : ℝ)) {l u : ℝ}
    (ha : a = some l) (hb : b = some u) :
    (∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, v x = some (g x)) ∧ out = some (∫ x in l..u, g x)) ∨
      ((∀ x, v x = none) ∧ out = none) := by
  subst hm ha hb
  induction h with
  | @pure v G p P r s hv hG hd =>
    exact Or.inl ⟨_, expPolynomial_continuous p r, hv.equation, difference hG hd l u⟩
  | @scaled v G c p P r s hv hG hd =>
    cases c with
    | none => exact Or.inr ⟨fun x => by rw [hv.equation x]; rfl, rfl⟩
    | some c =>
      refine Or.inl ⟨fun x => c * (polyEval p x * Real.exp ((r : ℝ) * x)),
        continuous_const.mul (expPolynomial_continuous p r),
        fun x => by rw [hv.equation x]; rfl, ?_⟩
      rw [difference hG hd l u, intervalIntegral.integral_const_mul]
      rfl
  | @add v w s t _ _ ih₁ ih₂ =>
    rcases ih₁ with ⟨g, hg, hv, hs⟩ | ⟨hv, hs⟩
    · rcases ih₂ with ⟨k, hk, hw, ht⟩ | ⟨hw, ht⟩
      · refine Or.inl ⟨fun x => g x + k x, hg.add hk, fun x => ?_, ?_⟩
        · show Value.add (v x) (w x) = _
          rw [hv x, hw x]; rfl
        · rw [hs, ht, intervalIntegral.integral_add (hg.intervalIntegrable _ _)
            (hk.intervalIntegrable _ _)]
          rfl
      · refine Or.inr ⟨fun x => ?_, by rw [hs, ht]; rfl⟩
        show Value.add (v x) (w x) = _
        rw [hv x, hw x]; rfl
    · refine Or.inr ⟨fun x => ?_, by rw [hs]; rfl⟩
      show Value.add (v x) (w x) = _
      rw [hv x]; rfl

private theorem and_some (p q : Bool) : Value.and (some p) (some q) = some (p && q) := by
  cases p <;> rfl

private theorem guard_defined (swap sl su : Bool) (l u x : ℝ) :
    intervalGuard swap sl su (some l) (some u) x =
      some (decide ((if sl then l < x else l ≤ x) ∧ (if su then x < u else x ≤ u))) := by
  cases swap <;> cases sl <;> cases su <;>
    simp [intervalGuard, compare, and_some, Value.lt, Value.le, Bool.and_comm]

private theorem compare_defined (s : Bool) (l u : ℝ) :
    compare s (some l) (some u) = some (decide (if s then l < u else l ≤ u)) := by
  cases s <;> simp [compare, Value.lt, Value.le]

private theorem zero_integral (f : ℝ → Option ℝ) (h : ∀ x, f x = some 0) :
    partialIntegral volume f = some 0 := by
  rw [funext h, partialIntegral_valid volume _ (fun _ => ⟨0, rfl⟩) (by simp)]
  simp

private theorem mask_decide (T : Prop) [Decidable T] (v : Option ℝ) :
    Value.mask (some (decide T)) v = if T then v else some 0 := by
  by_cases h : T <;> simp [h, Value.mask]

private theorem test_of_lt (s : Bool) {l u : ℝ} (h : l < u) :
    if s = true then l < u else l ≤ u := by
  split_ifs
  · exact h
  · exact le_of_lt h

private theorem le_of_test (s : Bool) {l u : ℝ} (h : if s = true then l < u else l ≤ u) :
    l ≤ u := by
  split_ifs at h
  · exact le_of_lt h
  · exact h

/-- The comparison of the bounds says exactly that the guard holds somewhere. -/
private theorem region_nonempty (sl su : Bool) {l u : ℝ}
    (h : if (sl || su) = true then l < u else l ≤ u) :
    ∃ x : ℝ, (if sl = true then l < x else l ≤ x) ∧ (if su = true then x < u else x ≤ u) := by
  revert h
  cases sl <;> cases su <;> intro h
  · exact ⟨l, le_refl l, h⟩
  · exact ⟨l, le_refl l, h⟩
  · exact ⟨u, h, le_refl u⟩
  · have h' : l < u := h
    exact ⟨(l + u) / 2, show l < (l + u) / 2 by linarith, show (l + u) / 2 < u by linarith⟩

private theorem region_empty (sl su : Bool) {l u : ℝ}
    (h : ¬(if (sl || su) = true then l < u else l ≤ u)) (x : ℝ) :
    ¬((if sl = true then l < x else l ≤ x) ∧ (if su = true then x < u else x ≤ u)) := by
  rintro ⟨h1, h2⟩
  apply h
  revert h1 h2
  cases sl <;> cases su <;> intro h1 h2
  · exact le_trans h1 h2
  · exact lt_of_le_of_lt h1 h2
  · exact lt_of_lt_of_le h1 h2
  · exact lt_trans h1 h2

/-- The observation of a guarded value between two partial bounds. -/
theorem interval_integral (swap sl su : Bool) (a b m : Option ℝ)
    {f v : ℝ → Option ℝ} {out : Option ℝ} (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hf : Masked f (intervalGuard swap sl su a b) v) (ht : IntervalTerms a b m v out) :
    partialIntegral volume f = Value.mask (compare (sl || su) a b) out := by
  have hm : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  have missing : ∀ y, f y = none → partialIntegral volume f = none := by
    intro y hy
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
    | none =>
      exact missing 0 (by
        rw [hf.equation]
        cases swap <;> cases sl <;> cases su <;> rfl)
    | some u =>
      refine missing (u - 1) ?_
      rw [hf.equation]
      cases swap <;> cases sl <;> cases su <;>
        simp [intervalGuard, compare, Value.and, Value.lt, Value.le, Value.mask]
  | some l =>
    cases b with
    | none =>
      have hn : compare (sl || su) (some l) none = none := by cases sl <;> cases su <;> rfl
      rw [hn]
      refine missing (l + 1) ?_
      rw [hf.equation]
      cases swap <;> cases sl <;> cases su <;>
        simp [intervalGuard, compare, Value.and, Value.lt, Value.le, Value.mask]
    | some u =>
      have hg := guard_defined swap sl su l u
      rw [compare_defined, mask_decide]
      rcases ht.sound hm rfl rfl with ⟨g, hc, hv, ho⟩ | ⟨hv, ho⟩
      · -- A continuous integrand on the interval, zero outside it.
        have total : ∀ x, Value.Defined (f x) := by
          intro x
          rw [hf.equation, hg, hv, mask_decide]
          split_ifs <;> exact ⟨_, rfl⟩
        have he : (fun x => (f x).getD 0) =ᵐ[volume] (Ioo l u).indicator g := by
          filter_upwards [ae_away [l, u]] with x hx
          have hl : x ≠ l := hx l (by simp)
          have hu : x ≠ u := hx u (by simp)
          rw [hf.equation, hg, hv, mask_decide]
          by_cases hi : x ∈ Ioo l u
          · have hin : (if sl = true then l < x else l ≤ x) ∧
                (if su = true then x < u else x ≤ u) := by
              constructor
              · split_ifs
                · exact hi.1
                · exact le_of_lt hi.1
              · split_ifs
                · exact hi.2
                · exact le_of_lt hi.2
            rw [if_pos hin, Set.indicator_of_mem hi, Option.getD_some]
          · have hout : ¬((if sl = true then l < x else l ≤ x) ∧
                (if su = true then x < u else x ≤ u)) := by
              rintro ⟨h1, h2⟩
              apply hi
              constructor
              · split_ifs at h1
                · exact h1
                · exact lt_of_le_of_ne h1 (Ne.symm hl)
              · split_ifs at h2
                · exact h2
                · exact lt_of_le_of_ne h2 hu
            rw [if_neg hout, Set.indicator_of_not_mem hi, Option.getD_some]
        have hi : Integrable ((Ioo l u).indicator g) volume :=
          (integrable_indicator_iff measurableSet_Ioo).mpr
            (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
        rw [partialIntegral_valid volume f total ((integrable_congr he).mpr hi),
          integral_congr_ae he, integral_indicator measurableSet_Ioo, ho]
        by_cases hlu : l ≤ u
        · have hI : ∫ x in Ioo l u, g x = ∫ x in l..u, g x := by
            rw [intervalIntegral.integral_of_le hlu, integral_Ioc_eq_integral_Ioo]
          rw [hI]
          by_cases hT : (if (sl || su) = true then l < u else l ≤ u)
          · rw [if_pos hT]
          · have he' : l = u := by
              by_cases hlt : l < u
              · exact absurd (test_of_lt _ hlt) hT
              · exact le_antisymm hlu (not_lt.mp hlt)
            subst he'
            rw [if_neg hT, intervalIntegral.integral_same]
        · have hempty : Ioo l u = ∅ := Ioo_eq_empty (fun h => hlu (le_of_lt h))
          have hT : ¬(if (sl || su) = true then l < u else l ≤ u) :=
            fun h => hlu (le_of_test _ h)
          rw [hempty, Measure.restrict_empty, integral_zero_measure, if_neg hT]
      · -- A missing value is forgotten exactly on an empty interval.
        rw [ho]
        by_cases hT : (if (sl || su) = true then l < u else l ≤ u)
        · obtain ⟨x, hx⟩ := region_nonempty sl su hT
          rw [if_pos hT]
          refine missing x ?_
          rw [hf.equation, hg, hv, mask_decide, if_pos hx]
        · rw [if_neg hT]
          refine zero_integral f (fun x => ?_)
          rw [hf.equation, hg, mask_decide, if_neg (region_empty sl su hT x)]

/-! A half-line. Below one lower bound every term must decay: a negative
rate. The antiderivative then vanishes at infinity, so the result is its
value at the bound with the opposite sign, and no limit is left behind. -/

open Filter Asymptotics Topology in
theorem polyEval_isBigO_exp (p : List ℚ) {b : ℝ} (hb : 0 < b) :
    (polyEval p) =O[atTop] fun x => Real.exp (b * x) := by
  induction p generalizing b with
  | nil =>
    exact (isBigO_zero _ _).congr_left (fun _ => rfl)
  | cons c p ih =>
    have hc : (fun _ : ℝ => (c : ℝ)) =O[atTop] fun x => Real.exp (b * x) := by
      refine IsBigO.of_bound |(c : ℝ)| ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have h1 : (1 : ℝ) ≤ Real.exp (b * x) := Real.one_le_exp (mul_nonneg hb.le hx)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      nlinarith [abs_nonneg (c : ℝ)]
    have hx : (fun x : ℝ => x) =O[atTop] fun x => Real.exp (b / 2 * x) := by
      simpa using (isLittleO_pow_exp_pos_mul_atTop 1 (half_pos hb)).isBigO
    have hm := hx.mul (ih (half_pos hb))
    have he : (fun x : ℝ => Real.exp (b / 2 * x) * Real.exp (b / 2 * x)) =
        fun x => Real.exp (b * x) := by
      funext x; rw [← Real.exp_add]; congr 1; ring
    rw [he] at hm
    exact hc.add hm

open Filter Asymptotics Topology in
theorem expPolynomial_isBigO (p : List ℚ) {r : ℝ} (hr : r < 0) :
    (fun x => polyEval p x * Real.exp (r * x)) =O[atTop] fun x => Real.exp (-(-r / 2) * x) := by
  have hp := polyEval_isBigO_exp p (show (0 : ℝ) < -r / 2 by linarith)
  have hm := hp.mul (isBigO_refl (fun x : ℝ => Real.exp (r * x)) atTop)
  have he : (fun x : ℝ => Real.exp (-r / 2 * x) * Real.exp (r * x)) =
      fun x => Real.exp (-(-r / 2) * x) := by
    funext x; rw [← Real.exp_add]; congr 1; ring
  rwa [he] at hm

open Filter Topology in
theorem expPolynomial_tendsto (p : List ℚ) {r : ℝ} (hr : r < 0) :
    Tendsto (fun x => polyEval p x * Real.exp (r * x)) atTop (𝓝 0) := by
  refine (expPolynomial_isBigO p hr).trans_tendsto ?_
  have hb : (0 : ℝ) < -r / 2 := by linarith
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)
  refine ht.congr (fun x => ?_)
  simp only [Function.comp_apply, id]
  congr 1; ring

theorem expPolynomial_integrableOn (p : List ℚ) {r : ℚ} (hr : (r : ℝ) < 0) (l : ℝ) :
    IntegrableOn (fun x => polyEval p x * Real.exp ((r : ℝ) * x)) (Ioi l) volume :=
  integrable_of_isBigO_exp_neg (show (0 : ℝ) < -(r : ℝ) / 2 by linarith)
    (expPolynomial_continuous p r).continuousOn (expPolynomial_isBigO p hr)

theorem expPrimitive_integral_Ioi {P p : List ℚ} {r s : ℚ} (h : expPrimitive P p r s = true)
    (hr : (r : ℝ) < 0) (l : ℝ) :
    ∫ x in Ioi l, polyEval p x * Real.exp ((r : ℝ) * x) =
      0 - polyEval P l * Real.exp ((s : ℝ) * l) := by
  have hs : s = r := by
    simp only [expPrimitive, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.symm
  have hs' : (s : ℝ) < 0 := by rw [hs]; exact hr
  exact integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => expPrimitive_deriv h x)
    (expPolynomial_integrableOn p hr l) (expPolynomial_tendsto P hs')

/-- The value below the mask of one lower bound and its integral. Every
antiderivative is strict in the bound, so a missing bound is missing in the
result without a mask. -/
inductive HalfLineTerms (a m : Option ℝ) : (ℝ → Option ℝ) → Option ℝ → Prop
  | pure {v : ℝ → Option ℝ} {G : Option ℝ → Option ℝ} {p P : List ℚ} {r s : ℚ}
      (hv : ExpPolynomial v p r) (hG : ExpPolynomial (fun t => G (some t)) P s)
      (h0 : G none = none) (hd : expPrimitive P p r s = true) (hr : decide (r < 0) = true) :
      HalfLineTerms a m v (Value.mul m (G a))
  | scaled {v : ℝ → Option ℝ} {G : Option ℝ → Option ℝ} {c : Option ℝ} {p P : List ℚ}
      {r s : ℚ} (hv : Scaled v c p r) (hG : ExpPolynomial (fun t => G (some t)) P s)
      (h0 : G none = none) (hd : expPrimitive P p r s = true) (hr : decide (r < 0) = true) :
      HalfLineTerms a m v (Value.mul c (Value.mul m (G a)))
  | add {v w : ℝ → Option ℝ} {s t : Option ℝ} :
      HalfLineTerms a m v s → HalfLineTerms a m w t →
      HalfLineTerms a m (fun x => Value.add (v x) (w x)) (Value.add s t)

theorem HalfLineTerms.missing {a m : Option ℝ} {v : ℝ → Option ℝ} {out : Option ℝ}
    (h : HalfLineTerms a m v out) (ha : a = none) : out = none := by
  subst ha
  induction h with
  | pure _ _ h0 _ _ => rw [h0]; cases m <;> rfl
  | @scaled v G c p P r s _ _ h0 _ _ => rw [h0]; cases m <;> cases c <;> rfl
  | add _ _ ih₁ _ => rw [ih₁]; rfl

theorem HalfLineTerms.sound {a m : Option ℝ} {v : ℝ → Option ℝ} {out : Option ℝ}
    (h : HalfLineTerms a m v out) (hm : m = some (-1 : ℝ)) {l : ℝ} (ha : a = some l) :
    (∃ g : ℝ → ℝ, IntegrableOn g (Ioi l) volume ∧ (∀ x, v x = some (g x)) ∧
        out = some (∫ x in Ioi l, g x)) ∨ ((∀ x, v x = none) ∧ out = none) := by
  subst hm ha
  induction h with
  | @pure v G p P r s hv hG _ hd hr =>
    have hr' : (r : ℝ) < 0 := by exact_mod_cast of_decide_eq_true hr
    refine Or.inl ⟨_, expPolynomial_integrableOn p hr' l, hv.equation, ?_⟩
    rw [expPrimitive_integral_Ioi hd hr', hG.equation l]
    simp only [Value.mul, Option.some.injEq]
    ring
  | @scaled v G c p P r s hv hG _ hd hr =>
    have hr' : (r : ℝ) < 0 := by exact_mod_cast of_decide_eq_true hr
    cases c with
    | none => exact Or.inr ⟨fun x => by rw [hv.equation x]; rfl, rfl⟩
    | some c =>
      refine Or.inl ⟨fun x => c * (polyEval p x * Real.exp ((r : ℝ) * x)),
        (expPolynomial_integrableOn p hr' l).const_mul c,
        fun x => by rw [hv.equation x]; rfl, ?_⟩
      rw [integral_const_mul, expPrimitive_integral_Ioi hd hr', hG.equation l]
      simp only [Value.mul, Option.some.injEq]
      ring
  | @add v w s t _ _ ih₁ ih₂ =>
    rcases ih₁ with ⟨g, hg, hv, hs⟩ | ⟨hv, hs⟩
    · rcases ih₂ with ⟨k, hk, hw, ht⟩ | ⟨hw, ht⟩
      · refine Or.inl ⟨fun x => g x + k x, hg.add hk, fun x => ?_, ?_⟩
        · show Value.add (v x) (w x) = _
          rw [hv x, hw x]; rfl
        · rw [hs, ht, integral_add hg hk]
          rfl
      · refine Or.inr ⟨fun x => ?_, by rw [hs, ht]; rfl⟩
        show Value.add (v x) (w x) = _
        rw [hv x, hw x]; rfl
    · refine Or.inr ⟨fun x => ?_, by rw [hs]; rfl⟩
      show Value.add (v x) (w x) = _
      rw [hv x]; rfl

/-- The observation of a guarded value above one partial bound. -/
theorem halfline_integral (strict : Bool) (a m : Option ℝ)
    {f v : ℝ → Option ℝ} {out : Option ℝ} (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hf : Masked f (fun x => compare strict a (some x)) v) (ht : HalfLineTerms a m v out) :
    partialIntegral volume f = out := by
  have hm : m = some (-1 : ℝ) := by rw [hm]; simp [Numeric.denote]
  have missing : ∀ y, f y = none → partialIntegral volume f = none := by
    intro y hy
    apply if_neg
    intro hd
    obtain ⟨r, hr⟩ := hd.1 y
    rw [hy] at hr
    cases hr
  cases a with
  | none =>
    rw [ht.missing rfl]
    exact missing 0 (by rw [hf.equation]; cases strict <;> rfl)
  | some l =>
    have hg : ∀ x, compare strict (some l) (some x) =
        some (decide (if strict = true then l < x else l ≤ x)) := compare_defined strict l
    rcases ht.sound hm rfl with ⟨g, hi, hv, ho⟩ | ⟨hv, ho⟩
    · have total : ∀ x, Value.Defined (f x) := by
        intro x
        rw [hf.equation, hg, hv, mask_decide]
        split_ifs <;> exact ⟨_, rfl⟩
      have he : (fun x => (f x).getD 0) =ᵐ[volume] (Ioi l).indicator g := by
        filter_upwards [ae_away [l]] with x hx
        have hl : x ≠ l := hx l (by simp)
        rw [hf.equation, hg, hv, mask_decide]
        by_cases hin : x ∈ Ioi l
        · have hc : (if strict = true then l < x else l ≤ x) := by
            split_ifs
            · exact hin
            · exact le_of_lt hin
          rw [if_pos hc, Set.indicator_of_mem hin, Option.getD_some]
        · have hc : ¬(if strict = true then l < x else l ≤ x) := by
            intro h
            apply hin
            split_ifs at h
            · exact h
            · exact lt_of_le_of_ne h (Ne.symm hl)
          rw [if_neg hc, Set.indicator_of_not_mem hin, Option.getD_some]
      have hint : Integrable ((Ioi l).indicator g) volume :=
        (integrable_indicator_iff measurableSet_Ioi).mpr hi
      rw [partialIntegral_valid volume f total ((integrable_congr he).mpr hint),
        integral_congr_ae he, integral_indicator measurableSet_Ioi, ho]
    · rw [ho]
      refine missing (l + 1) ?_
      rw [hf.equation, hg, hv, mask_decide]
      have hc : (if strict = true then l < l + 1 else l ≤ l + 1) := by
        split_ifs <;> linarith
      rw [if_pos hc]

end QSym.Distribution.StepSource

namespace QSym.Distribution.DensityProgram

theorem presentation_mass_halfline (p : DensityProgram) (strict : Bool) (a m : Option ℝ)
    {v : ℝ → Option ℝ} {out : Option ℝ} (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hf : StepSource.Masked p.density (fun x => StepSource.compare strict a (some x)) v)
    (ht : StepSource.HalfLineTerms a m v out) :
    massValue p.presentation = out := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.halfline_integral strict a m hm hf ht

theorem presentation_mass_interval (p : DensityProgram) (swap sl su : Bool) (a b m : Option ℝ)
    {v : ℝ → Option ℝ} {out : Option ℝ} (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hf : StepSource.Masked p.density (StepSource.intervalGuard swap sl su a b) v)
    (ht : StepSource.IntervalTerms a b m v out) :
    massValue p.presentation = Value.mask (StepSource.compare (sl || su) a b) out := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.interval_integral swap sl su a b m hm hf ht

/-- A guard that does not mention the axis leaves the observation. The mask
is not strict, so this is an equation even where the inner observation is
missing: a false guard hides it on both sides. -/
theorem mass_guard (p : Option Bool) {w r : ℝ → Option ℝ}
    (h : ∀ x, w x = Value.mask p (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask p (massValue (DensityProgram.weight r .lebesgue).presentation) := by
  rw [mass_bridge, mass_bridge, DensityProgram.mass, DensityProgram.mass,
    Model.densityMassValue_eq, Model.densityMassValue_eq]
  have hw : (DensityProgram.weight w .lebesgue).density = w := by
    funext x; simp only [density, Value.mul_one_left]
  have hr : (DensityProgram.weight r .lebesgue).density = r := by
    funext x; simp only [density, Value.mul_one_left]
  rw [hw, hr, Option.some_bind, Option.some_bind]
  rcases p with _ | _ | _
  · show partialIntegral MeasureTheory.volume w = none
    apply if_neg
    intro hd
    obtain ⟨v, hv⟩ := hd.1 0
    rw [h 0] at hv
    cases hv
  · rw [StepSource.zero_integral w (fun x => h x)]
    rfl
  · have he : w = r := funext h
    rw [he]
    rfl

end QSym.Distribution.DensityProgram
