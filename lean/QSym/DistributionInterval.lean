import QSym.DistributionPolynomialGrid

/-! Intervals with symbolic endpoints. The guard is one lower and one upper
comparison of the axis with two partial bounds, in either order, strict or
not. The masked value is a sum of polynomials with rational coefficients,
each optionally scaled by a partial constant. The result is an equation of
partial values for every definedness pattern of the bounds and scales: the
conjunction and the mask are not strict, so an empty interval forgets a
missing scale, and exactly then the comparison of the bounds is false.

The antiderivative of every term is an expression of the frontend with its
own polynomial evidence. The certificate only checks that its derivative is
the integrand, by kernel reduction on rational coefficient lists. -/
noncomputable section
namespace QSym.Distribution.StepSource
open MeasureTheory Set

/-- Derivative of a coefficient list in Horner form. -/
def polyDerivative : List ℚ → List ℚ
  | [] => []
  | _ :: p => polyAdd p (0 :: polyDerivative p)

/-- The derivative of the first list is the second, up to trailing zeros. -/
def isPrimitive (P p : List ℚ) : Bool :=
  polyZero (polyAdd (polyDerivative P) (polyScale (-1) p))

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

theorem isPrimitive_deriv {P p : List ℚ} (h : isPrimitive P p = true) (x : ℝ) :
    HasDerivAt (polyEval P) (polyEval p x) x := by
  have hz := polyEval_zero h x
  rw [polyEval_add, polyEval_scale] at hz
  have he : polyEval (polyDerivative P) x = polyEval p x := by
    push_cast at hz; linarith
  exact he ▸ polyEval_hasDerivAt P x

theorem isPrimitive_integral {P p : List ℚ} (h : isPrimitive P p = true) (l u : ℝ) :
    ∫ x in l..u, polyEval p x = polyEval P u - polyEval P l :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => isPrimitive_deriv h x)
    ((polyEval_continuous p).intervalIntegrable _ _)

/-- A frontend comparison, strict or not. -/
def compare : Bool → Option ℝ → Option ℝ → Option Bool
  | true => Value.lt
  | false => Value.le

/-- One lower and one upper bound of the axis, in either order. -/
def intervalGuard (swap strictLower strictUpper : Bool) (a b : Option ℝ) (x : ℝ) : Option Bool :=
  match swap with
  | false => Value.and (compare strictLower a (some x)) (compare strictUpper (some x) b)
  | true => Value.and (compare strictUpper (some x) b) (compare strictLower a (some x))

/-- A polynomial scaled by a partial constant. -/
structure ScaledPolynomial (v : ℝ → Option ℝ) (c : Option ℝ) (p : List ℚ) : Prop where
  equation : ∀ x, v x = Value.mul c (some (polyEval p x))

theorem scaled_constant (c : Option ℝ) : ScaledPolynomial (fun _ => c) c [1] :=
  ⟨fun x => by cases c <;> simp [Value.mul, polyEval]⟩

theorem scaled_left (c : Option ℝ) {w : ℝ → Option ℝ} {p : List ℚ}
    (hw : PolynomialOn (fun _ => True) w p) :
    ScaledPolynomial (fun x => Value.mul c (w x)) c p :=
  ⟨fun x => by rw [hw.equation x trivial]⟩

theorem scaled_right (c : Option ℝ) {w : ℝ → Option ℝ} {p : List ℚ}
    (hw : PolynomialOn (fun _ => True) w p) :
    ScaledPolynomial (fun x => Value.mul (w x) c) c p :=
  ⟨fun x => by rw [hw.equation x trivial]; cases c <;> simp [Value.mul, mul_comm]⟩

theorem scaled_times {v w : ℝ → Option ℝ} {c : Option ℝ} {p q : List ℚ}
    (hv : ScaledPolynomial v c p) (hw : PolynomialOn (fun _ => True) w q) :
    ScaledPolynomial (fun x => Value.mul (v x) (w x)) c (polyMul p q) :=
  ⟨fun x => by
    rw [hv.equation x, hw.equation x trivial]
    cases c <;> simp [Value.mul, polyEval_mul, mul_assoc]⟩

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
theorem mask_mask (p q : Option Bool) (v : Option ℝ) :
    Value.mask p (Value.mask q v) = Value.mask (Value.and p q) v := by
  rcases p with _ | _ | _ <;> rfl

/-- The density of a program is a mask of the guard. -/
structure Masked (f : ℝ → Option ℝ) (g : ℝ → Option Bool) (v : ℝ → Option ℝ) : Prop where
  equation : ∀ x, f x = Value.mask (g x) (v x)

theorem masked_first {w : ℝ → Option ℝ} {g : ℝ → Option Bool} {v : ℝ → Option ℝ}
    (h : ∀ x, w x = Value.mask (g x) (v x)) :
    Masked (DensityProgram.density (.weight w .lebesgue)) g v :=
  ⟨fun x => by simp only [DensityProgram.density, Value.mul_one_left, h x]⟩

/-- A total polynomial factor moves below the mask. -/
theorem masked_times {f w : ℝ → Option ℝ} {g : ℝ → Option Bool} {v : ℝ → Option ℝ}
    {q : List ℚ} (hf : Masked f g v) (hw : PolynomialOn (fun _ => True) w q) :
    Masked (fun x => Value.mul (f x) (w x)) g (fun x => Value.mul (v x) (w x)) :=
  ⟨fun x => by
    rw [hf.equation x, hw.equation x trivial]
    rcases g x with _ | _ | _ <;> simp [Value.mask, Value.mul]⟩

/-- The value below the mask and its integral between the bounds. Each
antiderivative is evaluated at the partial bounds themselves, so the result
contains no application. The last operand of the difference is the literal
minus one of the frontend. -/
inductive IntervalTerms (a b m : Option ℝ) : (ℝ → Option ℝ) → Option ℝ → Prop
  | pure {v : ℝ → Option ℝ} {G : Option ℝ → Option ℝ} {p P : List ℚ}
      (hv : PolynomialOn (fun _ => True) v p)
      (hG : PolynomialOn (fun _ => True) (fun t => G (some t)) P) (hd : isPrimitive P p = true) :
      IntervalTerms a b m v (Value.add (G b) (Value.mul m (G a)))
  | scaled {v : ℝ → Option ℝ} {G : Option ℝ → Option ℝ} {c : Option ℝ} {p P : List ℚ}
      (hv : ScaledPolynomial v c p)
      (hG : PolynomialOn (fun _ => True) (fun t => G (some t)) P) (hd : isPrimitive P p = true) :
      IntervalTerms a b m v (Value.mul c (Value.add (G b) (Value.mul m (G a))))
  | add {v w : ℝ → Option ℝ} {s t : Option ℝ} :
      IntervalTerms a b m v s → IntervalTerms a b m w t →
      IntervalTerms a b m (fun x => Value.add (v x) (w x)) (Value.add s t)

private theorem difference {G : Option ℝ → Option ℝ} {P p : List ℚ}
    (hG : PolynomialOn (fun _ => True) (fun t => G (some t)) P) (hd : isPrimitive P p = true)
    (l u : ℝ) :
    Value.add (G (some u)) (Value.mul (some (-1)) (G (some l))) =
      some (∫ x in l..u, polyEval p x) := by
  rw [isPrimitive_integral hd, hG.equation u trivial, hG.equation l trivial]
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
  | pure hv hG hd =>
    exact Or.inl ⟨_, polyEval_continuous _, fun x => hv.equation x trivial, difference hG hd l u⟩
  | @scaled v G c p P hv hG hd =>
    cases c with
    | none => exact Or.inr ⟨fun x => by rw [hv.equation x]; rfl, rfl⟩
    | some c =>
      refine Or.inl ⟨fun x => c * polyEval p x, continuous_const.mul (polyEval_continuous p),
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

end QSym.Distribution.StepSource

namespace QSym.Distribution.DensityProgram

theorem presentation_mass_interval (p : DensityProgram) (swap sl su : Bool) (a b m : Option ℝ)
    {v : ℝ → Option ℝ} {out : Option ℝ} (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hf : StepSource.Masked p.density (StepSource.intervalGuard swap sl su a b) v)
    (ht : StepSource.IntervalTerms a b m v out) :
    massValue p.presentation = Value.mask (StepSource.compare (sl || su) a b) out := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.interval_integral swap sl su a b m hm hf ht

end QSym.Distribution.DensityProgram
