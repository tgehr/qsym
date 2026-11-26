import QSym.Binding
import QSym.DistributionAtomicObservation
import QSym.Summation

/-! Scalar observations of recursive distributions. The recursive value is a
partial presentation. Its mass is computed after taking the fixed point. -/
noncomputable section
namespace QSym.Distribution

/-- Weighting and binding compose even if a weight or kernel is absent. -/
private theorem observe_scale {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (r : Option ℝ) (d : Option (D α)) : o (scaleValue r d) = Value.mul r (o d) := by
  cases h with
  | absent h => rw [h, h]; cases r <;> rfl
  | linear h => exact h.scale _ _

theorem observe_scale_steps {α : Type} {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (g : ℕ → Option (D α)) (base : Option (D α)) (r : ℝ)
    (h0 : g 0 = base) (hs : ∀ n, g (n+1) = scaleValue (some r) (g n)) (n : ℕ) :
    o (g n) = Value.mul (some (r ^ n)) (o base) := by
  induction n with
  | zero => rw [h0, pow_zero]; cases o base <;> simp [Value.mul]
  | succ n ih =>
    rw [hs, observe_scale h, ih, pow_succ']
    cases o base <;> simp [Value.mul, mul_assoc]

theorem mass_scale_steps {α : Type} (g : ℕ → Option (D α)) (base : Option (D α)) (r : ℝ)
    (h0 : g 0 = base) (hs : ∀ n, g (n+1) = scaleValue (some r) (g n)) (n : ℕ) :
    massValue (g n) = Value.mul (some (r ^ n)) (massValue base) :=
  observe_scale_steps .mass g base r h0 hs n

private theorem countdown_equations {α : Type} (p : Recursion.Program ℕ (D α) (D α))
    (base : Option (D α)) (next : Option (D α) → Option (D α))
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (next ((Functions.subN.apply (some n) (some 1)).bind g))) :
    let g := FixedPoint.value p.functional
    g 0 = base ∧ ∀ n, g (n+1) = next (g n) := by
  let g := FixedPoint.value p.functional
  have hu (n : ℕ) := (p.unfold n).symm.trans (step g n)
  constructor
  · simpa [g, Binding.conditionalValue, Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not] using hu 0
  · intro n
    simpa [g, Binding.conditionalValue, Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not,
      Functions.subN, Function2.apply, Nat.succ_eq_add_one] using hu (n+1)

/-- The source-level countdown with a possibly missing argument. The scale is
total. The seed is allowed to be partial and may depend on the outer environment. -/
theorem observe_scale_countdown {α : Type} {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (p : Recursion.Program ℕ (D α) (D α))
    {fn : Option (ℕ → Option (D α))} (hf : fn = some (FixedPoint.value p.functional))
    (base : Option (D α)) (r : Option ℝ) {c : ℝ} (hr : r = some c)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) :
    o (fn.bind (fun g => arg.bind g)) = Value.mul (Functions.powRN.apply r arg) (o base) := by
  subst fn r
  let g := FixedPoint.value p.functional
  obtain ⟨h0, hs⟩ := countdown_equations p base (scaleValue (some c)) step
  cases arg with
  | none => exact h.missing
  | some n => simpa [Functions.powRN, Function2.apply, g] using observe_scale_steps h g base c h0 hs n

/-- A captured scale may be undefined. The zero branch returns the seed
without inspecting the scale, and a missing index still invalidates the call. -/
theorem observe_partial_scale_countdown {α : Type} {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (p : Recursion.Program ℕ (D α) (D α)) {fn : Option (ℕ → Option (D α))}
    (hf : fn = some (FixedPoint.value p.functional)) (base : Option (D α)) (r : Option ℝ)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) :
    o (fn.bind (fun g => arg.bind g)) = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg))) (o base)
      (Value.mul (Functions.powRN.apply r arg) (o base)) := by
  subst fn
  obtain ⟨h0, hs⟩ := countdown_equations p base (scaleValue r) step
  cases arg with
  | none => exact h.missing
  | some n =>
    cases n with
    | zero =>
      simpa [Binding.conditionalValue, Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not] using congrArg o h0
    | succ n =>
      simp only [Option.bind_some, Option.some_bind]
      have cond : Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some (n+1)))) = some false := by
        simp [Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not]
        omega
      rw [cond]
      change o (FixedPoint.value p.functional (n+1)) = Value.mul (Functions.powRN.apply r (some (n+1))) (o base)
      cases r with
      | none => rw [hs]; exact h.missing
      | some c =>
        simpa [Functions.powRN, Function2.apply] using observe_scale_steps h _ base c h0 hs (n+1)

private theorem observedAdd {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (swap : Bool) (e d : Option (D α)) :
    o (if swap then addValue d e else addValue e d) = Value.add (o e) (o d) := by
  cases h with
  | absent h => rw [h, h]; rfl
  | linear h =>
    cases swap <;> simp only [Bool.false_eq_true, if_false, if_true, h.add]
    cases o e <;> cases o d <;> simp [Value.add, add_comm]

private theorem observedEmission {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (swap : Bool) (e : Option (D α)) (r : Option ℝ) (d : Option (D α)) :
    o (if swap then addValue (scaleValue r d) e else addValue e (scaleValue r d)) =
      Value.add (o e) (Value.mul r (o d)) :=
  (observedAdd h swap e _).trans (congrArg (Value.add (o e)) (observe_scale h r d))

private theorem emission_steps (y : ℕ → Option ℝ) (b e : Option ℝ) (r : ℝ)
    (h0 : y 0 = b) (hs : ∀ n, y (n+1) = Value.add e (Value.mul (some r) (y n))) (n : ℕ) :
    y (n+1) = Value.add (Value.mul (some (r^(n+1))) b)
      (Value.mul (some (∑ i ∈ Finset.range (n+1), r^i)) e) := by
  have geom (k : ℕ) : ∑ i ∈ Finset.range (k+1), r^i = 1+r*(∑ i ∈ Finset.range k, r^i) := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp [pow_succ', add_comm]
  induction n with
  | zero => rw [hs, h0]; cases b <;> cases e <;> simp [Value.add, Value.mul, add_comm]
  | succ n ih =>
    rw [hs, ih, geom (n+1), pow_succ' r (n+1)]
    cases b <;> cases e <;> simp [Value.add, Value.mul] <;> ring

/-- Each positive recursive step emits a fixed contribution and scales the
tail. A partial test of that contribution is first forced at a positive index. -/
theorem observe_emitting_countdown {α : Type} {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (p : Recursion.Program ℕ (D α) (D α)) {fn : Option (ℕ → Option (D α))}
    (hf : fn = some (FixedPoint.value p.functional)) (b e : Option (D α)) (r : Option ℝ) (swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let d := scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)
       if swap then addValue d e else addValue e d))
    (arg : Option ℕ) :
    o (fn.bind (fun g => arg.bind g)) = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg))) (o b)
      (Value.add (Value.mul (Functions.powRN.apply r arg) (o b)) (Value.mul
        (Summation.rangeValue (some (fun i => Functions.powRN.apply r (some i))) arg) (o e))) := by
  subst fn
  let g := FixedPoint.value p.functional
  obtain ⟨h0, hs⟩ := countdown_equations p b
    (fun d => if swap then addValue (scaleValue r d) e else addValue e (scaleValue r d)) step
  have rec (n : ℕ) : o (g (n+1)) = Value.add (o e) (Value.mul r (o (g n))) :=
    (congrArg o (hs n)).trans (observedEmission h swap e r (g n))
  cases arg with
  | none => exact h.missing
  | some n =>
    cases n with
    | zero =>
      simpa [Binding.conditionalValue, Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not] using congrArg o h0
    | succ n =>
      have cond : Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some (n+1)))) = some false := by
        simp [Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not]
        omega
      rw [cond]
      cases r with
      | none =>
        change o (g (n+1)) = _
        rw [rec n]
        cases o e <;> rfl
      | some r =>
        simpa [Binding.conditionalValue, g, Functions.powRN, Function2.apply, Summation.rangeValue, Summation.finite] using
          emission_steps (fun n => o (g n)) (o b) (o e) r (congrArg o h0) rec n

/-- Collect the common geometric power when the scale is a rational other
than one. At a positive index both scalar observations are required. -/
theorem geometric_emission (q : ℚ) (hq : q ≠ 1) {r gain minus : Option ℝ} (hr : r = some (q:ℝ))
    (hg : gain = some (((1-q)⁻¹ : ℚ):ℝ)) (hm : minus = some ((-1:ℚ):ℝ))
    (base visit : Option ℝ) (arg : Option ℕ) :
    Binding.conditionalValue (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg))) base
      (Value.add (Value.mul (Functions.powRN.apply r arg) base)
        (Value.mul (Summation.rangeValue (some (fun i => Functions.powRN.apply r (some i))) arg) visit)) =
    Binding.conditionalValue (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg))) base
      (let limit := Value.mul gain visit
       Value.add limit (Value.mul (Functions.powRN.apply r arg) (Value.add base (Value.mul minus limit)))) := by
  subst r; subst gain; subst minus
  have neq : (q:ℝ) ≠ 1 := by exact_mod_cast hq
  cases arg with
  | none => rfl
  | some n =>
    apply congrArg (Binding.conditionalValue _ base)
    cases base <;> cases visit <;>
      simp [Functions.powRN, Function2.apply, Summation.rangeValue, Summation.finite, Value.add, Value.mul,
        geom_sum_eq neq]
    field_simp [sub_ne_zero.mpr neq, sub_ne_zero.mpr neq.symm]
    <;> ring

/-- With a bare recursive call or a unit-scale call the accumulated weight
is the number of steps. A missing emission is harmless at depth zero. -/
theorem observe_unit_countdown {α : Type} {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (p : Recursion.Program ℕ (D α) (D α)) {fn : Option (ℕ → Option (D α))}
    (hf : fn = some (FixedPoint.value p.functional)) (b e : Option (D α)) (r : Option ℝ)
    (hr : r = some 1) (scaled swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let tail := (Functions.subN.apply (some n) (some 1)).bind g
       let d := if scaled then scaleValue r tail else tail
       if swap then addValue d e else addValue e d))
    (arg : Option ℕ) :
    o (fn.bind (fun g => arg.bind g)) = Value.add (o b) (Value.mask (Functions.nonzeroN.apply arg)
      (Value.mul (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply arg))) (o e))) := by
  subst fn r
  let g := FixedPoint.value p.functional
  obtain ⟨h0, hs⟩ := countdown_equations p b (fun tail =>
    let d := if scaled then scaleValue (some 1) tail else tail
    if swap then addValue d e else addValue e d) step
  have unit (d : Option (D α)) : o (if scaled then scaleValue (some 1) d else d) = o d := by
    cases scaled <;> simp [observe_scale h, Value.mul_one_left]
  have rec (n : ℕ) : o (g (n+1)) = Value.add (o e) (Value.mul (some 1) (o (g n))) :=
    ((congrArg o (hs n)).trans (observedAdd h swap e _)).trans
      (congrArg (Value.add (o e)) ((unit _).trans (Value.mul_one_left _).symm))
  cases arg with
  | none =>
    change o none = Value.add (o b) none
    rw [h.missing]
    cases o b <;> rfl
  | some n =>
    cases n with
    | zero =>
      simpa [Function1.apply, Functions.nonzeroN, Value.mask, Value.add_zero_right] using congrArg o h0
    | succ n =>
      simpa [g, Functions.castNZ, Functions.castZQ, Functions.castQR, Function1.apply, Functions.nonzeroN,
        Value.mask, Value.mul_one_left] using emission_steps (fun k => o (g k)) (o b) (o e) 1 (congrArg o h0) rec n

theorem mass_scale_countdown {α : Type} (p : Recursion.Program ℕ (D α) (D α))
    {fn : Option (ℕ → Option (D α))} (hf : fn = some (FixedPoint.value p.functional))
    (base : Option (D α)) (r : Option ℝ) {c : ℝ} (hr : r = some c)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) :
    massValue (fn.bind (fun g => arg.bind g)) = Value.mul (Functions.powRN.apply r arg) (massValue base) :=
  observe_scale_countdown .mass p hf base r hr step arg

end QSym.Distribution
