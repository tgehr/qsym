import QSym.Binding
import QSym.DistributionAtomicObservation
import QSym.DistributionFibreCertificate
import QSym.SummationElementary

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
    (base : Option (D α)) (next : ℕ → Option (D α) → Option (D α))
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (next n ((Functions.subN.apply (some n) (some 1)).bind g))) :
    let g := FixedPoint.value p.functional
    g 0 = base ∧ ∀ n, g (n+1) = next (n+1) (g n) := by
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
  obtain ⟨h0, hs⟩ := countdown_equations p base (fun _ => scaleValue (some c)) step
  cases arg with
  | none => exact h.missing
  | some n => simpa [Functions.powRN, Function2.apply, g] using observe_scale_steps h g base c h0 hs n

/-- A source-checked cumulative scale solves a countdown with an index-dependent
rate. The seed observation may be partial, even at a zero cumulative scale. -/
theorem observe_product_countdown {α : Type} {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (p : Recursion.Program ℕ (D α) (D α)) {fn : Option (ℕ → Option (D α))}
    (hf : fn = some (FixedPoint.value p.functional)) (base : Option (D α))
    (r w : Option ℕ → Option ℝ) (hw0 : w (some 0) = some 1)
    (hw : ∀ n, let next := Functions.addN.apply (some n) (some 1)
      Value.mul (r next) (w (some n)) = w next)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue (r (some n)) ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) :
    o (fn.bind (fun g => arg.bind g)) = Value.mul (arg.bind (fun n => w (some n))) (o base) := by
  subst fn
  let g := FixedPoint.value p.functional
  obtain ⟨h0, hs⟩ := countdown_equations p base (fun n => scaleValue (r (some n))) step
  have rec (n : ℕ) : o (g (n+1)) = Value.mul (r (some (n+1))) (o (g n)) :=
    (congrArg o (hs n)).trans (observe_scale h _ _)
  have solved (n : ℕ) : o (g n) = Value.mul (w (some n)) (o base) := by
    induction n with
    | zero => rw [hw0, Value.mul_one_left]; exact congrArg o h0
    | succ n ih =>
      have succ : Functions.addN.apply (some n) (some 1) = some (n+1) := by
        simp [Function2.apply, Functions.addN]
      have hstep : Value.mul (r (some (n+1))) (w (some n)) = w (some (n+1)) := by
        simpa only [succ] using hw n
      rw [rec, ih, ← hstep]
      cases r (some (n+1)) <;> cases w (some n) <;> cases o base <;> simp [Value.mul, mul_assoc]
  cases arg with
  | none => exact h.missing
  | some n => exact solved n

/-- A defined zero difference certifies the equality of both partial operands. -/
theorem product_step_of_zero (a b : Option ℝ) (m : Option ℝ) (hm : m = some ((-1 : ℚ) : ℝ))
    (hz : Value.add a (Value.mul m b) = some 0) : a = b := by
  subst m
  cases a <;> cases b <;> simp_all [Value.add, Value.mul, ← sub_eq_add_neg, sub_eq_zero]

theorem product_ratio_comm (a b : Option ℝ) :
    Value.mul (Value.inv b) a = Value.mul a (Value.inv b) := by
  cases a <;> cases Value.inv b <;> simp [Value.mul, mul_comm]

theorem product_ratio_cast (a b : Option ℚ) (swap : Bool) :
    Functions.castQR.apply (if swap then Functions.mulQ.apply (Functions.invQ.apply b) a
      else Functions.mulQ.apply a (Functions.invQ.apply b)) =
    Value.mul (Functions.castQR.apply a) (Value.inv (Functions.castQR.apply b)) := by
  cases b with
  | none => cases swap <;> cases a <;> simp [Functions.castQR, Functions.mulQ, Functions.invQ, Function1.apply, Function2.apply, Value.mul, Value.inv]
  | some b =>
    by_cases hb : b = 0
    · subst b; cases swap <;> cases a <;>
        simp [Functions.castQR, Functions.mulQ, Functions.invQ, Function1.apply, Function2.apply, Value.mul, Value.inv]
    · have h : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      cases swap <;> cases a <;>
        simp [Functions.castQR, Functions.mulQ, Functions.invQ, Function1.apply, Function2.apply, Value.mul, Value.inv, hb, h, mul_comm]

private theorem scale_product_eq (r c u v : Option ℝ) (scaled : Bool) (h : Value.mul r u = v) :
    Value.mul r (if scaled then Value.mul c u else u) = (if scaled then Value.mul c v else v) := by
  subst v
  cases scaled with
  | false => rfl
  | true => cases r <;> cases c <;> cases u <;> simp [Value.mul, mul_left_comm]

/-- Clear denominators after certifying their domain. The remaining successor
identity can be checked as a polynomial even when the source rate is rational. -/
theorem product_step_cross (a b u v r c m : Option ℝ) (inverse scaled : Bool)
    (hr : r = Value.mul a (Value.inv b)) (hm : m = some ((-1 : ℚ) : ℝ))
    (hd : Domain.Correct (Value.inv (if inverse then Value.mul b (Value.mul u v) else b)) (some true))
    (hx : Value.add (Value.mul a (if inverse then v else u))
      (Value.mul m (Value.mul b (if inverse then u else v))) = some 0) :
    Value.mul r (if scaled then Value.mul c (if inverse then Value.inv u else u)
        else if inverse then Value.inv u else u) =
      (if scaled then Value.mul c (if inverse then Value.inv v else v)
        else if inverse then Value.inv v else v) := by
  apply scale_product_eq
  subst r
  have eqv := product_step_of_zero _ _ _ hm hx
  obtain ⟨d, hd, hn⟩ := (Value.defined_inv _).mp (hd.iff.mpr rfl)
  cases inverse with
  | false =>
    change b = some d at hd
    subst b
    cases a <;> cases u <;> cases v <;> simp_all [Value.mul, Value.inv]
    rename_i a u v
    calc a * d⁻¹ * u = (a*u) * d⁻¹ := by ring
         _ = v := by rw [eqv]; field_simp
  | true =>
    rcases b with _ | b <;> rcases u with _ | u <;> rcases v with _ | v <;> simp [Value.mul] at hd
    have nonzero : b * (u * v) ≠ 0 := hd ▸ hn
    have nz : b ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 := by simpa [mul_ne_zero_iff] using nonzero
    rcases nz with ⟨hb,hu,hv⟩
    cases a with
    | none => simp [Value.mul] at eqv
    | some a =>
      simp [Value.mul] at eqv
      simp [Value.mul, Value.inv, hb, hu, hv]
      field_simp [hb,hu,hv]
      linear_combination eqv

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
  obtain ⟨h0, hs⟩ := countdown_equations p base (fun _ => scaleValue r) step
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
    (fun _ d => if swap then addValue (scaleValue r d) e else addValue e (scaleValue r d)) step
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

private theorem observe_unit_tail {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (scaled : Bool) (d : Option (D α)) : o (if scaled then scaleValue (some 1) d else d) = o d := by
  cases scaled <;> simp [observe_scale h, Value.mul_one_left]

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
  obtain ⟨h0, hs⟩ := countdown_equations p b (fun _ tail =>
    let d := if scaled then scaleValue (some 1) tail else tail
    if swap then addValue d e else addValue e d) step
  have rec (n : ℕ) : o (g (n+1)) = Value.add (o e) (Value.mul (some 1) (o (g n))) :=
    ((congrArg o (hs n)).trans (observedAdd h swap e _)).trans
      (congrArg (Value.add (o e)) ((observe_unit_tail h scaled _).trans (Value.mul_one_left _).symm))
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

/-- The emission may depend on the current index. A finite sum visits
exactly indices 1 through the argument, even for a partial observation. -/
theorem observe_indexed_countdown {α : Type} {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (p : Recursion.Program ℕ (D α) (D α)) {fn : Option (ℕ → Option (D α))}
    (hf : fn = some (FixedPoint.value p.functional)) (b : Option (D α)) (e : Option ℕ → Option (D α))
    (r : Option ℝ) (hr : r = some 1) (scaled swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let tail := (Functions.subN.apply (some n) (some 1)).bind g
       let d := if scaled then scaleValue r tail else tail
       if swap then addValue d (e (some n)) else addValue (e (some n)) d))
    (arg : Option ℕ) :
    o (fn.bind (fun g => arg.bind g)) = Value.add (o b)
      (Summation.rangeValue (some (fun i => o (e (Functions.addN.apply (some i) (some 1))))) arg) := by
  subst fn r
  let g := FixedPoint.value p.functional
  let visit (i : ℕ) := o (e (some (i+1)))
  obtain ⟨h0, hs⟩ := countdown_equations p b (fun n tail =>
    let d := if scaled then scaleValue (some 1) tail else tail
    if swap then addValue d (e (some n)) else addValue (e (some n)) d) step
  have rec (n : ℕ) : o (g (n+1)) = Value.add (visit n) (o (g n)) :=
    ((congrArg o (hs n)).trans (observedAdd h swap _ _)).trans
      (congrArg (Value.add (visit n)) (observe_unit_tail h scaled _))
  have total (n : ℕ) : o (g n) = Value.add (o b) (Summation.finite (Finset.range n) visit) := by
    induction n with
    | zero => simpa [Summation.finite_empty, Value.add_zero_right] using congrArg o h0
    | succ n ih =>
      rw [rec, ih, Summation.range_succ]
      cases o b <;> cases Summation.finite (Finset.range n) visit <;> cases visit n <;>
        simp [Value.add, add_comm, add_left_comm, add_assoc]
  cases arg with
  | none =>
    change o none = Value.add (o b) none
    rw [h.missing]
    cases o b <;> rfl
  | some n =>
    simpa [visit, g, Summation.rangeValue, Function2.apply, Functions.addN] using total n

/-- Factor a nonzero rational scale out of an indexed countdown. Each
visited row is tested, including rows with zero observed mass. -/
theorem observe_discounted_countdown {α : Type} {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (p : Recursion.Program ℕ (D α) (D α)) {fn : Option (ℕ → Option (D α))}
    (hf : fn = some (FixedPoint.value p.functional)) (b : Option (D α)) (e : Option ℕ → Option (D α))
    (q inv : ℚ) (reciprocal : q * inv = 1) (r s : Option ℝ) (hr : r = some (q : ℝ))
    (hi : s = some (inv : ℝ)) (swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let d := scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)
       if swap then addValue d (e (some n)) else addValue (e (some n)) d))
    (arg : Option ℕ) :
    o (fn.bind (fun g => arg.bind g)) = Value.mul (Functions.powRN.apply r arg)
      (Value.add (o b) (Summation.rangeValue (some (fun i =>
        let k := Functions.addN.apply (some i) (some 1)
        Value.mul (Functions.powRN.apply s k) (o (e k)))) arg)) := by
  subst fn r s
  let g := FixedPoint.value p.functional
  let visit (i : ℕ) := Value.mul (some ((inv : ℝ)^(i+1))) (o (e (some (i+1))))
  obtain ⟨h0, hs⟩ := countdown_equations p b (fun n tail =>
    let d := scaleValue (some (q : ℝ)) tail
    if swap then addValue d (e (some n)) else addValue (e (some n)) d) step
  have rec (n : ℕ) : o (g (n+1)) = Value.add (o (e (some (n+1)))) (Value.mul (some (q : ℝ)) (o (g n))) :=
    (congrArg o (hs n)).trans (observedEmission h swap _ _ _)
  have cancel (n : ℕ) : (q : ℝ)^(n+1) * (inv : ℝ)^(n+1) = 1 := by
    have hc : (q : ℝ) * (inv : ℝ) = 1 := by exact_mod_cast reciprocal
    rw [← mul_pow, hc, one_pow]
  have update (n : ℕ) (b a v : ℝ) :
      v + q * ((q : ℝ)^n * (b+a)) = (q : ℝ)^(n+1) * (b + (a + (inv : ℝ)^(n+1) * v)) := by
    calc
      _ = (q : ℝ)^(n+1) * (b+a) + 1*v := by rw [pow_succ']; ring
      _ = _ := by rw [← cancel n]; ring
  have total (n : ℕ) : o (g n) = Value.mul (some ((q : ℝ)^n))
      (Value.add (o b) (Summation.finite (Finset.range n) visit)) := by
    induction n with
    | zero => simpa [Summation.finite_empty, Value.add_zero_right, Value.mul_one_left] using congrArg o h0
    | succ n ih =>
      rw [rec, ih, Summation.range_succ]
      cases o b <;> cases Summation.finite (Finset.range n) visit <;> dsimp only [visit] <;>
        cases o (e (some (n+1))) <;> simp [Value.add, Value.mul, update]
  cases arg with
  | none => exact h.missing
  | some n =>
    simpa [visit, g, Summation.rangeValue, Function2.apply, Functions.addN, Functions.powRN] using total n

private theorem product_emission_step (r u v b s z : Option ℝ) (hs : Value.mul r u = v)
    (hd : Domain.Correct (Value.inv v) (some true)) :
    Value.add z (Value.mul r (Value.mul u (Value.add b s))) =
      Value.mul v (Value.add b (s.bind fun a => (Value.mul (Value.inv v) z).map (fun x => a + x))) := by
  obtain ⟨w, hw, hn⟩ := (Value.defined_inv _).mp (hd.iff.mpr rfl)
  rw [hw] at hs ⊢
  cases r with
  | none => cases hs
  | some r =>
    cases u with
    | none => cases hs
    | some u =>
      have eq : r*u = w := Option.some.inj hs
      cases b <;> cases s <;> cases z <;> simp [Value.add, Value.mul, Value.inv, hn]
      rw [← mul_assoc, eq]
      field_simp
      ring

/-- The cumulative scale of a countdown can serve as an integrating factor.
The sum inspects each emitted observation exactly on the positive visited indices.
Its reciprocal is used only with a source proof of nonvanishing there. -/
theorem observe_product_emitting_countdown {α : Type} {o : Option (D α) → Option ℝ}
    (h : Atomic.Observation o) (p : Recursion.Program ℕ (D α) (D α))
    {fn : Option (ℕ → Option (D α))} (hf : fn = some (FixedPoint.value p.functional))
    (b : Option (D α)) (e : Option ℕ → Option (D α)) (r w : Option ℕ → Option ℝ)
    (hw0 : w (some 0) = some 1)
    (hw : ∀ n, let next := Functions.addN.apply (some n) (some 1)
      Value.mul (r next) (w (some n)) = w next)
    (hi : ∀ n, Domain.Correct (Value.inv (w (Functions.addN.apply (some n) (some 1)))) (some true))
    (swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let tail := scaleValue (r (some n)) ((Functions.subN.apply (some n) (some 1)).bind g)
       if swap then addValue tail (e (some n)) else addValue (e (some n)) tail))
    (arg : Option ℕ) :
    o (fn.bind (fun g => arg.bind g)) = Value.mul (arg.bind (fun n => w (some n)))
      (Value.add (o b) (Summation.rangeValue (some (fun i =>
        let next := Functions.addN.apply (some i) (some 1)
        Value.mul (Value.inv (w next)) (o (e next)))) arg)) := by
  subst fn
  let g := FixedPoint.value p.functional
  let visit (i : ℕ) := Value.mul (Value.inv (w (some (i+1)))) (o (e (some (i+1))))
  obtain ⟨h0, hs⟩ := countdown_equations p b (fun n tail =>
    let d := scaleValue (r (some n)) tail
    if swap then addValue d (e (some n)) else addValue (e (some n)) d) step
  have rec (n : ℕ) : o (g (n+1)) = Value.add (o (e (some (n+1)))) (Value.mul (r (some (n+1))) (o (g n))) :=
    (congrArg o (hs n)).trans (observedEmission h swap _ _ _)
  have total (n : ℕ) : o (g n) = Value.mul (w (some n))
      (Value.add (o b) (Summation.finite (Finset.range n) visit)) := by
    induction n with
    | zero => simpa [hw0, Summation.finite_empty, Value.add_zero_right, Value.mul_one_left] using congrArg o h0
    | succ n ih =>
      rw [rec, ih, Summation.range_succ]
      have succ : Functions.addN.apply (some n) (some 1) = some (n+1) := by
        simp [Function2.apply, Functions.addN]
      apply product_emission_step
      · simpa only [succ] using hw n
      · simpa only [succ] using hi n
  cases arg with
  | none => exact h.missing
  | some n => simpa [visit, Summation.rangeValue, Function2.apply, Functions.addN] using total n

private theorem indexed_steps (r : ℝ) (b : Option ℝ) (visit y : ℕ → Option ℝ)
    (h0 : y 0 = b) (hs : ∀ n, y (n+1) = Value.add (visit (n+1)) (Value.mul (some r) (y n))) (n : ℕ) :
    y n = Value.add (Value.mul (some (r^n)) b) (Summation.finite (Finset.range n)
      (fun i => Value.mul (some (r^(n-(i+1)))) (visit (i+1)))) := by
  let row (k i : ℕ) := Value.mul (some (r^(k-(i+1)))) (visit (i+1))
  have scaledPrefix (k : ℕ) : Summation.finite (Finset.range k) (row (k+1)) =
      Value.mul (some r) (Summation.finite (Finset.range k) (row k)) := by
    refine (Summation.finite_congr _ ?_).trans (SummationElementary.finite_scale r (row k) k)
    intro i hi
    have le : i+1 ≤ k := Finset.mem_range.mp hi
    have ex : (k+1)-(i+1) = (k-(i+1))+1 := by omega
    simp only [row, ex, pow_succ']
    cases visit (i+1) <;> simp [Value.mul, mul_assoc]
  have last (k : ℕ) : row (k+1) k = visit (k+1) := by simp [row, Value.mul_one_left]
  change y n = Value.add (Value.mul (some (r^n)) b) (Summation.finite _ (row n))
  induction n with
  | zero => simpa [Summation.finite_empty, Value.mul_one_left, Value.add_zero_right] using h0
  | succ n ih =>
    rw [hs, ih, Summation.range_succ, scaledPrefix, last]
    cases b <;> cases Summation.finite (Finset.range n) (row n) <;> cases visit (n+1) <;>
      simp [Value.add, Value.mul, pow_succ'] <;> ring

/-- The finite convolution uses only nonnegative powers on visited indices.
The zero branch does not evaluate the scale or the emission. -/
theorem observe_convolution_countdown {α : Type} {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (p : Recursion.Program ℕ (D α) (D α)) {fn : Option (ℕ → Option (D α))}
    (hf : fn = some (FixedPoint.value p.functional)) (b : Option (D α)) (e : Option ℕ → Option (D α))
    (r : Option ℝ) (swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let d := scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)
       if swap then addValue d (e (some n)) else addValue (e (some n)) d))
    (arg : Option ℕ) :
    o (fn.bind (fun g => arg.bind g)) = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg))) (o b)
      (Value.add (Value.mul (Functions.powRN.apply r arg) (o b))
        (Summation.rangeValue (some (fun i =>
          let k := Functions.addN.apply (some i) (some 1)
          Value.mul (Functions.powRN.apply r (Functions.subN.apply arg k)) (o (e k)))) arg)) := by
  subst fn
  let g := FixedPoint.value p.functional
  obtain ⟨h0, hs⟩ := countdown_equations p b (fun n tail =>
    let d := scaleValue r tail
    if swap then addValue d (e (some n)) else addValue (e (some n)) d) step
  have rec (n : ℕ) : o (g (n+1)) = Value.add (o (e (some (n+1)))) (Value.mul r (o (g n))) :=
    (congrArg o (hs n)).trans (observedEmission h swap _ _ _)
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
        rw [rec]
        cases o (e (some (n+1))) <;> rfl
      | some r =>
        have rows (k : ℕ) : Summation.rangeValue (some (fun i =>
            let j := Functions.addN.apply (some i) (some 1)
            Value.mul (Functions.powRN.apply (some r) (Functions.subN.apply (some k) j)) (o (e j)))) (some k) =
            Summation.finite (Finset.range k) (fun i => Value.mul (some (r^(k-(i+1)))) (o (e (some (i+1))))) := by
          apply Summation.finite_congr
          intro i hi
          have le : i+1 ≤ k := Finset.mem_range.mp hi
          simp [Functions.addN, Functions.subN, Functions.powRN, Function2.apply, le]
        rw [rows]
        simpa [Binding.conditionalValue, g, Functions.powRN, Function2.apply] using
          indexed_steps r (o b) (fun k => o (e (some k))) (fun k => o (g k)) (congrArg o h0) rec (n+1)

theorem mass_scale_countdown {α : Type} (p : Recursion.Program ℕ (D α) (D α))
    {fn : Option (ℕ → Option (D α))} (hf : fn = some (FixedPoint.value p.functional))
    (base : Option (D α)) (r : Option ℝ) {c : ℝ} (hr : r = some c)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) :
    massValue (fn.bind (fun g => arg.bind g)) = Value.mul (Functions.powRN.apply r arg) (massValue base) :=
  observe_scale_countdown .mass p hf base r hr step arg

namespace RealDensityFibre

/-- Both observations are linear, including when signed atoms cancel.
Extract the pointwise density only after computing the two components. -/
def component (charge : Bool) (x : Option ℝ) (d : Option (D ℝ)) : Option ℝ := do
  let v ← d
  let y ← x
  let fibre := realFibre v y
  if charge then some fibre.charge else fibre.regular

theorem observation (c : Bool) (x : Option ℝ) : Atomic.Observation (component c x) := by
  cases x with
  | none => exact .absent fun d => by cases d <;> rfl
  | some x =>
    apply Atomic.Observation.linear
    refine ⟨rfl, ?_, ?_, ?_⟩
    · cases c <;> rfl
    · intro a b
      cases a <;> cases b <;> cases c <;> simp [component, addValue, realFibre, add, Value.add]
    · intro r d
      cases r <;> cases d <;> cases c <;> simp [component, scaleValue, realFibre, scale, Value.mul]

theorem component_scale (c : Bool) (x r : Option ℝ) (d : Option (D ℝ)) :
    component c x (scaleValue r d) = Value.mul r (component c x d) :=
  observe_scale (observation c x) r d

private theorem certificate (d : Option (D ℝ)) (x : Option ℝ) :
    FibreCertificate d x (component true x d) (component false x d) := by
  cases d <;> cases x <;> constructor <;> rfl

theorem density_congr {d e : Option (D ℝ)} {x : Option ℝ}
    (h : ∀ c, component c x d = component c x e) : densityAtValue d x = densityAtValue e x := by
  rw [(certificate d x).extract, (certificate e x).extract, h true, h false]

private theorem density_cases (p : Option Bool) {d a b : Option (D ℝ)} {x : Option ℝ}
    (h : ∀ c, component c x d = Binding.conditionalValue p (component c x a) (component c x b)) :
    densityAtValue d x = Binding.conditionalValue p (densityAtValue a x) (densityAtValue b x) := by
  rcases p with _ | p
  · exact density_congr (e := none) h
  · cases p <;> exact density_congr h

theorem scale_countdown (p : Recursion.Program ℕ (D ℝ) (D ℝ)) {fn : Option (ℕ → Option (D ℝ))}
    (hf : fn = some (FixedPoint.value p.functional)) (base : Option (D ℝ)) (r : Option ℝ)
    {v : ℝ} (hr : r = some v)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) (x : Option ℝ) :
    densityAtValue (fn.bind (fun g => arg.bind g)) x =
      densityAtValue (scaleValue (Functions.powRN.apply r arg) base) x := by
  apply density_congr
  intro c
  exact (observe_scale_countdown (observation c x) p hf base r hr step arg).trans
    (component_scale c x _ base).symm

theorem partial_scale_countdown (p : Recursion.Program ℕ (D ℝ) (D ℝ)) {fn : Option (ℕ → Option (D ℝ))}
    (hf : fn = some (FixedPoint.value p.functional)) (base : Option (D ℝ)) (r : Option ℝ)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) (x : Option ℝ) :
    densityAtValue (fn.bind (fun g => arg.bind g)) x =
      Binding.conditionalValue (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg)))
        (densityAtValue base x) (densityAtValue (scaleValue (Functions.powRN.apply r arg) base) x) := by
  apply density_cases
  intro c
  rw [component_scale]
  exact observe_partial_scale_countdown (observation c x) p hf base r step arg

/-- A nonzero scalar preserves the pointwise obstruction from a nonzero
atomic charge. A zero scalar requires the full fibre calculation. -/
theorem density_scale_nonzero (r : ℝ) (hr : r ≠ 0) (d : Option (D ℝ)) (x : Option ℝ) :
    densityAtValue (scaleValue (some r) d) x = Value.mul (some r) (densityAtValue d x) := by
  rcases d with _ | d
  · rfl
  rcases x with _ | x
  · rfl
  change (scale r (realFibre d x)).density = Value.mul (some r) (realFibre d x).density
  by_cases hc : (realFibre d x).charge = 0 <;> simp [scale, density, hc, hr, Value.mul]

theorem nonzero_scale_countdown (p : Recursion.Program ℕ (D ℝ) (D ℝ)) {fn : Option (ℕ → Option (D ℝ))}
    (hf : fn = some (FixedPoint.value p.functional)) (base : Option (D ℝ)) (r : Option ℝ)
    (q : ℚ) (hr : r = some (Numeric.denote (s := .real) q)) (hq : q ≠ 0)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) (x : Option ℝ) :
    densityAtValue (fn.bind (fun g => arg.bind g)) x =
      Value.mul (Functions.powRN.apply r arg) (densityAtValue base x) := by
  rw [scale_countdown p hf base r hr step arg x, hr]
  have h : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  cases arg with
  | none => rfl
  | some n =>
    simpa [Functions.powRN, Function2.apply, Numeric.denote] using
      density_scale_nonzero ((q : ℝ) ^ n) (pow_ne_zero n h) base x

/-- A candidate cumulative scale is certified at zero and at every successor of the source recurrence. -/
theorem product_countdown
    (p : Recursion.Program ℕ (D ℝ) (D ℝ)) {fn : Option (ℕ → Option (D ℝ))}
    (hf : fn = some (FixedPoint.value p.functional)) (base : Option (D ℝ))
    (r w : Option ℕ → Option ℝ) (hw0 : w (some 0) = some 1)
    (hw : ∀ n, let next := Functions.addN.apply (some n) (some 1)
      Value.mul (r next) (w (some n)) = w next)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue (r (some n)) ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) (x : Option ℝ) :
    densityAtValue (fn.bind (fun g => arg.bind g)) x =
      densityAtValue (scaleValue (arg.bind (fun n => w (some n))) base) x := by
  apply density_congr
  intro c
  exact (observe_product_countdown (observation c x) p hf base r w hw0 hw step arg).trans
    (component_scale c x _ base).symm

theorem component_add (c : Bool) (x : Option ℝ) (a b : Option (D ℝ)) :
    component c x (addValue a b) = Value.add (component c x a) (component c x b) :=
  observedAdd (observation c x) false a b

/-- Extract the density after adding the signed contribution of all positive visits. -/
theorem unit_countdown
    (p : Recursion.Program ℕ (D ℝ) (D ℝ)) {fn : Option (ℕ → Option (D ℝ))}
    (hf : fn = some (FixedPoint.value p.functional)) (b e : Option (D ℝ)) (r : Option ℝ)
    (hr : r = some 1) (scaled swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let tail := (Functions.subN.apply (some n) (some 1)).bind g
       let d := if scaled then scaleValue r tail else tail
       if swap then addValue d e else addValue e d))
    (arg : Option ℕ) (x : Option ℝ) :
    densityAtValue (fn.bind (fun g => arg.bind g)) x = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg))) (densityAtValue b x)
      (densityAtValue (addValue b (scaleValue
        (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply arg))) e)) x) := by
  apply density_cases
  intro c
  rw [observe_unit_countdown (observation c x) p hf b e r hr scaled swap step arg,
    component_add, component_scale]
  rcases arg with _ | n
  · cases component c x b <;> rfl
  · cases n with
    | zero =>
      simpa [Functions.castNZ, Function1.apply, Functions.nonzeroZ, Functions.nonzeroN,
        Value.not, Value.mask, Binding.conditionalValue] using Value.add_zero_right (component c x b)
    | succ n =>
      have hn : (n : ℤ) + 1 ≠ 0 := by omega
      simp [Functions.nonzeroZ, Functions.nonzeroN, Functions.castNZ, Function1.apply,
        Value.not, Value.mask, Binding.conditionalValue, hn]

theorem emitting_countdown
    (p : Recursion.Program ℕ (D ℝ) (D ℝ)) {fn : Option (ℕ → Option (D ℝ))}
    (hf : fn = some (FixedPoint.value p.functional)) (b e : Option (D ℝ)) (r : Option ℝ) (swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let d := scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)
       if swap then addValue d e else addValue e d))
    (arg : Option ℕ) (x : Option ℝ) :
    densityAtValue (fn.bind (fun g => arg.bind g)) x = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg))) (densityAtValue b x)
      (densityAtValue (addValue (scaleValue (Functions.powRN.apply r arg) b) (scaleValue
        (Summation.rangeValue (some (fun i => Functions.powRN.apply r (some i))) arg) e)) x) := by
  apply density_cases
  intro c
  rw [component_add, component_scale, component_scale]
  exact observe_emitting_countdown (observation c x) p hf b e r swap step arg

theorem centered_countdown
    (p : Recursion.Program ℕ (D ℝ) (D ℝ)) {fn : Option (ℕ → Option (D ℝ))}
    (hf : fn = some (FixedPoint.value p.functional)) (b e : Option (D ℝ))
    (q : ℚ) (hq : q ≠ 1) {r gain minus : Option ℝ} (hr : r = some (q : ℝ))
    (hg : gain = some (((1-q)⁻¹ : ℚ) : ℝ)) (hm : minus = some ((-1 : ℚ) : ℝ)) (swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let d := scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)
       if swap then addValue d e else addValue e d))
    (arg : Option ℕ) (x : Option ℝ) :
    densityAtValue (fn.bind (fun g => arg.bind g)) x = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg))) (densityAtValue b x)
      (let limit := scaleValue gain e
       densityAtValue (addValue limit (scaleValue (Functions.powRN.apply r arg)
         (addValue b (scaleValue minus limit)))) x) := by
  apply density_cases
  intro c
  simp only [component_add, component_scale]
  exact (observe_emitting_countdown (observation c x) p hf b e r swap step arg).trans
    (geometric_emission q hq hr hg hm (component c x b) (component c x e) arg)

/-- Each positive visit emits a source-dependent scalar multiple of the same
distribution. Sum the scalars before combining its fibre with the seed. -/
theorem factored_countdown
    (p : Recursion.Program ℕ (D ℝ) (D ℝ)) {fn : Option (ℕ → Option (D ℝ))}
    (hf : fn = some (FixedPoint.value p.functional)) (b e : Option (D ℝ))
    (w : Option ℕ → Option ℝ) (r : Option ℝ) (hr : r = some 1) (scaled swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let tail := (Functions.subN.apply (some n) (some 1)).bind g
       let d := if scaled then scaleValue r tail else tail
       let row := scaleValue (w (some n)) e
       if swap then addValue d row else addValue row d))
    (arg : Option ℕ) (x : Option ℝ) :
    densityAtValue (fn.bind (fun g => arg.bind g)) x = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply arg))) (densityAtValue b x)
      (densityAtValue (addValue b (scaleValue
        (Summation.rangeValue (some (fun i => w (Functions.addN.apply (some i) (some 1)))) arg) e)) x) := by
  apply density_cases
  intro c
  rw [observe_indexed_countdown (observation c x) p hf b (fun k => scaleValue (w k) e) r hr scaled swap step arg]
  simp only [component_scale, component_add]
  rw [SummationElementary.scale_rev Value.mul rfl (component c x e)
    (fun i => w (Functions.addN.apply (some i) (some 1))) arg]
  rcases arg with _ | n
  · cases component c x b <;> rfl
  · cases n with
    | zero =>
      simpa [Functions.castNZ, Function1.apply, Functions.nonzeroZ, Functions.nonzeroN,
        Value.not, Value.mask, Binding.conditionalValue] using Value.add_zero_right (component c x b)
    | succ n =>
      have hn : (n : ℤ) + 1 ≠ 0 := by omega
      simp [Functions.nonzeroZ, Functions.nonzeroN, Functions.castNZ, Function1.apply,
        Value.not, Value.mask, Binding.conditionalValue, hn, SummationElementary.mul_swap (component c x e)]

/-- Fold the charge and the regular part of each visited emission. A missing
row poisons the charge check only if that row is actually visited. -/
theorem indexed_countdown
    (p : Recursion.Program ℕ (D ℝ) (D ℝ)) {fn : Option (ℕ → Option (D ℝ))}
    (hf : fn = some (FixedPoint.value p.functional)) (b : Option (D ℝ)) (e : Option ℕ → Option (D ℝ))
    (r : Option ℝ) (hr : r = some 1) (scaled swap : Bool)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) b
      (let tail := (Functions.subN.apply (some n) (some 1)).bind g
       let d := if scaled then scaleValue r tail else tail
       if swap then addValue d (e (some n)) else addValue (e (some n)) d))
    (arg : Option ℕ) {x bc bw : Option ℝ} {charge regular : ℕ → Option ℝ}
    (hb : FibreCertificate b x bc bw)
    (rows : ∀ i, FibreCertificate (e (Functions.addN.apply (some i) (some 1))) x (charge i) (regular i)) :
    densityAtValue (fn.bind (fun g => arg.bind g)) x =
      Binding.guardValue (Value.not (Value.nonzero (Value.add bc (Summation.rangeValue (some charge) arg))))
        (Value.add bw (Summation.rangeValue (some regular) arg)) := by
  subst fn r
  let g := FixedPoint.value p.functional
  obtain ⟨h0, hs⟩ := countdown_equations p b (fun n tail =>
    let d := if scaled then scaleValue (some 1) tail else tail
    if swap then addValue d (e (some n)) else addValue (e (some n)) d) step
  have total (n : ℕ) : FibreCertificate (g n) x
      (Value.add bc (Summation.finite (Finset.range n) charge))
      (Value.add bw (Summation.finite (Finset.range n) regular)) := by
    induction n with
    | zero => simpa [g, h0, Summation.finite_empty, Value.add_zero_right] using hb
    | succ n ih =>
      have prior : FibreCertificate (if scaled then scaleValue (some 1) (g n) else g n) x
          (Value.add bc (Summation.finite (Finset.range n) charge))
          (Value.add bw (Summation.finite (Finset.range n) regular)) := by
        cases scaled
        · exact ih
        · simpa only [Value.mul_one_left] using FibreCertificate.scale (some 1) ih
      have row : FibreCertificate (e (some (n+1))) x (charge n) (regular n) := by
        simpa [Functions.addN, Function2.apply] using rows n
      rw [show g (n+1) = _ from hs n, Summation.range_succ, Summation.range_succ, ← Summation.add, ← Summation.add,
        Summation.add_assoc Value.add Summation.add, Summation.add_assoc Value.add Summation.add]
      cases swap
      · exact (Summation.add_comm Value.add Summation.add _ (charge n)) ▸
          (Summation.add_comm Value.add Summation.add _ (regular n)) ▸ FibreCertificate.add row prior
      · exact FibreCertificate.add prior row
  apply FibreCertificate.extract
  cases arg with
  | none => cases bc <;> rfl
  | some n => exact total n

end RealDensityFibre
end QSym.Distribution
