import QSym.Binding
import QSym.DistributionAtomicObservation

/-! Scalar observations of recursive distributions. The recursive value is a
partial presentation. Its mass is computed after taking the fixed point. -/
noncomputable section
namespace QSym.Distribution

/-- Weighting and binding compose even if a weight or kernel is absent. -/
private theorem observe_scale {o : Option (D α) → Option ℝ} (h : Atomic.Observation o)
    (r : ℝ) (d : Option (D α)) : o (scaleValue (some r) d) = Value.mul (some r) (o d) := by
  cases h with
  | absent h => rw [h, h]; rfl
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
  have hu (n : ℕ) := (p.unfold n).symm.trans (step g n)
  have h0 : g 0 = base := by
    simpa [g, Binding.conditionalValue, Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not] using hu 0
  have hs (n : ℕ) : g (n+1) = scaleValue (some c) (g n) := by
    simpa [g, Binding.conditionalValue, Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not,
      Functions.subN, Function2.apply, Nat.succ_eq_add_one] using hu (n+1)
  cases arg with
  | none => exact h.missing
  | some n => simpa [Functions.powRN, Function2.apply, g] using observe_scale_steps h g base c h0 hs n

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
