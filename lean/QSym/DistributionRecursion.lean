import QSym.Binding

/-! Scalar observations of recursive distributions. The recursive value is a
partial presentation. Its mass is computed after taking the fixed point. -/
noncomputable section
namespace QSym.Distribution

/-- Repeated scaling is geometric under the mass observer, including for
signed weights and distributions whose mass is undefined. -/
theorem mass_scale_steps {α : Type} (g : ℕ → Option (D α)) (base : Option (D α)) (r : ℝ)
    (h0 : g 0 = base) (hs : ∀ n, g (n+1) = scaleValue (some r) (g n)) (n : ℕ) :
    massValue (g n) = Value.mul (some (r ^ n)) (massValue base) := by
  induction n with
  | zero => rw [h0, pow_zero]; cases massValue base <;> simp [Value.mul]
  | succ n ih =>
    rw [hs, mass_scaleValue, ih, pow_succ']
    cases massValue base <;> simp [Value.mul, mul_assoc]

/-- The source-level countdown with a possibly missing argument. The scale is
total. The seed is allowed to be partial and may depend on the outer environment. -/
theorem mass_scale_countdown {α : Type} (p : Recursion.Program ℕ (D α) (D α))
    {fn : Option (ℕ → Option (D α))} (hf : fn = some (FixedPoint.value p.functional))
    (base : Option (D α)) (r : Option ℝ) {c : ℝ} (hr : r = some c)
    (step : ∀ g n, p.eval g n = Binding.conditionalValue
      (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) base
      (scaleValue r ((Functions.subN.apply (some n) (some 1)).bind g)))
    (arg : Option ℕ) :
    massValue (fn.bind (fun g => arg.bind g)) = Value.mul (Functions.powRN.apply r arg) (massValue base) := by
  subst fn r
  let g := FixedPoint.value p.functional
  have hu (n : ℕ) := (p.unfold n).symm.trans (step g n)
  have h0 : g 0 = base := by
    simpa [g, Binding.conditionalValue, Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not] using hu 0
  have hs (n : ℕ) : g (n+1) = scaleValue (some c) (g n) := by
    simpa [g, Binding.conditionalValue, Functions.castNZ, Functions.nonzeroZ, Function1.apply, Value.not,
      Functions.subN, Function2.apply, Nat.succ_eq_add_one] using hu (n+1)
  cases arg with
  | none => rfl
  | some n => simpa [Functions.powRN, Function2.apply, g] using mass_scale_steps g base c h0 hs n

end QSym.Distribution
