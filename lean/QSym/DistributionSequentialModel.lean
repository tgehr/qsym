import QSym.DistributionDensityModel

/-! Ordered observations of source integrals and density-source binds.

The continuation supplies a partial scalar observation, so its failure remains
visible even where the source weight is zero. These equations preserve the
order of integration. They neither flatten a tower nor assert a Fubini law.
The continuation's value type needs no measurable-space structure.
-/
noncomputable section
namespace QSym.Distribution

namespace DensityProgram

def observe (p : DensityProgram) (f : ℝ → Option ℝ) : Option ℝ :=
  Model.densityMassValue (some (fun x => Value.mul (p.density x) (f x)))

theorem observe_weight (p : DensityProgram) (f : ℝ → Option ℝ) :
    p.observe f = (weight f p).mass := rfl

/-- A constant weight can be pulled out of a defined strict observation.
The hypothesis keeps nonintegrable observations and undefined points visible,
including when the constant weight is zero. -/
theorem observe_weight_const (p : DensityProgram) (c : Option ℝ)
    (f : ℝ → Option ℝ) (hd : Value.Defined (p.observe f)) :
    (weight (fun _ => c) p).observe f = Value.mul c (p.observe f) := by
  simp only [observe, Model.densityMassValue_eq, Option.some_bind] at hd ⊢
  cases c with
  | none =>
    have hrow : (fun x => Value.mul ((weight (fun _ => none) p).density x) (f x)) =
        fun _ : ℝ => none := by
      funext x
      simp [DensityProgram.density, Value.mul]
    rw [hrow]
    simp [partialIntegral, Value.Defined, Value.mul]
  | some r =>
    have hrow : (fun x => Value.mul ((weight (fun _ => some r) p).density x) (f x)) =
        fun x => Value.mul (some r) (Value.mul (p.density x) (f x)) := by
      funext x
      cases hp : p.density x <;> cases hf : f x <;>
        simp [DensityProgram.density, hp, hf, Value.mul, mul_assoc, mul_left_comm]
    rw [hrow]
    exact partialIntegral_scale_defined MeasureTheory.volume r
      (fun x => Value.mul (p.density x) (f x)) hd

private theorem integrate_getD (d : Option (D α)) (f : α → Option ℝ) :
    integrate (d.getD .invalid) f = d.bind (fun a => integrate a f) := by
  cases d <;> rfl

private theorem integrate_scaleValue (r : Option ℝ) (d : Option (D α))
    (f : α → Option ℝ) :
    (scaleValue r d).bind (fun a => integrate a f) =
      Value.mul r (d.bind (fun a => integrate a f)) := by
  cases r <;> cases d <;> rfl

/-- Pointwise source observation is compatible with the old presentation
observer for every strict partial test, not only for mass. -/
theorem observe_bridge (p : DensityProgram) (f : ℝ → Option ℝ) :
    p.observe f = p.presentation.bind (fun d => integrate d f) := by
  rw [p.presentation_eq, observe, Model.densityMassValue_eq]
  rfl

/-- Only the real source is interpreted as a density program. A continuation
may return any supported value type and any presentation, including failure. -/
theorem bind_observe_bridge (p : DensityProgram) (k : ℝ → Option (D α))
    (f : α → Option ℝ) :
    (bindValue p.presentation (some k)).bind (fun d => integrate d f) =
      p.observe (fun x => (k x).bind (fun d => integrate d f)) := by
  rw [p.presentation_eq, observe, Model.densityMassValue_eq]
  change partialIntegral _ (fun x =>
    integrate ((scaleValue (p.density x) (k x)).getD .invalid) f) = _
  simp only [integrate_getD, integrate_scaleValue, Option.bind_some]
  rfl

theorem bind_mass_bridge (p : DensityProgram) (k : ℝ → Option (D α)) :
    massValue (bindValue p.presentation (some k)) =
      p.observe (fun x => massValue (k x)) :=
  bind_observe_bridge p k (fun _ => some 1)

theorem integral_observe_bridge (k : ℝ → Option (D α)) (f : α → Option ℝ) :
    (integralValue (some k)).bind (fun d => integrate d f) =
      lebesgue.observe (fun x => (k x).bind (fun d => integrate d f)) := by
  rw [observe, Model.densityMassValue_eq]
  change partialIntegral _ (fun x => integrate ((k x).getD .invalid) f) = _
  simp only [integrate_getD, density, Value.mul_one_left, Option.bind_some]
  rfl

theorem integral_mass_bridge (k : ℝ → Option (D α)) :
    massValue (integralValue (some k)) =
      lebesgue.observe (fun x => massValue (k x)) :=
  integral_observe_bridge k (fun _ => some 1)

end DensityProgram
end QSym.Distribution
