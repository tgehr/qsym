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
