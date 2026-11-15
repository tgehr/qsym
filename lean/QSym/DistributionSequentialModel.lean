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

private theorem mass_getD (d : Option (D α)) :
    integrate (d.getD .invalid) (fun _ => some 1) = massValue d := by
  cases d <;> rfl

/-- Only the real source is interpreted as a density program. A continuation
may return any supported value type and any presentation, including failure. -/
theorem bind_mass_bridge (p : DensityProgram) (k : ℝ → Option (D α)) :
    massValue (bindValue p.presentation (some k)) =
      p.observe (fun x => massValue (k x)) := by
  rw [p.presentation_eq, observe, Model.densityMassValue_eq]
  change partialIntegral _ (fun x =>
    integrate ((scaleValue (p.density x) (k x)).getD .invalid) (fun _ => some 1)) = _
  simp only [mass_getD, mass_scaleValue, Option.bind_some]
  rfl

theorem integral_mass_bridge (k : ℝ → Option (D α)) :
    massValue (integralValue (some k)) =
      lebesgue.observe (fun x => massValue (k x)) := by
  rw [observe, Model.densityMassValue_eq]
  change partialIntegral _ (fun x => integrate ((k x).getD .invalid) (fun _ => some 1)) = _
  simp only [mass_getD, density, Value.mul_one_left, Option.bind_some]
  rfl

end DensityProgram
end QSym.Distribution
