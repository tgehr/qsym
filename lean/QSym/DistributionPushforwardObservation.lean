import QSym.DistributionWeightObservation
import QSym.DistributionModelBridge
import QSym.DistributionGraph

noncomputable section
namespace QSym.Distribution

/-- Evaluate a weighted forward image in its parameter space. The ordinary
parameter chart supports partial scalar tests and arbitrary result types. -/
theorem mass_weight_push (p : ℝ → Option Bool) (f : ℝ → Option α) (t : α → Option ℝ) :
    massValue (weightValue (some t) (pushforwardOnValue (some p) (some f))) =
      massValue (weightValue (some fun x =>
        Value.mul (Value.mask (p x) (some ((1:ℤ):ℝ))) ((f x).bind t)) lebesgueValue) := by
  rw [mass_weight_test, weighted_lebesgue_mass_bridge, Model.densityMassValue_eq, Int.cast_one]
  rfl

/-- Strictness of the three function values also holds for an empty source.
Within the integral the parameter map and the test retain their domains. -/
theorem mass_weight_push_values (p : Option (ℝ → Option Bool)) (f : Option (ℝ → Option α))
    (t : Option (α → Option ℝ)) :
    massValue (weightValue t (pushforwardOnValue p f)) =
      p.bind (fun _ => f.bind (fun _ => t.bind (fun _ =>
        massValue (weightValue (some fun x =>
          Value.mul (Value.mask (p.bind (fun h => h x)) (some ((1:ℤ):ℝ)))
            (t.bind (fun test => (f.bind (fun g => g x)).bind test))) lebesgueValue)))) := by
  cases p with
  | none => cases t <;> rfl
  | some p =>
    cases f with
    | none => cases t <;> rfl
    | some f =>
      cases t with
      | none => rfl
      | some t => exact mass_weight_push p f t

/-- Changing to real output coordinates preserves every total scalar test,
including when the parameter map or its mask is partial. -/
theorem GraphFibre.mass_weight_real_push_total (p : Option (ℝ → Option Bool))
    (f : Option (ℝ → Option ℝ)) (t : ℝ → Option ℝ) (ht : ∀ y, Value.Defined (t y)) :
    massValue (weightValue (some t) (GraphFibre.realPushforwardOnValue p f)) =
      massValue (weightValue (some t) (pushforwardOnValue p f)) := by
  rw [mass_weight_test, mass_weight_test]
  choose g hg using ht
  rw [funext hg]
  unfold realPushforwardOnValue
  cases pushforwardOnValue p f with
  | none => rfl
  | some d => exact coordinates_test d g

end QSym.Distribution
