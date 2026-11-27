import QSym.DistributionFiniteFibreModel
import QSym.DistributionFactorModel
import QSym.DistributionSequentialModel

noncomputable section
namespace QSym.Distribution
open MeasureTheory

/-- Reweighting a distribution multiplies its strict test at each source
point. Integral and countable-sum nodes keep their original observers. -/
theorem integrate_weight (d : D α) (g f : α → Option ℝ) :
    (weight g d).bind (fun a => integrate a f) = integrate d (fun x => Value.mul (g x) (f x)) := by
  induction d with
  | invalid => rfl
  | zero => rfl
  | dirac x => cases h : g x <;> simp [weight, integrate, h, Value.mul]
  | density w v =>
    apply congrArg (partialIntegral volume)
    funext r
    cases h : v r with
    | none => cases w r <;> simp [h, Value.mul]
    | some x => simpa only [h, Option.some_bind] using Value.mul_assoc (w r) (g x) (f x)
  | add a b ha hb => exact (integrate_addValue _ _ _).trans (congrArg₂ Value.add ha hb)
  | scale r d ih => exact (integrate_scaleValue _ _ _).trans (congrArg (Value.mul (some r)) ih)
  | integral k ih => exact congrArg (partialIntegral volume) (funext fun r => (integrate_getD _ _).trans (ih r))
  | sum k ih => exact congrArg partialSum (funext fun i => (integrate_getD _ _).trans (ih i))

theorem mass_weight_test (g : α → Option ℝ) (d : Option (D α)) :
    massValue (weightValue (some g) d) = d.bind (fun a => integrate a g) := by
  cases d with
  | none => rfl
  | some d =>
    simpa only [Value.mul_one_right] using integrate_weight d g (fun _ => some 1)

theorem mass_two_weights (g f : α → Option ℝ) (d : Option (D α)) :
    massValue (weightValue (some f) (weightValue (some g) d)) =
      massValue (weightValue (some fun x => Value.mul (g x) (f x)) d) := by
  rw [mass_weight_test, mass_weight_test]
  cases d with
  | none => rfl
  | some d => exact integrate_weight d g f

/-- Evaluating both weight functions is necessary even when
the source is empty. Their values at individual points remain partial. -/
theorem mass_weight_pair (g f : Option (α → Option ℝ)) (d : Option (D α)) :
    massValue (weightValue f (weightValue g d)) =
      g.bind (fun _ => f.bind (fun _ => massValue (weightValue (some fun x =>
        Value.mul (g.bind (fun h => h x)) (f.bind (fun h => h x))) d))) := by
  cases g <;> cases f
  all_goals first | rfl | exact mass_two_weights _ _ _

theorem FiniteFibre.Represents.weighted_mass {d : Option (D ℝ)} {m : Option (FiniteFibre.Model ℝ)}
    (r : FiniteFibre.Represents d m) (g : Option (ℝ → Option ℝ)) :
    massValue (weightValue g d) = g.bind (fun test => m.bind (fun p => FiniteFibre.pairing p test)) := by
  cases g with
  | none => rfl
  | some test => exact (mass_weight_test test d).trans (r.integral test)

end QSym.Distribution
