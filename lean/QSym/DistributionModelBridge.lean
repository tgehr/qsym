import QSym.Distribution
import QSym.Refinement

/-! Conservative bridges for migrating frontend extraction.

The frontend still denotes `Presentation`. For these supported observations we
prove a commuting equation to the reference-aware model, then discharge the
simplification with the ordinary `qsym_rule` prover and the verified model law
instance. This is not a representation theorem for arbitrary presentations.
-/
namespace QSym.Distribution

theorem atom_observation_bridge {A : Type} (f : Option (A → Option ℝ)) (a : Option A) :
    massValue (weightValue f (diracValue a)) = Model.atomTestValue f a := by
  rw [Model.atomTestValue_eq]
  exact mass_weight_diracValue f a

theorem density_observation_bridge (f : Option (ℝ → Option ℝ)) (x : Option ℝ) :
    densityAtValue (weightValue f lebesgueValue) x = Model.densityTestValue f x := by
  rw [Model.densityTestValue_eq]
  exact density_weight_lebesgueValue f x

theorem density_mass_bridge (f : Option (ℝ → Option ℝ)) :
    massValue (densityValue f) = Model.densityMassValue f := by
  rw [Model.densityMassValue_eq]
  cases f with
  | none => rfl
  | some f =>
    change partialIntegral _ (fun x => Value.mul (f x) (some 1)) = partialIntegral _ f
    simp only [Value.mul_one_right]

theorem weighted_lebesgue_mass_bridge (f : Option (ℝ → Option ℝ)) :
    massValue (weightValue f lebesgueValue) = Model.densityMassValue f := by
  rw [Model.densityMassValue_eq]
  cases f with
  | none => rfl
  | some f =>
    change partialIntegral _ (fun x => Value.mul (Value.mul (some 1) (f x)) (some 1)) =
      partialIntegral _ f
    simp only [Value.mul_one_left, Value.mul_one_right]

theorem model_mass_weight_diracValue {A : Type} (f : Option (A → Option ℝ)) (a : Option A) :
    massValue (weightValue f (diracValue a)) = f.bind (fun g => a.bind g) := by
  rw [atom_observation_bridge]
  qsym_rule

theorem model_density_weight_lebesgueValue (f : Option (ℝ → Option ℝ)) (x : Option ℝ) :
    densityAtValue (weightValue f lebesgueValue) x = f.bind (fun g => x.bind g) := by
  rw [density_observation_bridge]
  qsym_rule

theorem model_mass_diracValue {A : Type} (a : Option A) :
    massValue (diracValue a) = a.bind (fun _ => some ((1 : ℤ) : ℝ)) := by
  have hm : massValue (diracValue a) = Model.atomTestValue (some (fun _ => some ((1 : ℤ) : ℝ))) a := by
    rw [Model.atomTestValue_eq]
    exact mass_diracValue a
  rw [hm]
  qsym_rule

theorem model_density_lebesgueValue (x : Option ℝ) :
    densityAtValue lebesgueValue x = x.bind (fun _ => some ((1 : ℤ) : ℝ)) := by
  have hm : densityAtValue lebesgueValue x = Model.densityTestValue (some (fun _ => some ((1 : ℤ) : ℝ))) x := by
    rw [Model.densityTestValue_eq]
    exact density_lebesgueValue x
  rw [hm]
  qsym_rule

end QSym.Distribution
