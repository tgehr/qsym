import QSym.Binding
import QSym.Refinement

/-! Conservative bridges for migrating frontend extraction.

The frontend still denotes `Presentation`. For these supported observations we
prove a commuting equation to the reference-aware model, then discharge the
simplification with the ordinary `qsym_rule` prover and the verified model law
instance. This is not a representation theorem for arbitrary presentations.
-/
namespace QSym.Distribution

theorem model_mass_bind_density (p : DensityProgram) (k : ℝ → Option (D α)) :
    massValue (bindValue p.presentation (some k)) =
      massValue (weightValue (some (fun x => massValue (k x))) p.presentation) := by
  rw [p.bind_mass_bridge]
  change p.observe _ = massValue (DensityProgram.presentation (.weight _ p))
  rw [DensityProgram.mass_bridge]
  qsym_rule

theorem model_mass_integralValue (k : ℝ → Option (D α)) :
    massValue (integralValue (some k)) =
      massValue (weightValue (some (fun x => massValue (k x))) lebesgueValue) := by
  rw [DensityProgram.integral_mass_bridge]
  change DensityProgram.lebesgue.observe _ =
    massValue (DensityProgram.presentation (.weight _ .lebesgue))
  rw [DensityProgram.mass_bridge]
  qsym_rule

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

/-- The frontend's two summand orders represent the same mixed observation. -/
theorem mixed_density_bridge (atomFirst : Bool) (p : DensityProgram) (a x : ℝ) :
    densityAtValue (if atomFirst then addValue (diracValue (some a)) p.presentation
      else addValue p.presentation (diracValue (some a))) (some x) =
      (AtomPlusDensity.mk a p.density).densityAt x := by
  rw [p.presentation_eq, AtomPlusDensity.densityAt_eq]
  cases atomFirst <;> by_cases h : x = a <;> cases hw : p.density x <;>
    simp [densityAtValue, diracValue, addValue, densityValue, densityAt, Value.add, h, hw]

/-- Integration against any strict test commutes with denotation, including
when a weight or test is partial or the integral is non-finite. -/
theorem mixed_observe_bridge (a : ℝ) (p : DensityProgram) (f : ℝ → Option ℝ) :
    (addValue (diracValue (some a)) p.presentation).bind (fun d => integrate d f) =
      (AtomPlusDensity.mk a p.density).observe f := by
  rw [p.presentation_eq, AtomPlusDensity.observe_eq]
  rfl

theorem mixed_mass_bridge (a : ℝ) (p : DensityProgram) :
    massValue (addValue (diracValue (some a)) p.presentation) =
      (AtomPlusDensity.mk a p.density).mass :=
  mixed_observe_bridge a p (fun _ => some 1)

/-- The scalar frontend represents x ≠ a by nonzero (x + (-1) * a). -/
private noncomputable def awayFromAtom (a x : Option ℝ) : Option Bool :=
  Value.nonzero (Value.add x (Value.mul (some ((-1 : ℤ) : ℝ)) a))

private theorem mixed_guard (a x : ℝ) (w : ℝ → Option ℝ) :
    (AtomPlusDensity.mk a w).densityAt x =
      Binding.guardValue (awayFromAtom (some a) (some x)) (w x) := by
  have obs : (AtomPlusDensity.mk a w).densityAt x = (if x = a then none else w x) := by
    qsym_rule
  rw [obs]
  by_cases h : x = a <;>
    simp [awayFromAtom, Binding.guardValue, Value.nonzero, Value.mul, Value.add,
      ← sub_eq_add_neg, sub_eq_zero, h]

/-- Scalar expression emitted for a retained weight chain. The first factor
is emitted directly, and the empty chain uses the frontend's integer literal. -/
def DensityProgram.extractedWeight : DensityProgram → ℝ → Option ℝ
  | .lebesgue => fun _ => some ((1 : ℤ) : ℝ)
  | .weight f .lebesgue => f
  | .weight f (.weight g p) => fun x => Value.mul ((DensityProgram.weight g p).extractedWeight x) (f x)

theorem DensityProgram.extractedWeight_eq (p : DensityProgram) (x : ℝ) :
    p.extractedWeight x = p.density x := by
  induction p with
  | lebesgue => simp [extractedWeight, density]
  | weight f p ih =>
    cases p <;> simp only [extractedWeight, density, Value.mul_one_left, ih]

theorem model_density_atom_add (atomFirst : Bool) (p : DensityProgram) (a x : Option ℝ) :
    densityAtValue (if atomFirst then addValue (diracValue a) p.presentation
      else addValue p.presentation (diracValue a)) x =
      Binding.guardValue (awayFromAtom a x) (x.bind p.extractedWeight) := by
  cases a with
  | none =>
    rw [p.presentation_eq]
    cases atomFirst <;> cases x <;> rfl
  | some a =>
    cases x with
    | none =>
      rw [p.presentation_eq]
      cases atomFirst <;> rfl
    | some x =>
      rw [mixed_density_bridge, mixed_guard]
      exact congrArg _ (p.extractedWeight_eq x).symm

theorem model_density_dirac (a x : Option ℝ) :
    densityAtValue (diracValue a) x =
      Binding.guardValue (awayFromAtom a x) (some ((0 : ℤ) : ℝ)) := by
  cases a with
  | none => cases x <;> rfl
  | some a =>
    cases x with
    | none => rfl
    | some x =>
      change densityAt (.dirac a) x = _
      rw [densityAt_dirac]
      simpa only [AtomPlusDensity.densityAt_eq, Int.cast_zero] using
        mixed_guard a x (fun _ => some 0)

end QSym.Distribution
