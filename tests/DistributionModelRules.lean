import QSym.DistributionModelBridge
import QSym.AxiomCheck

noncomputable section
namespace QSym.DistributionRuleTests
open MeasureTheory Distribution
open WeightedParameter.Fibre

-- The same prover used by rulec, with both abstract laws and the closed model.
theorem generic_right_unit (T : ObservationTheory ℝ) (p : T.K ℕ ℝ) :
    T.comp p (T.pure (fun _ => id)) = p := by qsym_rule

theorem generic_observe (T : ObservationTheory ℝ) (f : ℝ → ℕ → ℝ)
    (x : ℝ) (n : ℕ) (g : ℝ → Option ℝ) :
    T.observe (T.pure f) x n g = g (f x n) := by qsym_rule

theorem generic_reweight (T : ObservationTheory ℝ) (p : T.K ℕ ℝ)
    (g : ℝ → ℕ → ℝ → ℝ) (x : ℝ) (n : ℕ) (f : ℝ → Option ℝ) :
    T.observe (T.reweight g p) x n f =
      T.observe p x n (fun b => Value.mul (some (g x n b)) (f b)) := by qsym_rule

theorem ordinary_atom {A : Type} (f : Option (A → Option ℝ)) (a : Option A) :
    Value.Refines (Model.atomTestValue f a) (f.bind (fun g => a.bind g)) := by qsym_rule

theorem ordinary_density (f : Option (ℝ → Option ℝ)) (x : Option ℝ) :
    Value.Refines (Model.densityTestValue f x) (f.bind (fun g => x.bind g)) := by qsym_rule

theorem ordinary_density_mass (f : Option (ℝ → Option ℝ)) :
    Model.densityMassValue f = f.bind (partialIntegral volume) := by qsym_rule

theorem ordinary_scale (T : FiniteIntegralTheory ℝ) (c : ℝ) (hc : c ≠ 0)
    (f : ℝ → Option ℝ) :
    Value.Refines (T.integrate (fun x => Value.mul (some c) (f x)))
      (Value.mul (some c) (T.integrate f)) := by qsym_rule

theorem ordinary_scale_defined (T : FiniteIntegralTheory ℝ) (c : ℝ)
    (f : ℝ → Option ℝ) (hf : Value.Defined (T.integrate f)) :
    T.integrate (fun x => Value.mul (some c) (f x)) = Value.mul (some c) (T.integrate f) := by
  qsym_rule

theorem ordinary_add_defined (T : FiniteIntegralTheory ℝ) (f g : ℝ → Option ℝ)
    (hf : Value.Defined (T.integrate f)) (hg : Value.Defined (T.integrate g)) :
    T.integrate (fun x => Value.add (f x) (g x)) = Value.add (T.integrate f) (T.integrate g) := by
  qsym_rule

theorem ordinary_contract (T : FiniteIntegralTheory ℝ) (f g : ℝ → Option ℝ) :
    Value.Refines (Value.add (T.integrate f) (T.integrate g))
      (T.integrate (fun x => Value.add (f x) (g x))) := by qsym_rule

theorem concrete_scale (c : ℝ) (hc : c ≠ 0) (f : ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mul (some c) (f x)) =
      Value.mul (some c) (partialIntegral volume f) := by qsym_rule

theorem concrete_contract (c : ℝ) (f : ℝ → Option ℝ) :
    Value.Refines (Value.mul (some c) (partialIntegral volume f))
      (partialIntegral volume (fun x => Value.mul (some c) (f x))) := by qsym_rule

theorem ordinary_zero_scale (T : FiniteIntegralTheory ℝ) (f : ℝ → Option ℝ)
    (hf : ∀ x, Value.Defined (f x)) :
    T.integrate (fun x => Value.mul (some 0) (f x)) = some 0 := by qsym_rule

-- Undefined integrands at null points remain undefined, including after a
-- zero scalar multiplier. Their totalization would be the integrable zero.
def hole (x : ℝ) : Option ℝ := if x = 0 then none else some 0

theorem hole_integrable : Integrable (fun x => (hole x).getD 0) volume := by
  have h : (fun x => (hole x).getD 0) = fun _ : ℝ => (0 : ℝ) := by
    funext x; by_cases hx : x = 0 <;> simp [hole, hx]
  rw [h]
  exact integrable_zero _ _ _

theorem hole_undefined : partialIntegral volume hole = none := by
  have hn : ¬ (∀ x, Value.Defined (hole x)) := by
    intro h; simpa [hole, Value.Defined] using h 0
  simp [partialIntegral, hn]

theorem density_hole : Model.densityTestValue (some hole) (some 0) = none := by
  rw [Model.densityTestValue_eq]
  simp [hole]

theorem density_hole_mass : Model.densityMassValue (some hole) = none := by
  rw [Model.densityMassValue_eq]
  exact hole_undefined

theorem hole_ae_zero : hole =ᵐ[volume] (fun _ : ℝ => some (0 : ℝ)) := by
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [h0] with x hx
  simp [hole, hx]

theorem strict_partial_not_ae :
    partialIntegral volume hole ≠ partialIntegral volume (fun _ : ℝ => some (0 : ℝ)) := by
  rw [hole_undefined, partialIntegral_zero]
  simp

theorem infinite_one : partialIntegral volume (fun _ : ℝ => some (1 : ℝ)) = none := by
  simp [partialIntegral, Value.Defined, integrable_const_iff, isFiniteMeasure_iff, Real.volume_univ]

theorem zero_scale_obstruction :
    ¬ Value.Refines
      (partialIntegral volume (fun _ : ℝ => Value.mul (some 0) (some (1 : ℝ))))
      (Value.mul (some 0) (partialIntegral volume (fun _ : ℝ => some (1 : ℝ)))) := by
  simp [Value.mul, partialIntegral_zero, infinite_one, Value.Refines]

theorem split_sum_obstruction :
    ¬ Value.Refines
      (partialIntegral volume (fun _ : ℝ => Value.add (some (1 : ℝ)) (some (-1))))
      (Value.add (partialIntegral volume (fun _ : ℝ => some (1 : ℝ)))
        (partialIntegral volume (fun _ : ℝ => some (-1 : ℝ)))) := by
  simp [Value.add, partialIntegral_zero, infinite_one, Value.Refines]

-- The distribution branch of ordinary rule search must not manufacture the
-- missing capabilities or fall through to a different distribution law.
example (T : FiniteIntegralTheory ℝ) (c : ℝ) (f : ℝ → Option ℝ) :
    Value.Refines (Value.mul (some c) (T.integrate f))
      (T.integrate (fun x => Value.mul (some c) (f x))) := by
  fail_if_success
    have bad : T.integrate (fun x => Value.mul (some c) (f x)) =
        Value.mul (some c) (T.integrate f) := by
      qsym_distribution
  qsym_rule

private def atomAndInterval : AtomPlusDensity :=
  ⟨0, fun x => some (if 0 ≤ x ∧ x ≤ 1 then 1 else 0)⟩

theorem mixed_interval_density (x : ℝ) :
    atomAndInterval.densityAt x =
      if x = 0 then none else some (if 0 ≤ x ∧ x ≤ 1 then 1 else 0) := by
  qsym_rule

theorem mixed_interval_mass : atomAndInterval.mass = some 2 := by
  have hi := partialIntegral_interval atomAndInterval.weight 0 1 1 [] zero_le_one
    (fun _ => ⟨_, rfl⟩) (fun _ _ => rfl)
  rw [AtomPlusDensity.mass_eq, hi]
  norm_num [Value.add]

private def cancelling (a : ℝ) : FiniteMixedReal :=
  ⟨[(a,3), (a,-3)], fun _ => some 1⟩

theorem cancelling_density (a x : ℝ) : densityAt (cancelling a).presentation x = some 1 := by
  rw [FiniteMixedReal.densityAt_bridge]
  by_cases h : x = a <;> norm_num [cancelling, FiniteMixedReal.charge, h]

theorem cancelling_test_hole (a : ℝ) (f : ℝ → Option ℝ) (h : f a = none) :
    FiniteMixedReal.atomicObserve (cancelling a).atoms f (some 0) = none := by
  simp [cancelling, FiniteMixedReal.atomicObserve, Value.mul, Value.add, h]

theorem undefined_coefficient_away (a x : ℝ) (w : ℝ → Option ℝ) (hw : w a = none) :
    densityAtValue (addValue (weightValue (some w) (diracValue (some a))) lebesgueValue)
      (some x) = none := by
  simp [weightValue, weight, diracValue, addValue, densityAtValue, hw]

-- Integrating the singleton charges of moving atoms would incorrectly give
-- zero for every x. This constructor still requests a row-wise density proof.
theorem integral_of_moving_atoms (x : ℝ) :
    densityAt (.integral (fun a => .dirac a)) x = none := by
  have hn : ¬ ∀ a : ℝ, Value.Defined (densityAt (.dirac a) x) := by
    intro h
    simpa [Value.Defined] using h x
  change (RealDensityFibre.mk 0 (partialIntegral volume (fun a => densityAt (.dirac a) x))).density = none
  simp only [RealDensityFibre.density, if_pos rfl, partialIntegral, hn, false_and, if_false, if_true]

#qsym_check_axioms undefined_coefficient_away
#qsym_check_axioms integral_of_moving_atoms
#qsym_check_axioms cancelling_density
#qsym_check_axioms cancelling_test_hole
#qsym_check_axioms FiniteMixedReal.atomicObserve_singleton
#qsym_check_axioms AtomPlusDensity.observe_toFinite
#qsym_check_axioms AtomPlusDensity.density_toFinite
#qsym_check_axioms FiniteMixedReal.observe_perm
#qsym_check_axioms FiniteMixedReal.fibre_perm
#qsym_check_axioms FiniteMixedReal.observe_parameterSpace
#qsym_check_axioms FiniteMixedReal.observe_bridge
#qsym_check_axioms FiniteMixedReal.fibre_bridge
#qsym_check_axioms mixed_interval_density
#qsym_check_axioms mixed_interval_mass
#qsym_check_axioms mixed_density_bridge
#qsym_check_axioms mixed_mass_bridge
#qsym_check_axioms model_density_atom_add
#qsym_check_axioms model_density_dirac
#qsym_check_axioms partialIntegral_comp
#qsym_check_axioms partialIntegral_scale_zero_defined_iff
#qsym_check_axioms finiteIntegralTheory
#qsym_check_axioms fibreObservationTheory
#qsym_check_axioms Family.Iso.observePartial_eq
#qsym_check_axioms Family.Iso.observeJointPartial_eq
#qsym_check_axioms Hom.observePartial_some
#qsym_check_axioms Hom.observeJointPartial_some
#qsym_check_axioms Hom.observePartial_reindex
#qsym_check_axioms atom_observation_bridge
#qsym_check_axioms density_observation_bridge
#qsym_check_axioms density_mass_bridge
#qsym_check_axioms weighted_lebesgue_mass_bridge
#qsym_check_axioms model_mass_weight_diracValue
#qsym_check_axioms model_density_weight_lebesgueValue
#qsym_check_axioms model_mass_diracValue
#qsym_check_axioms model_density_lebesgueValue
#qsym_check_axioms generic_right_unit
#qsym_check_axioms generic_observe
#qsym_check_axioms generic_reweight
#qsym_check_axioms ordinary_atom
#qsym_check_axioms ordinary_density
#qsym_check_axioms ordinary_density_mass
#qsym_check_axioms ordinary_scale
#qsym_check_axioms ordinary_scale_defined
#qsym_check_axioms ordinary_add_defined
#qsym_check_axioms ordinary_contract
#qsym_check_axioms concrete_scale
#qsym_check_axioms concrete_contract
#qsym_check_axioms ordinary_zero_scale
#qsym_check_axioms hole_integrable
#qsym_check_axioms hole_undefined
#qsym_check_axioms density_hole
#qsym_check_axioms density_hole_mass
#qsym_check_axioms hole_ae_zero
#qsym_check_axioms strict_partial_not_ae
#qsym_check_axioms infinite_one
#qsym_check_axioms zero_scale_obstruction
#qsym_check_axioms split_sum_obstruction

end QSym.DistributionRuleTests
