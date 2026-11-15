import QSym.WeightedParameterSpace
import QSym.AxiomCheck

namespace QSym.WeightedParameter.Tests
noncomputable section
open MeasureTheory

def puncture (x : ℝ) : ℝ := if x = 0 then 0 else 1

theorem puncture_measurable : Measurable puncture :=
  Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const measurable_const

def punctureChart : DensityChart volume
    (Kernel.density (fun _ : PUnit => puncture)) PUnit.unit :=
  DensityChart.identity _ _ puncture_measurable

def lebesgueChart : DensityChart volume (Kernel.lebesgue PUnit) PUnit.unit :=
  DensityChart.identity _ _ measurable_const

-- The old presentation interpreter failed this right-unit density observation.
theorem density_bind_dirac :
    DensityChart.densityAt (DensityChart.compPure lebesgueChart) 0 = 1 := by
  rw [DensityChart.densityAt_compPure]
  rfl

theorem puncture_bind_dirac :
    DensityChart.densityAt (DensityChart.compPure punctureChart) 0 = 0 := by
  rw [DensityChart.densityAt_compPure]
  change puncture 0 = 0
  simp [puncture]

-- This rewrite is proved using the abstract laws, then closed with an instance.
theorem signed_interval :
    parameterTheory.observe volume (parameterTheory.density (fun _ : PUnit =>
      fun x => if -1 ≤ x ∧ x ≤ 1 then (-3 : ℝ) else 0)) PUnit.unit (fun _ => 1) =
      some (-6) := by
  have h := ParameterTheory.mass_interval parameterTheory (-1) 1 (-3) (by norm_num)
  norm_num at h ⊢
  exact h

-- The puncture disappears under the scalar observer, while remaining observable
-- above. This holds even when the finite integral is undefined (unbounded mass).
theorem puncture_scalar :
    parameterTheory.observe volume
        (parameterTheory.density (fun _ : PUnit => puncture)) PUnit.unit (fun _ => 1) =
      parameterTheory.observe volume
        (parameterTheory.density (fun _ : PUnit => fun _ => 1)) PUnit.unit (fun _ => 1) := by
  apply ParameterTheory.mass_density_congr_ae
  have h : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h] with x hx
  simp [puncture, hx]

theorem lebesgue_mass_not_finite :
    Kernel.integrate volume (Kernel.lebesgue PUnit) PUnit.unit (fun _ => 1) = none := by
  simp [Kernel.integrate, Kernel.lebesgue, Kernel.density, finiteIntegral,
    integrable_const_iff, isFiniteMeasure_iff, Real.volume_univ]

-- A nonzero density can have zero mass. Neither exact kernel equality nor exact
-- parameter isomorphisms are allowed to erase the retained pointwise weight.
def singleton : Kernel ℝ PUnit ℝ :=
  Kernel.density (fun _ x => if x = 0 then 1 else 0)

theorem singleton_mass :
    Kernel.integrate volume singleton PUnit.unit (fun _ => 1) = some 0 := by
  have h : (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) =ᵐ[volume] (fun _ => 0) := by
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [h0] with x hx
    simp [hx]
  simpa [Kernel.integrate, singleton, Kernel.density, finiteIntegral] using
    finiteIntegral_congr_ae h

theorem singleton_not_zero : singleton ≠ Kernel.density (fun _ : PUnit => fun _ => 0) := by
  intro h
  have hw := congrArg (fun p : Kernel ℝ PUnit ℝ => p.weight PUnit.unit 0) h
  norm_num [singleton, Kernel.density] at hw

theorem singleton_not_reparam_zero (e : ℝ ≃ ℝ) :
    singleton ≠ Kernel.pull e (Kernel.density (fun _ : PUnit => fun _ => 0)) := by
  intro h
  have hw := congrArg (fun p : Kernel ℝ PUnit ℝ => p.weight PUnit.unit 0) h
  norm_num [singleton, Kernel.density, Kernel.pull] at hw

-- A singular atom lacks this ordinary-density chart; it is not assigned zero.
theorem atom_has_no_chart (a : ℝ) :
    ¬ Nonempty (DensityChart (Measure.dirac PUnit.unit)
      (Kernel.pure (fun _ : PUnit => a)) PUnit.unit) := by
  rintro ⟨c⟩
  have h : (0 : ℝ) = 1 := by
    simpa using congrArg c.coord (Subsingleton.elim (c.coord.symm 0) (c.coord.symm 1))
  exact zero_ne_one h

-- Unit laws are literal equalities in the quotient, not just scalar agreement.
theorem quotient_bind_dirac (p : Trace ℝ) : Hom.comp p (Hom.pure id) = p := Hom.comp_pure p

theorem quotient_density_bind_dirac :
    (Hom.Chart.compPure (Hom.Chart.density (fun _ : PUnit => puncture)
      PUnit.unit puncture_measurable)).densityAt 0 = 0 := by
  rw [Hom.Chart.densityAt_compPure, Hom.Chart.densityAt_density]
  simp [puncture]

-- Same measure and same scalar integrals do not imply quotient equality.
theorem quotient_puncture_not_lebesgue :
    Hom.density (fun _ : PUnit => puncture) ≠ Hom.density (fun _ : PUnit => fun _ => 1) := by
  intro h
  have hd := Hom.Chart.densityAt_eq_of_eq
    (Hom.Chart.density _ PUnit.unit puncture_measurable)
    (Hom.Chart.density _ PUnit.unit measurable_const) h 0
  simp [Hom.Chart.densityAt_density, puncture] at hd

theorem quotient_weight_density :
    ((Hom.Chart.density (fun _ : PUnit => fun _ => 1) PUnit.unit measurable_const).reweight
      (fun _ => puncture) puncture_measurable).densityAt 0 = 0 := by
  rw [Hom.Chart.densityAt_reweight, Hom.Chart.densityAt_density]
  simp [puncture]

theorem quotient_punctured_interval :
    Hom.observe
      (Hom.reweight (fun _ : PUnit => puncture)
        (Hom.density (fun _ : PUnit => fun x => if -1 ≤ x ∧ x ≤ 1 then 1 else 0)))
      PUnit.unit (fun _ => 1) = some 2 := by
  have h : (fun x : ℝ => (if -1 ≤ x ∧ x ≤ 1 then (1 : ℝ) else 0) * puncture x)
      =ᵐ[volume] (fun x => if -1 ≤ x ∧ x ≤ 1 then 1 else 0) := by
    have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [h0] with x hx
    simp [puncture, hx]
  change finiteIntegral volume
    (fun x => ((if -1 ≤ x ∧ x ≤ 1 then 1 else 0) * puncture x) * 1) = some 2
  simp only [mul_one]
  rw [finiteIntegral_congr_ae h]
  have hi := finiteIntegral_interval (-1) 1 1 (by norm_num)
  norm_num at hi
  exact hi

-- Result carriers need no measurable-space instances, including actual types.
example : Kernel.integrate (Measure.dirac PUnit.unit)
    (Kernel.pure (fun _ : PUnit => fun n : ℕ => n + 1)) PUnit.unit (fun _ => 1) = some 1 :=
  Kernel.integrate_pure _ _ _

example : Kernel.integrate (Measure.dirac PUnit.unit)
    (Kernel.pure (fun _ : PUnit => ℕ)) PUnit.unit (fun _ => 1) = some 1 :=
  Kernel.integrate_pure _ _ _

example : Kernel.integrate (Measure.dirac PUnit.unit)
    (Kernel.pure (fun _ : PUnit => Kernel.lebesgue PUnit)) PUnit.unit (fun _ => 1) = some 1 :=
  Kernel.integrate_pure _ _ _

example : Kernel.integrate (Measure.dirac PUnit.unit)
    (Kernel.pure (fun _ : PUnit => (⟨1, one_ne_zero⟩ : {x : ℝ // x ≠ 0})))
      PUnit.unit (fun _ => 1) = some 1 := Kernel.integrate_pure _ _ _

example : Hom.observe (Hom.pure (fun _ : PUnit => ℕ)) PUnit.unit (fun _ => 1) = some 1 :=
  Hom.observe_pure _ _ _

example : Hom.observe
    (Hom.pure (fun _ : PUnit => (Hom.density (fun _ : PUnit => fun _ => 1) : Trace ℝ)))
      PUnit.unit (fun _ => 1) = some 1 := Hom.observe_pure _ _ _

#qsym_check_axioms kernelTheory
#qsym_check_axioms parameterTheory
#qsym_check_axioms Kernel.pull_trans
#qsym_check_axioms Kernel.reweight_pull
#qsym_check_axioms finiteIntegral_eq_partialIntegral
#qsym_check_axioms finiteIntegral_defined_iff
#qsym_check_axioms Kernel.integrate_pure
#qsym_check_axioms Kernel.integrate_comp_pure
#qsym_check_axioms Kernel.integrate_pure_comp
#qsym_check_axioms Kernel.integrate_comp_assoc
#qsym_check_axioms DensityChart.densityAt_pull
#qsym_check_axioms DensityChart.integrate_eq
#qsym_check_axioms ParameterTheory.observe_comp_pure
#qsym_check_axioms ParameterTheory.observe_comp_assoc
#qsym_check_axioms ParameterTheory.mass_interval
#qsym_check_axioms ParameterTheory.mass_density_congr_ae
#qsym_check_axioms density_bind_dirac
#qsym_check_axioms puncture_bind_dirac
#qsym_check_axioms signed_interval
#qsym_check_axioms puncture_scalar
#qsym_check_axioms lebesgue_mass_not_finite
#qsym_check_axioms singleton_mass
#qsym_check_axioms singleton_not_zero
#qsym_check_axioms singleton_not_reparam_zero
#qsym_check_axioms atom_has_no_chart
#qsym_check_axioms ParamKernel.Iso.symm
#qsym_check_axioms ParamKernel.Iso.trans
#qsym_check_axioms ParamKernel.Iso.comp
#qsym_check_axioms ParamKernel.Iso.reweight
#qsym_check_axioms ParamKernel.Iso.observe_eq
#qsym_check_axioms ParamKernel.Iso.density_eq
#qsym_check_axioms Hom.comp_pure
#qsym_check_axioms Hom.pure_comp
#qsym_check_axioms Hom.comp_assoc
#qsym_check_axioms Hom.pure_comp_pure
#qsym_check_axioms Hom.observe
#qsym_check_axioms Hom.observe_pure
#qsym_check_axioms Hom.Chart.densityAt_unique
#qsym_check_axioms Hom.Chart.observe_eq
#qsym_check_axioms Hom.Chart.densityAt_reweight
#qsym_check_axioms quotient_bind_dirac
#qsym_check_axioms quotient_density_bind_dirac
#qsym_check_axioms quotient_puncture_not_lebesgue
#qsym_check_axioms quotient_weight_density
#qsym_check_axioms quotient_punctured_interval
end
end QSym.WeightedParameter.Tests
