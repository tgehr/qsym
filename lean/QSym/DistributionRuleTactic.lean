import QSym.DistributionModelLaws
import QSym.WeightedFibreTower
import QSym.DistributionSequentialModel
import QSym.DistributionFactorModel
import QSym.DistributionParametricModel
import QSym.DistributionNullSupportModel
import QSym.DistributionStepGrid

/-! Checked distribution and integral laws used by the ordinary `qsym_rule`
prover. The tactic constructs proofs from laws/instances; it never introduces
an axiom or discharges an integrability side condition by computation.
-/
namespace QSym

-- Keep the ordinary scalar rule path cheap: abstract law projections should
-- only be tried on goals that actually mention this interface or its model.
open Lean Meta Elab Tactic in
elab "qsym_distribution_goal" : tactic => do
  let target ← instantiateMVars (← getMainTarget)
  let heads := #[``partialIntegral, ``FiniteIntegralTheory.integrate,
    ``Distribution.ObservationTheory.observe, ``Distribution.ObservationTheory.comp,
    ``Distribution.ObservationTheory.reweight, ``Distribution.Model.atomTestValue,
    ``Distribution.Model.densityTestValue, ``Distribution.Model.densityMassValue,
    ``WeightedParameter.Fibre.Hom.observePartial,
    ``DependentIntegralTheory.joint, ``WeightedParameter.Fibre.Tower.observe,
    ``Distribution.DensityProgram.mass, ``Distribution.DensityIntegralTheory.mass,
    ``Distribution.DensityProgram.observe]
  unless (target.find? fun e => match e with
      | .const name _ => heads.contains name
      | _ => false).isSome do
    throwError "not a distribution-model rule goal"

macro "qsym_distribution_eq" : tactic => `(tactic| first
  | exact Distribution.DensityProgram.observe_weight _ _
  | solve | apply Distribution.DensityProgram.mass_factor <;> assumption
  | solve | apply Distribution.DensityProgram.mass_parametric <;> assumption
  | solve | apply Distribution.DensityProgram.mass_null_support <;> assumption
  | solve | apply Distribution.DensityProgram.mass_step <;> assumption
  | solve | apply Distribution.DensityProgram.mass_interval <;> assumption
  | solve | apply Distribution.DensityProgram.mass_null_edit <;> assumption
  | exact Distribution.DensityIntegralTheory.interval _ _ _ _ _ _ (by assumption)
  | exact Distribution.DensityIntegralTheory.null_edit _ _ _ _ (by assumption)
  | solve | apply DependentIntegralTheory.fubini <;> assumption
  | solve | apply WeightedParameter.Fibre.Tower.observe_fubini <;> assumption
  | solve | apply partialIntegral_compProd_of_integrable <;> assumption
  | exact Distribution.Model.atomTestValue_eq _ _
  | exact Distribution.Model.densityTestValue_eq _ _
  | exact Distribution.Model.densityMassValue_eq _
  | exact WeightedParameter.Fibre.Hom.observePartial_pure _ _ _ _
  | exact WeightedParameter.Fibre.Hom.observePartial_reweight _ _ _ _ _
  | exact Distribution.ObservationTheory.observe_pure _ _ _ _ _
  | exact Distribution.ObservationTheory.observe_reweight _ _ _ _ _ _
  | exact Distribution.ObservationTheory.comp_pure _ _
  | exact Distribution.ObservationTheory.pure_comp _ _
  | exact Distribution.ObservationTheory.comp_assoc _ _ _ _
  | exact Distribution.ObservationTheory.reweight_one _ _
  | exact Distribution.ObservationTheory.reweight_mul _ _ _ _
  | exact partialIntegral_zero _
  | solve | apply partialIntegral_scale_zero_total <;> assumption
  | solve | apply partialIntegral_scale_nonzero <;> assumption
  | solve | apply partialIntegral_scale_defined <;> assumption
  | solve | apply partialIntegral_add_defined <;> assumption
  | exact FiniteIntegralTheory.zero _
  | solve | apply FiniteIntegralTheory.scale_zero_total <;> assumption
  | solve | apply FiniteIntegralTheory.scale_nonzero <;> assumption
  | solve | apply FiniteIntegralTheory.scale_defined <;> assumption
  | solve | apply FiniteIntegralTheory.add_defined <;> assumption)

macro "qsym_distribution" : tactic => `(tactic| (qsym_distribution_goal; first
  | solve | qsym_distribution_eq
  | solve | apply Value.refines_of_eq; qsym_distribution_eq
  | solve | apply DependentIntegralTheory.fubini_refines <;> assumption
  | solve | apply WeightedParameter.Fibre.Tower.observe_fubini_refines <;> assumption
  | solve | apply partialIntegral_compProd_refines <;> assumption
  | exact partialIntegral_scale_refines _ _ _
  | exact partialIntegral_add_refines _ _ _
  | exact FiniteIntegralTheory.scale_refines _ _ _
  | exact FiniteIntegralTheory.add_refines _ _ _))

end QSym
