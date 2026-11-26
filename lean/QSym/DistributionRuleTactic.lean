import QSym.DistributionOddPower
import QSym.DistributionRootCover
import QSym.DistributionPartialModel
import QSym.DistributionWeightedSquare
import QSym.DistributionCoordinateProbe
import QSym.DistributionCoordinateJumps
import QSym.DistributionAtomRows
import QSym.DistributionFiniteMixedReal
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
  let heads := #[``Distribution.GraphFibre.RootCover, ``Distribution.GraphFibre.GlobalInverseBranch, ``Distribution.GraphFibre.branchIntegral, ``Distribution.GraphFibre.fibreOn,
    ``partialIntegral, ``FiniteIntegralTheory.integrate, ``Distribution.GraphFibre.weightedSquareDensity,
    ``Distribution.GraphFibre.Coordinates.value, ``Distribution.GraphFibre.Coordinates.restricted,
    ``Distribution.GraphFibre.chartObservations, ``Distribution.GraphFibre.inverseCoverValue,
    ``Distribution.GraphFibre.inverseCoverOutput, ``Distribution.GraphFibre.radiusOutput, ``Distribution.GraphFibre.radiusImageValue,
    ``Distribution.GraphFibre.imageIntegral, ``Distribution.GraphFibre.affineSquareSource,
    ``Distribution.ObservationTheory.observe, ``Distribution.ObservationTheory.comp,
    ``Distribution.ObservationTheory.reweight, ``Distribution.Model.atomTestValue,
    ``Distribution.GraphFibre.realBindValue, ``Distribution.GraphFibre.realIntegralValue,
    ``Distribution.GraphFibre.realPushforwardOnValue, ``Distribution.pushforwardOnValue, ``Distribution.GraphFibre.marginalOn, ``Distribution.GraphFibre.marginal, ``Distribution.GraphFibre.fibre, ``Distribution.GraphFibre.maskedAtoms, ``Distribution.RealDensityFibre.density, ``Distribution.AtomPlusDensity.densityAt, ``Distribution.AtomPlusDensity.mass,
    ``Distribution.Model.densityTestValue, ``Distribution.Model.densityMassValue,
    ``WeightedParameter.Fibre.Hom.observePartial,
    ``WeightedParameter.Fibre.PartialHom.sectionAt, ``WeightedParameter.Fibre.PartialHom.marginalize,
    ``WeightedParameter.Fibre.RootedPartialHom.marginalize, ``integrateSections, ``Distribution.DensityProgram.semanticDensityAt,
    ``DependentIntegralTheory.joint, ``WeightedParameter.Fibre.Tower.observe,
    ``Distribution.DensityProgram.mass, ``Distribution.DensityIntegralTheory.mass,
    ``Distribution.DensityProgram.observe]
  unless (target.find? fun e => match e with
      | .const name _ => heads.contains name
      | _ => false).isSome do
    throwError "not a distribution-model rule goal"

macro "qsym_distribution_eq" : tactic => `(tactic| first
  | exact Distribution.GraphFibre.masked_square_disintegrates _ _
  | solve | apply Distribution.GraphFibre.masked_square_regular_eq; assumption
  | solve | apply Distribution.GraphFibre.square_positive; assumption
  | solve | apply Distribution.GraphFibre.square_negative; assumption
  | solve | apply Distribution.GraphFibre.pushforwardOn_density; assumption
  | solve | apply Distribution.GraphFibre.masked_square_positive; assumption
  | solve | apply Distribution.GraphFibre.masked_square_negative; assumption
  | exact Distribution.GraphFibre.masked_square_zero _
  | solve | apply Distribution.GraphFibre.masked_affine_atoms; assumption
  | solve | apply Distribution.GraphFibre.affine_fibre; assumption
  | solve | apply Distribution.GraphFibre.affine_lebesgue; assumption
  | exact Distribution.GraphFibre.realIntegral_dirac _ _
  | exact Distribution.GraphFibre.realBind_dirac _ _
  | exact Distribution.GraphFibre.realBind_weight_dirac _ _
  | exact Distribution.GraphFibre.realPushforward_identity _
  | exact Distribution.GraphFibre.realPushforward_mass_total _ _
  | exact Distribution.GraphFibre.pushforwardOn_test _ _ _
  | exact Distribution.GraphFibre.mass_pushforwardOn_total _ _
  | solve | apply Distribution.GraphFibre.square_positiveSource_lebesgue; assumption
  | exact Distribution.GraphFibre.square_marginalOn_openUnit _
  | solve | apply Distribution.GraphFibre.square_marginal_positive; assumption
  | solve | apply Distribution.GraphFibre.square_marginal_negative; assumption
  | exact Distribution.GraphFibre.square_marginal_zero
  | exact Distribution.GraphFibre.square_critical
  | exact Distribution.RealDensityFibre.density_eq _
  | exact Distribution.AtomPlusDensity.densityAt_eq _ _
  | exact Distribution.AtomPlusDensity.mass_eq _
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
  | solve | apply FiniteIntegralTheory.add_defined <;> assumption
  | exact Distribution.DensityProgram.semanticDensityAt_eq _ _
  | apply WeightedParameter.Fibre.PartialHom.observe_sectionAt_weighted_pure
  | apply WeightedParameter.Fibre.PartialHom.observe_sectionAt
  | apply WeightedParameter.Fibre.PartialHom.sectionAt_add
  | apply WeightedParameter.Fibre.PartialHom.sectionAt_reweight
  | apply WeightedParameter.Fibre.PartialHom.marginalize_reweight
  | apply WeightedParameter.Fibre.PartialHom.sectionAt_marginalize
  | apply WeightedParameter.Fibre.PartialHom.reindex_marginalize
  | apply WeightedParameter.Fibre.PartialHom.marginalize_marginalize
  | apply WeightedParameter.Fibre.PartialHom.observe_marginalize
  | apply WeightedParameter.Fibre.RootedPartialHom.observeJoint_marginalize
  | apply WeightedParameter.Fibre.PartialHom.observeJoint_marginalize
  | solve | apply WeightedParameter.Fibre.PartialFamily.observeJoint_sections; assumption
  | solve | apply partialIntegral_compProd_sections; assumption
  | solve | apply Distribution.GraphFibre.fibreOn_of_injOn <;> assumption
  | solve | apply Distribution.GraphFibre.fibreOn_of_notMem_image <;> assumption
  | solve | apply Distribution.GraphFibre.branchIntegral_union <;> assumption
  | solve | apply Distribution.GraphFibre.branchIntegral_image <;> assumption
  | solve | apply Distribution.GraphFibre.affine_square_image_integral <;> assumption
  | solve | apply Distribution.GraphFibre.affine_square_masked_image_integral <;> assumption
  | solve | apply Distribution.GraphFibre.unrestricted_density_eq_marginal <;> assumption
  | solve | apply Distribution.GraphFibre.affine_square_critical_density <;> assumption
  | solve | apply Distribution.GraphFibre.restrict_target_chart <;> assumption
  | solve | apply Distribution.GraphFibre.restrict_target_density; assumption
  | solve | apply Distribution.GraphFibre.radius_sublevel; assumption
  | solve | apply Distribution.GraphFibre.sqrtRadius_image_integral; assumption
  | solve | apply Distribution.GraphFibre.sqrtRadius_image; assumption
  | solve | apply Distribution.GraphFibre.sqrtRadius_output; assumption
  | solve | apply Distribution.GraphFibre.Coordinates.singleton_join <;> assumption
  | solve | apply Distribution.GraphFibre.Coordinates.length_eq; assumption
  | solve | apply Distribution.GraphFibre.Coordinates.restricted_length_eq; assumption
  | solve | apply Distribution.GraphFibre.Coordinates.density_pieces; assumption
  | solve | apply Distribution.GraphFibre.Coordinates.pieces_eq; assumption
  | solve | apply Distribution.GraphFibre.Coordinates.restricted_pieces_eq; assumption
  | solve | apply Distribution.GraphFibre.Coordinates.branch_image <;> assumption
  | solve | apply Distribution.GraphFibre.inverseCover_joint_split <;> assumption
  | solve | apply Distribution.GraphFibre.inversePart_density_roots <;> assumption
  | solve | apply Distribution.GraphFibre.inversePart_pairing_split <;> assumption
  | solve | apply Distribution.GraphFibre.inverseCover_sum <;> assumption
  | solve | apply Distribution.GraphFibre.inverseCover_eq; assumption
  | solve | apply Distribution.GraphFibre.inverseCoverOutput_eq; assumption
  | solve | apply Distribution.GraphFibre.radiusOutput_of_inverse; assumption
  | solve | apply Distribution.GraphFibre.radiusImage_of_inverse; assumption
  | solve | apply Distribution.GraphFibre.imageIntegral_of_transport <;> assumption
  | exact Distribution.GraphFibre.weighted_square_density _ _
  | solve | apply Distribution.GraphFibre.weighted_square_chart <;> assumption
  | solve | apply Distribution.GraphFibre.weighted_square_integral <;> assumption
  | solve | apply Distribution.GraphFibre.integral_pair_common_test <;> assumption
  | solve | apply Distribution.GraphFibre.affine_square_integral <;> assumption
  | solve | apply Distribution.GraphFibre.square_masked_integral <;> assumption
  | solve | apply Distribution.GraphFibre.square_positiveSource_disintegrates <;> assumption
  | solve | apply Distribution.GraphFibre.injectiveBranch_disintegrates <;> assumption
  | solve | apply Distribution.GraphFibre.injectiveBranch_disintegrates_masked <;> assumption
  | solve | apply Distribution.GraphFibre.injectiveBranch_disintegrates_ae <;> assumption
  | solve | apply Distribution.GraphFibre.RootCover.precomp <;> assumption
  | solve | apply Distribution.GraphFibre.RootCover.restrict <;> assumption
  | solve | apply Distribution.GraphFibre.RootCover.density <;> assumption
  | solve | apply Distribution.GraphFibre.GlobalInverseBranch.comp <;> assumption
  | solve | apply Distribution.GraphFibre.GlobalInverseBranch.fibreOn_eq <;> assumption
  | solve | apply Distribution.GraphFibre.GlobalInverseBranch.maskedAtoms_eq <;> assumption
  | solve | apply Distribution.GraphFibre.GlobalInverseBranch.density_defined_iff <;> assumption
  | solve | apply Distribution.GraphFibre.GlobalInverseBranch.density_total_iff <;> assumption
  | solve | apply Distribution.GraphFibre.GlobalInverseBranch.density_eq <;> assumption
  | solve | apply Distribution.GraphFibre.GlobalInverseBranch.lebesgueChart <;> assumption
  | exact Distribution.GraphFibre.oddPower_fibre _ _
  | exact Distribution.GraphFibre.oddPower_masked _ _ _
  | exact Distribution.GraphFibre.oddPower_density _ _ _
  | solve | apply Distribution.GraphFibre.oddPower_chart <;> assumption)

macro "qsym_distribution" : tactic => `(tactic| (qsym_distribution_goal; first
  | solve | qsym_distribution_eq
  | exact Distribution.GraphFibre.masked_square_regular_refines _ _
  | solve | apply Value.refines_of_eq; qsym_distribution_eq
  | solve | apply DependentIntegralTheory.fubini_refines <;> assumption
  | solve | apply WeightedParameter.Fibre.Tower.observe_fubini_refines <;> assumption
  | solve | apply partialIntegral_compProd_refines <;> assumption
  | exact partialIntegral_scale_refines _ _ _
  | exact partialIntegral_add_refines _ _ _
  | exact FiniteIntegralTheory.scale_refines _ _ _
  | exact FiniteIntegralTheory.add_refines _ _ _))

end QSym
