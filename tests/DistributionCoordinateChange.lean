import QSym.DistributionCoordinateChange
import QSym.DistributionCoordinateCorners
import QSym.AxiomCheck

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.ChangeTests
open VariationChart Filter Set Topology

private def step (x : ℝ) : ℝ := if x < 0 then 0 else 1

private theorem step_limits : Tendsto step (𝓝[<] 0) (𝓝 0) ∧ Tendsto step (𝓝[>] 0) (𝓝 1) := by
  constructor
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
    simp [step, hx]
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    simp [step, hx.not_lt]

/-- Exponentiating a unit jump changes its source length to e−1. -/
theorem exp_step : atCut (Real.exp ∘ step) 0 none = atom 0 (some (Real.exp 1 - 1)) := by
  rw [ChangeOn.exp.atCut step_limits.1 step_limits.2 trivial trivial]
  simp [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)))]

/-- A partial predicate is integrated over all new jump values. -/
theorem exp_step_restricted (p : ℝ → Option Bool) :
    atCut (Real.exp ∘ step) 0 (some p) =
      atom 0 (branchIntegral (Icc 1 (Real.exp 1)) (fun y => Value.mask (p y) (some 1))) := by
  rw [ChangeOn.exp.atCut step_limits.1 step_limits.2 trivial trivial]
  simp [uIcc_of_le (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1))]

/-- A logarithm is regular along 1+|x|, but the pointwise corner survives. -/
theorem log_corner : densityAtValue (atCut (fun x : ℝ => Real.log (1 + |x|)) 0 none) (some 0) = none := by
  have tc : ContinuousAt (fun x : ℝ => 1 + |x|) 0 := continuousAt_const.add continuous_abs.continuousAt
  have hl := tc.continuousWithinAt (s := Iio 0)
  have hr := tc.continuousWithinAt (s := Ioi 0)
  have h : 1 + |(0 : ℝ)| ∈ Ioi (0 : ℝ) := by norm_num
  change densityAtValue (atCut (Real.log ∘ (fun x : ℝ => 1 + |x|)) 0 none) _ = _
  rw [ChangeOn.log.atCut hl hr h h]
  simp [corner_density]

#qsym_check_axioms present_postcompose
#qsym_check_axioms exp_step
#qsym_check_axioms exp_step_restricted
#qsym_check_axioms log_corner
end QSym.Distribution.GraphFibre.Coordinates.ChangeTests
