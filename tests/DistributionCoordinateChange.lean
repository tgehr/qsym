import QSym.DistributionCoordinateChange
import QSym.DistributionCoordinateProbe
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

private theorem step_regular {x : ℝ} (hx : x ≠ 0) : ContDiffAt ℝ 1 step x := by
  rcases lt_or_gt_of_ne hx with hl | hr
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hl] with y hy
    simp [step, hy]
  · apply (contDiffAt_const (c := (1:ℝ))).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hr] with y hy
    simp [step, hy.not_lt]

private def stepChart : VariationChart := by
  have cut : ¬ DifferentiableAt ℝ step 0 := by
    intro d
    have v : (0 : ℝ) = 1 := (tendsto_nhds_unique step_limits.1 d.continuousAt.continuousWithinAt).trans
      (tendsto_nhds_unique d.continuousAt.continuousWithinAt step_limits.2)
    exact zero_ne_one v
  refine ⟨step, [0], by simp, ?_, fun _ hx => step_regular (by simpa using hx), ?_⟩
  · intro x
    by_cases h : x = 0
    · simp [h, cut]
    · simp [h, (step_regular h).differentiableAt le_rfl]
  · intro x hx
    obtain rfl : x = 0 := by simpa using hx
    exact ⟨0, 1, step_limits.1, step_limits.2, Or.inr (by simp [step])⟩

/-- Two independent observations of the entire transformed coordinate. -/
theorem exp_step_observations :
    let c := stepChart.postcompose ChangeOn.exp (.univ stepChart)
    densityAtValue (c.present none) (some 0) = none ∧
      (c.present none).map (fun d => (realFibre d 0).charge) = some (Real.exp 1 - 1) := by
  dsimp only
  rw [density_present, charge_present]
  have l := Real.continuous_exp.continuousAt.tendsto.comp step_limits.1
  have r := Real.continuous_exp.continuousAt.tendsto.comp step_limits.2
  simp [postcompose, stepChart, leftLim_eq_of_tendsto (NeBot.ne inferInstance) l,
    rightLim_eq_of_tendsto (NeBot.ne inferInstance) r,
    abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)))]

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

/-- Each actual input admits a logarithm. The omitted left trace at zero
still sends the logarithm to minus infinity and prevents a finite jump. -/
theorem positive_values_with_log_pole :
    let f := fun x : ℝ => if x < 0 then -x else 1
    (∀ x, 0 < f x) ∧ Tendsto (Real.log ∘ f) (𝓝[<] 0) atBot := by
  dsimp only
  constructor
  · intro x; split <;> linarith
  · apply Real.tendsto_log_nhdsGT_zero.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have t : Tendsto (fun x : ℝ => -x) (𝓝[<] 0) (𝓝 0) := by
        simpa using ((continuousAt_id.neg (x := (0:ℝ))).continuousWithinAt (s := Iio 0)).tendsto
      apply t.congr'
      filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
      simp [hx]
    · filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
      simp [hx]

#qsym_check_axioms positive_values_with_log_pole
#qsym_check_axioms present_postcompose
#qsym_check_axioms exp_step
#qsym_check_axioms exp_step_observations
#qsym_check_axioms exp_step_restricted
#qsym_check_axioms log_corner
end QSym.Distribution.GraphFibre.Coordinates.ChangeTests
