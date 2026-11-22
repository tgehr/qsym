import QSym.DistributionSquareIntegral
import QSym.DistributionGraphBridge
import QSym.AxiomCheck

noncomputable section
namespace QSym.Distribution.RestrictedSquareTests
open GraphFibre MeasureTheory Set

/-- The zero joint test has source integral zero. An active critical root
still makes the strict integral of the target fibres undefined. -/
theorem critical_reconstruction_obstruction :
    partialIntegral volume (fun _ : ℝ => some (0 : ℝ)) = some 0 ∧
    partialIntegral volume (fun y =>
      (maskedKernel (some fun _ => some true) (some fun x => some (square x))).bind
        (fun k => (k y).bind (fun d => integrate d (fun _ => some 0)))) = none := by
  refine ⟨partialIntegral_zero _, ?_⟩
  rw [maskedKernel_total _ square (measurable_id.pow_const 2)]
  unfold partialIntegral
  split
  · rename_i h
    obtain ⟨_, hv⟩ := h.1 0
    simp [masked_square_zero] at hv
  · rfl

/-- A probe may be undefined precisely on the discarded sign branch. -/
theorem excluded_negative_probe {y : ℝ} (hy : 0 < y) :
    (maskedAtoms (fun x => some (decide (0 < x))) square y).bind
      (fun atoms => integrate (presentation atoms) (fun x => if x < 0 then none else some 1)) = none := by
  rw [masked_square_positive _ hy]
  have hs := Real.sqrt_pos.mpr hy
  simp [hs, not_lt_of_ge hs.le, presentation, integrate, Value.add, Value.mul]

#qsym_check_axioms excluded_negative_probe
#qsym_check_axioms masked_square_rule
#qsym_check_axioms masked_square_mul_rule
#qsym_check_axioms critical_reconstruction_obstruction

private def intervalWeight := sourceWeight (Ioo 0 1)

/-- The legacy explicit bind still has a row-wise density observer. -/
private def legacySource : Option (D ℝ) :=
  bindValue lebesgueValue (some (fun x =>
    scaleValue (some (intervalWeight x)) (diracValue (some (square x)))))

private def chart := densityValue (some (marginalOn (Ioo 0 1) square))

theorem chart_at_quarter : densityAtValue chart (some (1/4)) = some 1 := by
  change densityAt (.density _ some) _ = _
  rw [densityAt_density, square_marginalOn_openUnit]
  norm_num [jac, Real.sqrt_div]

theorem open_endpoints :
    marginalOn (Ioo 0 1) square 0 = some 0 ∧ marginalOn (Ioo 0 1) square 1 = some 0 := by
  simp [square_marginalOn_openUnit]

theorem included_endpoints :
    marginalOn (Ico 0 1) square 0 = none ∧ marginalOn (Ioc 0 1) square 1 = some (1/2) := by
  constructor
  · rw [marginalOn, fibreOn_of_critical (x := 0) (by norm_num [mem_Ico])
      (by simp [square]) (by simp [deriv_square])]
    rfl
  · rw [square_marginalOn_positiveSource (fun _ hx => hx.1)]
    norm_num [jac, mem_Ioc]

/-- The old row-wise interpretation is a regression witness at a regular value. -/
theorem legacy_at_quarter : densityAtValue legacySource (some (1/4)) = none := by
  let row (x : ℝ) : D ℝ := .scale 1 (.scale (intervalWeight x) (.dirac (square x)))
  change (RealDensityFibre.mk 0 (partialIntegral volume
    (fun x => (realFibre (row x) (1/4)).density))).density = none
  rw [RealDensityFibre.density_eq, if_pos rfl]
  cases h : partialIntegral volume (fun x => (realFibre (row x) (1/4)).density) with
  | none => rfl
  | some a =>
    have bad := ((partialIntegral_defined_iff _ _).mp ⟨a, h⟩).1 (1/2)
    norm_num [row, realFibre, RealDensityFibre.density, RealDensityFibre.scale,
      square, intervalWeight, sourceWeight, mem_Ioo, Value.Defined, Value.mul] at bad
    obtain ⟨_, hv⟩ := bad
    cases hv

theorem no_presentation_rewrite : legacySource ≠ chart := by
  intro h
  have bad := legacy_at_quarter
  rw [h, chart_at_quarter] at bad
  contradiction

theorem unit_mass : pushforwardTest (Ioo 0 1) square (fun _ => some 1) = some 1 := by
  rw [pushforwardTest_total measurableSet_Ioo square (fun _ => 1)]
  · simp [Real.volume_Ioo, MeasureTheory.measureReal_def]
  · exact integrableOn_const.mpr (Or.inr (by simp [Real.volume_Ioo]))

/-- Correcting just the pointwise observer would still leave a difference:
the graph only evaluates a test at squares, but the current density chart
evaluates it even at a negative target where its coefficient vanishes. -/
private def probe (y : ℝ) : Option ℝ := if y < 0 then none else some 0

theorem source_probe : legacySource.bind (fun d => integrate d probe) = some 0 := by
  calc
    _ = pushforwardTest (Ioo 0 1) square probe := bind_masked_dirac_test _ _ _
    _ = _ := by
      have zero (x : ℝ) : probe (square x) = some 0 := if_neg (not_lt_of_ge (sq_nonneg x))
      simp [pushforwardTest, zero, Value.mul, partialIntegral, Value.Defined]

theorem chart_probe : chart.bind (fun d => integrate d probe) = none := by
  let body := fun y => Value.mul (marginalOn (Ioo 0 1) square y) (probe y)
  change partialIntegral volume body = none
  cases h : partialIntegral volume body with
  | none => rfl
  | some a =>
    have bad := ((partialIntegral_defined_iff _ _).mp ⟨a, h⟩).1 (-1)
    norm_num [body, square_marginalOn_openUnit, probe, Value.mul, Value.Defined] at bad
    obtain ⟨_, hv⟩ := bad
    cases hv

theorem real_graph_partial_probe :
    (realPushforwardOnValue (some (fun x => some (decide (x ∈ Ioo (0 : ℝ) 1))))
      (some (fun x => some (square x)))).bind (fun d => integrate d probe) = none := by
  rw [square_positiveSource_lebesgue _ (fun _ hx => hx.1)]
  exact chart_probe

theorem critical_graph_preserves_hole :
    densityAtValue (realPushforwardOnValue (some (fun x => some (decide (x ∈ Ico (0 : ℝ) 1))))
      (some (fun x => some (square x)))) (some 0) = none := by
  change densityAt (inLebesgueCoordinates _) 0 = none
  rw [coordinates_density]
  exact (pushforwardOn_density _ square (measurable_id.pow_const 2) 0).trans included_endpoints.1

private def explicitBind (s : Set ℝ) :=
  realBindValue lebesgueValue (some fun x =>
    scaleValue (some (sourceWeight s x)) (diracValue (some (square x))))

private theorem explicitBind_eq_graph (s : Set ℝ) [DecidablePred (· ∈ s)] :
    explicitBind s = realPushforwardOnValue (some fun x => some (decide (x ∈ s)))
      (some fun x => some (square x)) := by
  rw [explicitBind, realBind_dirac]
  apply congrArg (fun w => some (inLebesgueCoordinates (.density w (fun x => some (square x)))))
  funext x
  by_cases h : x ∈ s <;> simp [sourceWeight, Value.mask, h]

theorem explicitBind_eq_chart : explicitBind (Ioo 0 1) = chart := by
  rw [explicitBind_eq_graph, square_positiveSource_lebesgue _ (fun _ hx => hx.1)]
  rfl

theorem explicitBind_at_quarter : densityAtValue (explicitBind (Ioo 0 1)) (some (1/4)) = some 1 :=
  by rw [explicitBind_eq_chart]; exact chart_at_quarter

theorem explicitBind_probe : (explicitBind (Ioo 0 1)).bind (fun d => integrate d probe) = none :=
  by rw [explicitBind_eq_chart]; exact chart_probe

theorem explicitBind_critical : densityAtValue (explicitBind (Ico 0 1)) (some 0) = none := by
  rw [explicitBind_eq_graph]
  exact critical_graph_preserves_hole

/-- A bad row is visible even when it occurs at just one parameter. -/
theorem missing_row (f : ℝ → D ℝ) (h : f 0 = .invalid) :
    realIntegralRows f = .integral f :=
  realIntegralRows_of_missing (r := 0) (by rw [h]; rfl)

#qsym_check_axioms explicitBind_at_quarter
#qsym_check_axioms explicitBind_probe
#qsym_check_axioms explicitBind_critical
#qsym_check_axioms missing_row
#qsym_check_axioms realIntegralRows_partial
#qsym_check_axioms realBind_mass
#qsym_check_axioms realIntegral_dirac
#qsym_check_axioms realBind_weight_dirac
#qsym_check_axioms square_positiveSource_lebesgue
#qsym_check_axioms coordinates_of_missing_density
#qsym_check_axioms coordinates_partial
#qsym_check_axioms coordinates_test
#qsym_check_axioms real_graph_partial_probe
#qsym_check_axioms critical_graph_preserves_hole
#qsym_check_axioms pushforwardOn_density
#qsym_check_axioms mass_pushforwardOn_total
#qsym_check_axioms pushforwardOn_test
#qsym_check_axioms square_marginalOn_openUnit
#qsym_check_axioms square_positiveSource_test
#qsym_check_axioms bind_masked_dirac_test
#qsym_check_axioms square_positiveSource_integral
#qsym_check_axioms chart_at_quarter
#qsym_check_axioms open_endpoints
#qsym_check_axioms included_endpoints
#qsym_check_axioms legacy_at_quarter
#qsym_check_axioms no_presentation_rewrite
#qsym_check_axioms unit_mass
#qsym_check_axioms source_probe
#qsym_check_axioms chart_probe

end QSym.Distribution.RestrictedSquareTests
