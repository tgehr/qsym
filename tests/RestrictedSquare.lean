import QSym.DistributionSquareIntegral
import QSym.DistributionGraph
import QSym.AxiomCheck

noncomputable section
namespace QSym.Distribution.RestrictedSquareTests
open GraphFibre MeasureTheory Set

private def intervalWeight := sourceWeight (Ioo 0 1)

/-- The legacy explicit bind still has a row-wise density observer. -/
private def source : Option (D ℝ) :=
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

/-- Even at an interior regular target the legacy observer integrates an
undefined Dirac density. A distribution equality in the current exporter
would have to preserve this observation. -/
theorem source_at_quarter : densityAtValue source (some (1/4)) = none := by
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

theorem no_presentation_rewrite : source ≠ chart := by
  intro h
  have bad := source_at_quarter
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

theorem source_probe : source.bind (fun d => integrate d probe) = some 0 := by
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

theorem positive_chart_probe :
    (weightValue (some (marginalOn (Ioo 0 1) square)) positiveLebesgueValue).bind
      (fun d => integrate d probe) = some 0 := by
  rw [← square_positiveSource_chart _ (fun _ hx => hx.1), pushforwardOn_test]
  exact (bind_masked_dirac_test _ _ _).symm.trans source_probe

theorem positive_reference_sees_zero :
    positiveLebesgueValue.bind (fun d => integrate d (fun y => if y = 0 then none else some 0)) = none := by
  rw [positiveLebesgue_test, if_neg]
  intro h
  simpa [Value.Defined] using h.1 0 le_rfl

#qsym_check_axioms positiveLebesgue_test
#qsym_check_axioms positiveLebesgue_density
#qsym_check_axioms square_positiveSource_chart
#qsym_check_axioms positive_chart_probe
#qsym_check_axioms positive_reference_sees_zero
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
#qsym_check_axioms source_at_quarter
#qsym_check_axioms no_presentation_rewrite
#qsym_check_axioms unit_mass
#qsym_check_axioms source_probe
#qsym_check_axioms chart_probe

end QSym.Distribution.RestrictedSquareTests
