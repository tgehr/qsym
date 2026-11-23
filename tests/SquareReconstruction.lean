import QSym.DistributionGraphBridge
import QSym.AxiomCheck
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
namespace QSym.Distribution.SquareReconstructionTests
open GraphFibre MeasureTheory

private abbrev kernel (p : ℝ → Option Bool) (y : ℝ) :=
  (maskedKernel (some p) (some fun x => some (square x))).bind (fun k => k y)

private abbrev reconstruct (p : ℝ → Option Bool) (h : ℝ → ℝ → Option ℝ) :=
  (partialIntegral volume (squareReconstructionRows
    (Value.mul (Value.mask (p 0) (some 1)) (h 0 0)) (kernel p) h)).map (fun v => v.1 + v.2)

theorem reconstruction_rule (p : ℝ → Option Bool) (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mul (Value.mask (p x) (some 1)) (h x (square x))) =
      reconstruct p h := by qsym_rule

theorem regular_rule (p : ℝ → Option Bool) (h : ℝ → ℝ → Option ℝ) :
    Value.Refines
      (partialIntegral volume (fun x => Value.mul (Value.mask (p x) (some 1)) (h x (square x))))
      (partialIntegral volume (squareRegularTest (Value.mul (Value.mask (p 0) (some 1)) (h 0 0))
        (kernel p) h)) := by qsym_rule

/-- A syntactically one-sided mask certifies the scalar rewrite for any
partial test, including one whose positive branch is nonintegrable. -/
theorem positive_mask_scalar_eq (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mul (Value.mask (some (decide (0 < x))) (some 1))
      (h x (square x))) =
      partialIntegral volume (squareRegularTest (Value.mul (Value.mask (some (decide (0 < (0 : ℝ))))
        (some 1)) (h 0 0)) (kernel (fun x => some (decide (0 < x)))) h) := by
  let f := fun x => (Value.mul (Value.mask (some (decide (0 < x))) (some 1))
    (h x (square x))).getD 0
  have half : IntegrableOn f (Set.Iic 0) ∨ IntegrableOn f (Set.Ioi 0) := by
    left
    have zero : Set.EqOn (fun _ : ℝ => (0 : ℝ)) f (Set.Iic 0) := by
      intro x hx
      have hn : ¬0 < x := not_lt_of_ge hx
      cases hv : h x (square x) <;> simp [f, hn, Value.mask, Value.mul, hv]
    exact integrableOn_zero.congr_fun zero measurableSet_Iic
  qsym_rule

theorem active_critical_zero_test :
    kernel (fun _ => some true) 0 = none ∧
    reconstruct (fun _ => some true) (fun _ _ => some 0) = some 0 := by
  constructor
  · rw [kernel, maskedKernel_total _ square (measurable_id.pow_const 2)]
    simp [masked_square_zero]
  · rw [← reconstruction_rule]
    simpa [Value.mul, Value.mask] using partialIntegral_zero (volume : Measure ℝ)

theorem excluded_missing_test (a : ℝ) :
    reconstruct (fun _ => some false) (fun x _ => if x = a then none else some 0) = none := by
  rw [← reconstruction_rule]
  unfold partialIntegral
  split
  · rename_i h
    obtain ⟨_, bad⟩ := h.1 a
    simp [Value.mul] at bad
  · rfl

theorem missing_critical_mask :
    reconstruct (fun x => if x = 0 then none else some false) (fun _ _ => some 0) = none := by
  rw [← reconstruction_rule]
  unfold partialIntegral
  split
  · rename_i h
    obtain ⟨_, bad⟩ := h.1 0
    simp [Value.mask, Value.mul] at bad
  · rfl

theorem open_unit_mass :
    reconstruct (fun x => some (decide (x ∈ Set.Ioo (0 : ℝ) 1))) (fun _ _ => some 1) = some 1 := by
  rw [← reconstruction_rule]
  let s := Set.Ioo (0 : ℝ) 1
  have weight (x : ℝ) : Value.mul (Value.mask (some (decide (x ∈ s))) (some (1 : ℝ))) (some 1) =
      some (s.indicator (fun _ => (1 : ℝ)) x) := by
    by_cases hx : x ∈ s <;> simp [hx, Value.mask, Value.mul, Set.indicator]
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s := by
    apply integrableOn_const.mpr (Or.inr _)
    simp [s, Real.volume_Ioo]
  change partialIntegral volume (fun x => Value.mul (Value.mask (some (decide (x ∈ s))) (some 1)) (some 1)) = _
  rw [funext weight]
  have hs : MeasurableSet s := measurableSet_Ioo
  simp [partialIntegral, Value.Defined, integrable_indicator_iff hs, integral_indicator hs, hi,
    s, MeasureTheory.measureReal_def, Real.volume_Ioo]

private def signTest (x _ : ℝ) := some (if x < 0 then (-1 : ℝ) else 1)

/-- Each regular fibre sums to zero. The absolute source integrand is one
on the entire line, so reconstruction must still report nonintegrability. -/
theorem signed_cancellation :
    reconstruct (fun _ => some true) signTest = none ∧
    partialIntegral volume (squareRegularTest (some 1) (kernel (fun _ => some true)) signTest) =
      some 0 := by
  constructor
  · rw [← reconstruction_rule]
    apply partialIntegral_invalid
    intro hi
    have absOne : (fun x : ℝ => ‖(Value.mul (Value.mask (some true) (some (1 : ℝ)))
        (signTest x (square x))).getD 0‖) = fun _ => 1 := by
      funext x
      by_cases hx : x < 0 <;> simp [Value.mask, Value.mul, signTest, hx]
    have absInt := hi.norm
    rw [absOne] at absInt
    simp [integrable_const_iff, isFiniteMeasure_iff, Real.volume_univ] at absInt
  · have zero (y : ℝ) :
        squareRegularTest (some 1) (kernel (fun _ => some true)) signTest y = some 0 := by
      rcases lt_trichotomy y 0 with hn | rfl | hp
      · simp [squareRegularTest, hn.ne, kernel, maskedKernel_total _ square (measurable_id.pow_const 2),
          masked_square_negative _ hn, presentation, integrate]
      · simp [squareRegularTest]
      · have hs := Real.sqrt_pos.mpr hp
        simp [squareRegularTest, hp.ne', kernel, maskedKernel_total _ square (measurable_id.pow_const 2),
          masked_square_positive _ hp, presentation, integrate, signTest, hs, not_lt_of_gt hs,
          Value.mul, Value.add]
    rw [funext zero]
    exact partialIntegral_zero _

#qsym_check_axioms reconstruction_rule
#qsym_check_axioms regular_rule
open Classical in
theorem affine_square_chart (s : Set ℝ) (hs : MeasurableSet s) (t : ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) :
    partialIntegral volume (fun x => some (if x ∈ s then t ((a*x+b)^2) else 0)) =
      partialIntegral volume (fun y => some
        (squareChartWeight ((fun u => (u-b)/a) ⁻¹' s) y * |a|⁻¹ * t y)) := by
  qsym_rule

theorem unequal_branch_weights (w t : ℝ → ℝ) (hm : Measurable w) (hs : ∀ x, 0 ≤ w (-x) * w x) :
    partialIntegral volume (fun x => some (w x * t (square x))) =
      partialIntegral volume (fun y => some (weightedSquareDensity w y * t y)) := by qsym_rule

theorem unequal_branch_density (w : ℝ → ℝ) (y : ℝ) :
    densityAt (.density (fun x => some (w x)) (fun x => some (square x))) y =
      (if y = 0 ∧ w 0 ≠ 0 then none else some (weightedSquareDensity w y)) := by qsym_rule

theorem unequal_branch_chart (w : ℝ → ℝ) (h0 : w 0 = 0) (hm : Measurable w) (hs : ∀ x, 0 ≤ w (-x) * w x) :
    inLebesgueCoordinates (.density (fun x => some (w x)) (fun x => some (square x))) =
      .density (fun y => some (weightedSquareDensity w y)) some := by qsym_rule

/-- Opposite branch weights cancel in every density query. The constant
test still detects the nonintegrable source. -/
theorem odd_weight_cancellation :
    let d := inLebesgueCoordinates (.density some (fun x => some (square x)))
    (∀ y, densityAt d y = some 0) ∧ integrate d (fun _ => some 1) = none := by
  dsimp only
  constructor
  · intro y
    rw [coordinates_density]
    simpa [weightedSquareDensity] using weighted_square_density (fun x => x) y
  · rw [coordinates_test _ (fun _ => 1)]
    apply partialIntegral_invalid
    intro h
    have hi : Integrable (fun x : ℝ => x) := by simpa [Value.mul] using h
    exact not_integrableOn_Ioi_rpow 1 (by simpa using (hi.integrableOn (s := Set.Ioi 0)))

#qsym_check_axioms unequal_branch_weights
#qsym_check_axioms unequal_branch_density
#qsym_check_axioms unequal_branch_chart
#qsym_check_axioms odd_weight_cancellation
#qsym_check_axioms affine_square_chart
#qsym_check_axioms positive_mask_scalar_eq
#qsym_check_axioms active_critical_zero_test
#qsym_check_axioms open_unit_mass
#qsym_check_axioms missing_critical_mask
#qsym_check_axioms excluded_missing_test
#qsym_check_axioms signed_cancellation

theorem unrestricted_image (a b : ℝ) (ha : a ≠ 0) (t : ℝ → Option ℝ) :
    integrate (inLebesgueCoordinates (affineSquareSource a b)) t =
      imageIntegral volume (Set.Ici 0) (affineSquareIntegralWeight a) t := by qsym_rule

theorem unrestricted_critical (a b : ℝ) (ha : a ≠ 0) :
    densityAt (inLebesgueCoordinates (affineSquareSource a b)) 0 = none := by qsym_rule

theorem missing_test_point (p : ℝ) :
    integrate (inLebesgueCoordinates (affineSquareSource (-2) 1))
      (fun y => if y = p then none else some 0) = if p < 0 then some 0 else none := by
  rw [unrestricted_image _ _ (by norm_num)]
  by_cases hp : p < 0
  · have hd (y : ℝ) (hy : y ∈ Set.Ici (0 : ℝ)) :
        Value.Defined (if y = p then none else some (0 : ℝ)) := by
      simp [ne_of_gt (hp.trans_le hy), Value.Defined]
    have zero (y : ℝ) : (if y = p then none else some (0 : ℝ)).getD 0 = 0 := by
      split <;> rfl
    rw [imageIntegral, if_pos hd, if_pos hp]
    simpa [zero] using (partialIntegral_zero (volume : Measure ℝ))
  · have bad : ¬ ∀ y ∈ Set.Ici (0 : ℝ), Value.Defined (if y = p then none else some (0 : ℝ)) := by
      intro h
      simpa [Value.Defined] using h p (le_of_not_gt hp)
    rw [imageIntegral, if_neg bad, if_neg hp]

#qsym_check_axioms unrestricted_image
#qsym_check_axioms unrestricted_critical
#qsym_check_axioms missing_test_point

theorem all_active_observer (f : ℝ → ℝ) (hf : Measurable f) (y : Option ℝ) :
    densityAtValue (realPushforwardOnValue (some fun _ => some true) (some fun x => some (f x))) y =
      marginal (some fun x => some (f x)) y := by qsym_rule

theorem closed_mask_pairing (t : ℝ → Option ℝ) :
    integrate (inLebesgueCoordinates (affineSquareSource (-2) 1)) t =
      imageIntegral volume (Set.Ici 0)
        (fun y => (unrestrictedSquareDensity (some |(-2 : ℝ)|⁻¹) (some y)).getD 0) t := by
  have ha : (-2 : ℝ) ≠ 0 := by norm_num
  qsym_rule

/-- A missing coefficient in an ordinary Lebesgue chart fails even the zero
test. The affine-square graph returns zero for the same test. -/
theorem critical_weight_zero_test (a b : ℝ) (w : ℝ → Option ℝ) (hw : w 0 = none) :
    integrate (inLebesgueCoordinates (affineSquareSource a b)) (fun _ => some 0) = some 0 ∧
    integrate (.density w some) (fun _ => some 0) = none := by
  constructor
  · rw [coordinates_test _ (fun _ => 0)]
    simpa [affineSquareSource, integrate, Value.mul] using (partialIntegral_zero (volume : Measure ℝ))
  · change partialIntegral volume _ = none
    unfold partialIntegral
    split
    · rename_i h
      simpa [hw, Value.Defined, Value.mul] using h.1 0
    · rfl

#qsym_check_axioms all_active_observer
#qsym_check_axioms closed_mask_pairing
#qsym_check_axioms critical_weight_zero_test

theorem inverse_radius_partial {c : ℝ} {r f : ℝ → Option ℝ}
    (h : ∀ x y, r y = some |x-c| ↔ f x = some y) : radiusOutput c r = f := by qsym_rule

theorem inverse_radius_distribution {c : ℝ} {r f : ℝ → Option ℝ}
    (h : ∀ x y, r y = some |x-c| ↔ f x = some y) :
    realPushforwardOnValue (some fun _ => some true) (some f) =
      radiusImageValue (some c) (some r) := by qsym_rule

theorem inverse_radius_pairing (a b : ℝ) (ha : a ≠ 0) (t : ℝ → Option ℝ) :
    (radiusImageValue (some (-b/a)) (some (sqrtRadius (some |a|⁻¹)))).bind
        (fun d => integrate d t) =
      imageIntegral volume (Set.Ici 0)
        (fun y => (unrestrictedSquareDensity (some |a|⁻¹) (some y)).getD 0) t := by qsym_rule

#qsym_check_axioms inverse_radius_distribution
#qsym_check_axioms inverse_radius_partial
#qsym_check_axioms inverse_radius_pairing

theorem restrict_chart_rule (f : ℝ → ℝ) (hf : Measurable f) (s : Set ℝ) [DecidablePred (· ∈ s)]
    (z : ℝ) (active : z ∈ s)
    (bad : densityAtValue (pushforwardOnValue (some fun _ => some true)
      (some fun x => some (f x))) (some z) = none) :
    realPushforwardOnValue (some fun x => some (decide (f x ∈ s))) (some fun x => some (f x)) =
      weightValue (some (fun y => Value.mask (some (decide (y ∈ s))) (some (1 : ℝ))))
        (realPushforwardOnValue (some fun _ => some true) (some fun x => some (f x))) := by qsym_rule

#qsym_check_axioms restrict_chart_rule

private def squareBranches (right : Bool) (y : ℝ) : Option ℝ :=
  if 0 ≤ y then some (if right then √y else -√y) else none

private theorem branches_inverse (x y : ℝ) :
    (∃ i, squareBranches i y = some x) ↔ square x = y := by
  by_cases h : 0 ≤ y
  · have eq := Real.sq_sqrt h
    constructor
    · rintro ⟨i,hi⟩
      cases i <;> simp [squareBranches, h] at hi <;> subst x <;> simpa [square] using eq
    · intro hx
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hx.trans eq.symm) with e | e
      · exact ⟨true, by simp [squareBranches, h, e]⟩
      · exact ⟨false, by simp [squareBranches, h, e]⟩
  · simp [squareBranches, h, ne_of_gt ((lt_of_not_ge h).trans_le (sq_nonneg x)), square]

/-- The overlap at zero belongs to the left summand. Both scalar observers
agree with ordinary distribution addition, even for a test missing at zero. -/
theorem square_inverse_sum :
    chartObservations (inverseCoverValue (some squareBranches)) = chartObservations
      (addValue (inversePartValue squareBranches (fun x => decide (x ∈ Set.Iic 0)))
        (inversePartValue squareBranches (fun x => decide (x ∈ (Set.Iic 0)ᶜ)))) := by
  have hd (x : ℝ) : HasStrictDerivAt square (2*x) x := by
    simpa [square] using hasStrictDerivAt_pow 2 x
  have roots (y : ℝ) : ∃ xs, RootCover Set.univ square y xs := by
    rcases lt_trichotomy y 0 with h | rfl | h
    · exact ⟨[], squareCover_negative id h⟩
    · exact ⟨[0], by constructor <;> simp [List.Sorted, square]⟩
    · have r := square_positive_roots h
      exact ⟨_, r.sorted, fun x => by simpa using r.complete x⟩
  have bad := affine_square_critical_density 1 0 one_ne_zero
  rw [coordinates_density] at bad
  have critical : densityAt (.density (fun _ => some 1) (fun x => some (square x))) 0 = none := by
    simpa only [affineSquareSource, one_mul, add_zero, square] using bad
  have hf : Measurable square := measurable_id.pow_const 2
  have hs : MeasurableSet (Set.Iic (0 : ℝ)) := measurableSet_Iic
  have inverse := branches_inverse
  qsym_rule

/-- Ambiguity is between distinct targets, not between labels for the same target. -/
theorem repeated_coordinate : inverseCoverOutput (fun (_ : Bool) y => some y) = some := by
  apply inverseCoverOutput_eq
  simp [eq_comm]

theorem ambiguous_coordinate : inverseCoverOutput (fun (_ : Unit) (_ : ℝ) => some 0) 0 = none := by
  unfold inverseCoverOutput
  apply dif_neg
  rintro ⟨y,_,h⟩
  have a := h 0 ⟨(), rfl⟩
  have b := h 1 ⟨(), rfl⟩
  linarith

theorem positive_inverse_alone :
    (inverseCoverValue (some (fun (_ : Unit) => squareBranches true))).bind
      (fun d => integrate d (fun _ => some 0)) = none := by
  apply inverseCover_missing_zero_test (x := -1)
  intro _ y
  by_cases hy : 0 ≤ y <;> simp [squareBranches, hy]
  linarith [Real.sqrt_nonneg y]

#qsym_check_axioms positive_inverse_alone
#qsym_check_axioms square_inverse_sum
#qsym_check_axioms repeated_coordinate
#qsym_check_axioms ambiguous_coordinate
#qsym_check_axioms affineSquare_not_presentation_add

end QSym.Distribution.SquareReconstructionTests
