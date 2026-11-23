import QSym.DistributionGraphBridge

/-! Affine images of weighted Lebesgue sources. A row of point masses with
a total weight and a rational affine output is one weighted parameter space;
a nonzero slope gives it Lebesgue coordinates, with the weight evaluated at
the inverse point and the constant Jacobian. The weight is arbitrary: no
measurability is needed, since the change of variables is applied to the
weighted test itself. A weight that is missing anywhere keeps the ordered
integral in the model, so totality is a hypothesis. -/
noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory

/-- The parameter chart of a weighted affine graph is a Lebesgue density. -/
theorem affine_weighted_coordinates (w : ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) :
    inLebesgueCoordinates (.density (fun x => some (w x)) (fun x => some (a*x+b))) =
      .density (fun y => some (w ((y-b)/a) * |a|⁻¹)) some := by
  classical
  apply inLebesgueCoordinates_of_chart
  constructor
  · funext y
    by_cases hi : (fun x : ℝ => some (a*x+b)) = some
    · have h0 : b = 0 := by simpa using congrFun hi 0
      have h1 : a = 1 := by simpa [h0] using congrFun hi 1
      subst h0 h1
      simp [densityAt, realFibre, RealDensityFibre.density]
    · have hm : Measurable (fun x : ℝ => a*x+b) := by fun_prop
      simp only [densityAt, realFibre, hi, if_false, RealDensityFibre.density, if_true,
        chartDensity, Value.Defined, Option.some.injEq, exists_eq', implies_true,
        Option.getD_some, true_and, if_pos hm, affine_fibreOn _ a b ha, Option.some_bind]
      by_cases hz : w ((y-b)/a) = 0
      · simp [hz, observe]
      · simp [hz, observe, Value.mul, Value.add, mul_comm]
  · intro y
    exact ⟨_, rfl⟩
  · intro t
    change partialIntegral volume (fun x => Value.mul (some (w x)) (some (t (a*x+b)))) =
      partialIntegral volume (fun y => Value.mul (some (w ((y-b)/a) * |a|⁻¹)) (some (t y)))
    apply affine_integral a b ha
    intro x
    have inv : (a*x+b-b)/a = x := by field_simp [ha]
    simp only [inv, Value.mul, Option.some.injEq]
    ring

private theorem affine_rows (rows : ℝ → D ℝ) (g : ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0)
    (h : ∀ r, atomRow (rows r) = some (g r, a*r+b)) :
    realIntegralRows rows = .density (fun y => some (g ((y-b)/a) * |a|⁻¹)) some := by
  rw [realIntegralRows_of_atoms rows g (fun r => a*r+b) h, affine_weighted_coordinates g a b ha]

private theorem affine_target (g : ℝ → ℝ) (w : ℝ → Option ℝ) (hg : ∀ x, w x = some (g x))
    (a b j : ℚ) {i : ℝ → Option ℝ} {v : Option ℝ} (hj : j = |a⁻¹|)
    (hi : StepSource.Affine i a⁻¹ (-b/a)) (hv : v = some (j : ℝ)) :
    some (Presentation.density (fun y => some (g ((y-(b : ℝ))/(a : ℝ)) * |(a : ℝ)|⁻¹)) some) =
      weightValue (some (fun y => Value.mul ((i y).bind w) v)) lebesgueValue := by
  subst hv hj
  simp only [weightValue, lebesgueValue, densityValue, Option.some_bind, weight, Value.mul_one_left]
  apply congrArg (fun w => some (Presentation.density w some))
  funext y
  have inverse : ((a : ℝ))⁻¹*y + -(b : ℝ)/a = (y-b)/a := by ring
  simp only [Option.some_bind, Value.mul_one_left, hi.equation, hg, Value.mul, Rat.cast_inv,
    Rat.cast_div, Rat.cast_neg, Rat.cast_abs, abs_inv, inverse, one_mul]

/-- An ordered real integral of weighted point masses on an affine graph. -/
theorem integral_affine_weighted_rule (w : ℝ → Option ℝ) (hw : ∀ x, Value.Defined (w x))
    (a b j : ℚ) {f i : ℝ → Option ℝ} {v : Option ℝ}
    (ha : a ≠ 0) (hj : j = |a⁻¹|) (hf : StepSource.Affine f a b)
    (hi : StepSource.Affine i a⁻¹ (-b/a)) (hv : v = some (j : ℝ)) :
    realIntegralValue (some fun x => scaleValue (w x) (diracValue (f x))) =
      weightValue (some (fun y => Value.mul ((i y).bind w) v)) lebesgueValue := by
  choose g hg using hw
  have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [← affine_target g w hg a b j hj hi hv]
  apply congrArg some
  apply affine_rows _ g a b hn
  intro r
  simp [hg, hf.equation, scaleValue, diracValue, atomRow, Value.mul]

/-- The same rows below a bind of the Lebesgue reference. -/
theorem bind_affine_weighted_rule (w : ℝ → Option ℝ) (hw : ∀ x, Value.Defined (w x))
    (a b j : ℚ) {f i : ℝ → Option ℝ} {v : Option ℝ}
    (ha : a ≠ 0) (hj : j = |a⁻¹|) (hf : StepSource.Affine f a b)
    (hi : StepSource.Affine i a⁻¹ (-b/a)) (hv : v = some (j : ℝ)) :
    realBindValue lebesgueValue (some fun x => scaleValue (w x) (diracValue (f x))) =
      weightValue (some (fun y => Value.mul ((i y).bind w) v)) lebesgueValue := by
  choose g hg using hw
  have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [← affine_target g w hg a b j hj hi hv]
  apply congrArg some
  apply affine_rows _ g a b hn
  intro r
  simp [hg, hf.equation, scaleValue, diracValue, atomRow, Value.mul]

/-- A weighted Lebesgue source bound to a point mass on an affine graph. -/
theorem weighted_bind_affine_weighted_rule (w : ℝ → Option ℝ) (hw : ∀ x, Value.Defined (w x))
    (a b j : ℚ) {f i : ℝ → Option ℝ} {v : Option ℝ}
    (ha : a ≠ 0) (hj : j = |a⁻¹|) (hf : StepSource.Affine f a b)
    (hi : StepSource.Affine i a⁻¹ (-b/a)) (hv : v = some (j : ℝ)) :
    realBindValue (weightValue (some w) lebesgueValue) (some fun x => diracValue (f x)) =
      weightValue (some (fun y => Value.mul ((i y).bind w) v)) lebesgueValue := by
  choose g hg using hw
  have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [← affine_target g w hg a b j hj hi hv]
  apply congrArg some
  apply affine_rows _ g a b hn
  intro r
  simp [hg, hf.equation, scaleValue, diracValue, atomRow, Value.mul]

end QSym.Distribution.GraphFibre
