import QSym.DistributionSquareChart
import QSym.DistributionRootCover

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set

/-- Each branch is a bounded measurable share of the sum. The common test
can have either sign and need not be measurable. The two coefficients may
both change sign, provided they agree in sign at each target. -/
theorem integral_pair_common_test {X : Type} [MeasurableSpace X] {μ : Measure X}
    (a b : X → ℝ) (ha : Measurable a) (hb : Measurable b) (hs : ∀ x, 0 ≤ a x * b x)
    (t : X → ℝ) :
    (partialIntegral μ (fun x => some (a x * t x, b x * t x))).map (fun z => z.1 + z.2) =
      partialIntegral μ (fun x => some ((a x + b x) * t x)) := by
  simp_rw [add_mul]
  apply integral_pair_sum
  intro h
  let r := fun x => a x / (a x + b x)
  have hr : Measurable r := ha.div (ha.add hb)
  have bound (x) : ‖r x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, show r x = _ from rfl, abs_div]
    by_cases hz : a x + b x = 0
    · simp [hz]
    · apply (div_le_one (abs_pos.mpr hz)).mpr
      rcases (mul_nonneg_iff.mp (hs x)) with ⟨pa,pb⟩ | ⟨na,nb⟩
      · rw [abs_of_nonneg pa, abs_of_nonneg (add_nonneg pa pb)]; linarith
      · rw [abs_of_nonpos na, abs_of_nonpos (add_nonpos na nb)]; linarith
  have eq (x) : r x * (a x * t x + b x * t x) = a x * t x := by
    rw [← add_mul]
    by_cases hz : a x + b x = 0
    · have az : a x = 0 := by
        rcases mul_nonneg_iff.mp (hs x) with h | h <;> linarith [h.1,h.2]
      rw [hz, az]; simp
    · dsimp [r]; field_simp; ring
  exact (h.bdd_mul hr.aestronglyMeasurable ⟨1,bound⟩).congr (Filter.Eventually.of_forall eq)

def weightedSquareDensity (w : ℝ → ℝ) (y : ℝ) : ℝ :=
  if 0 < y then (w (-√y) + w (√y)) * jac y else 0

/-- Transport the strict finite integral through the square even when the
two inverse points carry different signed weights. -/
theorem weighted_square_integral (w : ℝ → ℝ) (hm : Measurable w) (hs : ∀ x, 0 ≤ w (-x) * w x)
    (t : ℝ → ℝ) : partialIntegral volume (fun x => some (w x * t (square x))) =
      partialIntegral volume (fun y => some (weightedSquareDensity w y * t y)) := by
  let k := fun y => if 0 < y then jac y * t y else 0
  rw [square_pair_integral]
  calc
    _ = (partialIntegral volume (fun y => some (w (-√y) * k y, w (√y) * k y))).map (fun z => z.1 + z.2) := by
      congr 2
      funext y
      by_cases hy : 0 < y
      · simp [square, k, hy, Real.sq_sqrt hy.le, mul_left_comm]
      · simp [k, hy]
    _ = _ := by
      rw [integral_pair_common_test (fun y => w (-√y)) (fun y => w (√y))
        (hm.comp (by fun_prop)) (hm.comp (by fun_prop)) (fun y => hs (√y))]
      congr 1
      funext y
      by_cases hy : 0 < y <;> simp [k, weightedSquareDensity, hy, mul_assoc]

/-- A vanishing critical weight removes its root before regularity is
tested. At a positive target the two remaining contributions are ordinary
weighted regular roots, including when one of them has weight zero. -/
theorem weighted_square_density (w : ℝ → ℝ) (y : ℝ) :
    densityAt (.density (fun x => some (w x)) (fun x => some (square x))) y =
      (if y = 0 ∧ w 0 ≠ 0 then none else some (weightedSquareDensity w y)) := by
  classical
  have ne : (fun x => some (square x)) ≠ some := by
    intro he; have := congrFun he (-1); norm_num [square] at this
  have hm : Measurable square := measurable_id.pow_const 2
  simp only [densityAt, realFibre, ne, if_false, RealDensityFibre.density, chartDensity,
    Value.Defined, Option.some.injEq, exists_eq', implies_true, Option.getD_some, hm, and_self, if_true]
  rcases lt_trichotomy y 0 with hn | rfl | hp
  · rw [fibreOn_of_notMem_image (by rintro ⟨x, _, rfl⟩; exact (not_lt_of_ge (sq_nonneg x)) hn)]
    simp [weightedSquareDensity, not_lt_of_gt hn, hn.ne, observe]
  · by_cases h0 : w 0 = 0
    · rw [fibreOn_of_notMem_image (by
        rintro ⟨x, hx, hz⟩
        have eq : x = 0 := by simpa [square] using hz
        exact hx (by simp [eq,h0]))]
      simp [weightedSquareDensity, h0, observe]
    · have active : (0 : ℝ) ∈ {x | some (w x) ≠ some 0} := by simpa using h0
      rw [fibreOn_of_critical active (show square 0 = 0 by simp [square]) (by simp [deriv_square])]
      simp [h0]
  · have roots := square_positive_roots hp
    have cover : RootCover univ square y [-√y,√y] :=
      ⟨roots.sorted, fun x => by simpa only [mem_univ, true_and] using roots.complete x⟩
    rw [cover.observe_weighted (fun x => some (w x)) (fun x => 2*x) (fun x _ _ => by
      simpa [square] using hasStrictDerivAt_pow 2 x)]
    have sp := Real.sqrt_pos.mpr hp
    by_cases n : w (-√y) = 0 <;> by_cases p : w (√y) = 0 <;>
      simp [weightedSquareDensity, hp, hp.ne', n, p, Value.add, Value.inv, Value.mul, abs_mul, abs_of_pos sp,
        sp.ne', jac, add_mul, mul_comm]
    ring

theorem weighted_square_chart (w : ℝ → ℝ) (h0 : w 0 = 0) (hm : Measurable w)
    (hs : ∀ x, 0 ≤ w (-x) * w x) :
    inLebesgueCoordinates (.density (fun x => some (w x)) (fun x => some (square x))) =
      .density (fun y => some (weightedSquareDensity w y)) some := by
  apply inLebesgueCoordinates_of_chart
  exact ⟨funext (fun y => by simpa [h0] using weighted_square_density w y), fun _ => ⟨_,rfl⟩, weighted_square_integral w hm hs⟩

end QSym.Distribution.GraphFibre
