import QSym.DistributionSquareReconstruction

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set Classical

/-- Collapse two branch observations to their scalar sum, with the exact
reverse-integrability obligation needed to recover the first component. -/
theorem integral_pair_sum {X : Type} [MeasurableSpace X] {μ : Measure X} (f g : X → ℝ)
    (recover : Integrable (f + g) μ → Integrable f μ) :
    (partialIntegral μ (fun x => some (f x, g x))).map (fun z => z.1 + z.2) =
      partialIntegral μ (fun x => some (f x + g x)) := by
  have iff : Integrable (f + g) μ ↔ Integrable (fun x => (f x, g x)) μ := by
    rw [integrable_prod]
    constructor
    · intro h
      have hf := recover h
      exact ⟨hf, by simpa only [add_sub_cancel_left] using h.sub hf⟩
    · exact fun h => h.1.add h.2
  by_cases h : Integrable (f + g) μ
  · have hp := iff.mp h
    rw [partialIntegral_valid _ _ (fun x => ⟨_, rfl⟩) hp,
      partialIntegral_valid _ (fun x => some (f x + g x)) (fun x => ⟨_, rfl⟩) h]
    simp only [Option.getD_some, Option.map_some, Option.some.injEq]
    rw [integral_pair (integrable_prod.mp hp).1 (integrable_prod.mp hp).2,
      integral_add (integrable_prod.mp hp).1 (integrable_prod.mp hp).2]
    rfl
  · rw [partialIntegral_invalid _ _ (mt iff.mpr h), partialIntegral_invalid _ (fun x => some (f x + g x)) h]
    rfl

/-- Both branches see the same target test and Jacobian. On their overlap
each contributes half the sum; on the first branch alone it contributes all.
This recovers measurability even for an arbitrary total target test. -/
theorem integrable_masked_left {X : Type} [MeasurableSpace X] {μ : Measure X} {s r : Set X}
    (hs : MeasurableSet s) (hr : MeasurableSet r)
    (k : X → ℝ) (h : Integrable (s.indicator k + r.indicator k) μ) : Integrable (s.indicator k) μ := by
  classical
  let sum := s.indicator k + r.indicator k
  have eq : s.indicator k = s.indicator sum - (s ∩ r).indicator (fun x => (1/2 : ℝ) * sum x) := by
    funext x
    by_cases hx : x ∈ s <;> by_cases hy : x ∈ r <;>
      simp [sum, Set.indicator, hx, hy]
    ring
  rw [eq]
  exact (h.indicator hs).sub ((h.const_mul (1/2 : ℝ)).indicator (hs.inter hr))

/-- The whole-chart coefficient on a square graph. At zero this integral
representative agrees with the pointwise density when the source excludes
the critical point. -/
def squareChartWeight (s : Set ℝ) (y : ℝ) : ℝ :=
  if 0 < y then (if -√y ∈ s then jac y else 0) + (if √y ∈ s then jac y else 0) else 0

theorem square_masked_integral (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (t : ℝ → ℝ) :
    partialIntegral volume (fun x => some (if x ∈ s then t (x^2) else 0)) =
      partialIntegral volume (fun y => some (squareChartWeight s y * t y)) := by
  classical
  let neg := Ioi 0 ∩ (fun y : ℝ => -√y) ⁻¹' s
  let pos := Ioi 0 ∩ Real.sqrt ⁻¹' s
  let k := fun y => jac y * t y
  have hn : MeasurableSet neg := measurableSet_Ioi.inter (hs.preimage (by fun_prop))
  have hp : MeasurableSet pos := measurableSet_Ioi.inter (hs.preimage (by fun_prop))
  rw [square_pair_integral]
  calc
    _ = (partialIntegral volume (fun y => some (neg.indicator k y, pos.indicator k y))).map (fun z => z.1 + z.2) := by
      congr 2
      funext y
      by_cases hy : 0 < y
      · by_cases h₁ : -√y ∈ s <;> by_cases h₂ : √y ∈ s <;>
          simp [neg, pos, k, Set.indicator, mem_Ioi, hy, h₁, h₂, Real.sq_sqrt hy.le]
      · simp [neg, pos, Set.indicator, hy]
    _ = _ := by
      rw [integral_pair_sum _ _ (integrable_masked_left hn hp k)]
      congr 1
      funext y
      by_cases hy : 0 < y <;> by_cases h₁ : -√y ∈ s <;> by_cases h₂ : √y ∈ s <;>
        simp [neg, pos, k, squareChartWeight, Set.indicator, mem_Ioi, hy, h₁, h₂, add_mul]

/-- First move the affine source to the square's coordinates, then combine
both branches. No integrability or measurability premise on the test. -/
theorem affine_square_integral (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (a b : ℝ) (ha : a ≠ 0) (t : ℝ → ℝ) :
    partialIntegral volume (fun x => some (if x ∈ s then t ((a*x+b)^2) else 0)) =
      partialIntegral volume (fun y => some
        (squareChartWeight ((fun u => (u-b)/a) ⁻¹' s) y * |a|⁻¹ * t y)) := by
  let r := (fun u => (u-b)/a) ⁻¹' s
  have hr : MeasurableSet r := hs.preimage (by fun_prop)
  rw [show (fun y => some (squareChartWeight r y * |a|⁻¹ * t y)) =
      (fun y => some (squareChartWeight r y * (|a|⁻¹ * t y))) by funext y; rw [mul_assoc]]
  rw [← square_masked_integral r hr]
  apply affine_integral a b ha
  intro x
  have back : (a*x+b-b)/a = x := by field_simp [ha]
  have mem : a*x+b ∈ r ↔ x ∈ s := by change ((a*x+b-b)/a ∈ s) ↔ _; rw [back]
  by_cases hx : x ∈ s <;> simp [mem, hx, Value.mul]

end QSym.Distribution.GraphFibre
