import QSym.DistributionIntegralCertificate
import QSym.DistributionWeightedSquare
import QSym.DistributionAffine

noncomputable section
namespace QSym.Distribution.RootInterval
open MeasureTheory Set GraphFibre

private theorem standard (p q k : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) :
    partialIntegral volume (fun z => some (if p < z ∧ z < q then k / √z else 0)) =
      some (2*k*(√q-√p)) := by
  let w := (Ioo (√p) (√q)).indicator (fun _ : ℝ => 2*k)
  have neg (x : ℝ) (hx : x ≤ 0) : w x = 0 := by
    have h : ¬ √p < x := not_lt_of_ge (hx.trans (Real.sqrt_nonneg _))
    simp [w, Set.indicator, h]
  have same (x : ℝ) : 0 ≤ w (-x) * w x := by
    rcases le_total x 0 with h | h
    · simp [neg x h]
    · simp [neg (-x) (neg_nonpos.mpr h)]
  have transfer := weighted_square_integral w (measurable_const.indicator measurableSet_Ioo) same (fun _ => 1)
  simp only [mul_one] at transfer
  have row (z : ℝ) : weightedSquareDensity w z = if p < z ∧ z < q then k / √z else 0 := by
    by_cases hz : 0 < z
    · have hl : √p < √z ↔ p < z := by
        simpa only [Real.sq_sqrt hp, Real.sq_sqrt hz.le] using
          (sq_lt_sq₀ (Real.sqrt_nonneg p) (Real.sqrt_nonneg z)).symm
      have hr : √z < √q ↔ z < q := by
        simpa only [Real.sq_sqrt hz.le, Real.sq_sqrt (hp.trans hpq)] using
          (sq_lt_sq₀ (Real.sqrt_nonneg z) (Real.sqrt_nonneg q)).symm
      rw [weightedSquareDensity, if_pos hz, neg _ (neg_nonpos.mpr (Real.sqrt_nonneg _))]
      by_cases h : p < z ∧ z < q <;>
        simp [w, Set.indicator, hl, hr, h, jac, mul_inv_rev, div_eq_mul_inv,
          mul_assoc, mul_left_comm, mul_comm]
    · simp [weightedSquareDensity, hz, not_lt_of_ge ((le_of_not_gt hz).trans hp)]
  simp_rw [row] at transfer
  rw [← transfer]
  apply partialIntegral_interval _ _ _ _ [√p, √q] (Real.sqrt_le_sqrt hpq) (fun x => ⟨_,rfl⟩)
  intro x away
  have lp := (away _ (by simp : √p ∈ [√p, √q])).symm
  have rq := away _ (by simp : √q ∈ [√p, √q])
  simp [w, Set.indicator, lt_iff_le_and_ne, lp, rq]

/-- An affine inverse square root on a bounded interval. Pointwise totality
is required even at the endpoints. The integration formula permits finitely
many changes to defined values and either sign of the real coefficient. -/
theorem integral (a b l u k : ℝ) (ha : a ≠ 0) (hlu : l ≤ u)
    (hl : 0 ≤ a*l+b) (hu : 0 ≤ a*u+b) (w : ℝ → Option ℝ) (points : List ℝ)
    (total : ∀ y, Value.Defined (w y))
    (away : ∀ y, (∀ p ∈ points, y ≠ p) →
      w y = some (if l < y ∧ y < u then k / √(a*y+b) else 0)) :
    partialIntegral volume w = some ((2*k/a)*(√(a*u+b)-√(a*l+b))) := by
  rw [partialIntegral_congr_away w _ points total (fun y => ⟨_,rfl⟩) away]
  let L := a*l+b
  let U := a*u+b
  have change (p q : ℝ)
      (bounds : ∀ y, (p < a*y+b ∧ a*y+b < q) ↔ (l < y ∧ y < u)) :
      partialIntegral volume (fun y => some (if l < y ∧ y < u then k / √(a*y+b) else 0)) =
        partialIntegral volume (fun z => some (if p < z ∧ z < q then (k/|a|) / √z else 0)) := by
    apply affine_integral a b ha
    intro y
    rw [if_congr (bounds y) rfl rfl]
    split <;> simp [Value.mul, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc]
  rcases lt_or_gt_of_ne ha with hn | hp
  · have order : U ≤ L := add_le_add_right (mul_le_mul_of_nonpos_left hlu hn.le) b
    rw [change U L (fun y => by
      simp only [U, L, add_lt_add_iff_right, mul_lt_mul_left_of_neg hn, and_comm]),
      standard _ _ _ hu order, abs_of_neg hn]
    congr 1
    ring
  · have order : L ≤ U := add_le_add_right (mul_le_mul_of_nonneg_left hlu hp.le) b
    rw [change L U (fun y => by simp only [L, U, add_lt_add_iff_right, mul_lt_mul_left hp]),
      standard _ _ _ hl order, abs_of_pos hp]
    congr 1
    ring

end QSym.Distribution.RootInterval
