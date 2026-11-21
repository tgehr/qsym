import QSym.DistributionGraph
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set

open Classical in

/-- The square chart integrates against Lebesgue measure on the open positive
half-line. Its strict probes see the whole image of the parameter map,
including the endpoint of measure zero. -/
theorem positiveLebesgue_test (t : ℝ → Option ℝ) :
    positiveLebesgueValue.bind (fun d => integrate d t) =
      (if (∀ y ≥ 0, Value.Defined (t y)) ∧ IntegrableOn (fun y => (t y).getD 0) (Ioi 0)
       then some (∫ y in Ioi 0, (t y).getD 0) else none) := by
  classical
  let k := fun y => (t y).getD 0
  let g := fun x => |2*x| • k (square x)
  have image : square '' Ioi (0 : ℝ) = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact sq_pos_of_pos (show 0 < x from hx)
    · intro (hy : 0 < y)
      exact ⟨√y, Real.sqrt_pos.mpr hy, Real.sq_sqrt hy.le⟩
  have inj : InjOn square (Ioi 0) := by
    intro x (hx : 0 < x) z (hz : 0 < z) h
    simpa only [square, Real.sqrt_sq hx.le, Real.sqrt_sq hz.le] using congrArg Real.sqrt h
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt square (2*x) (Ioi 0) x := by
    intro x _
    simpa [square] using ((hasDerivAt_pow 2 x).hasDerivWithinAt (s := Ioi 0))
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd inj k
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd inj k
  rw [image] at hi he
  let b := fun x => Value.mul (some (positiveJacobian x)) (t (square x))
  have body : (fun x => (b x).getD 0) = (Ioi 0).indicator g := by
    funext x
    by_cases hx : 0 < x
    · have hp : 0 < 2*x := by positivity
      cases h : t (square x) <;> simp [b, g, k, Value.mul, positiveJacobian, indicator,
        mem_Ioi, hx, h, smul_eq_mul, abs_of_pos hp]
    · cases h : t (square x) <;> simp [b, positiveJacobian, Value.mul, indicator, mem_Ioi, hx, h]
  have dom : (∀ x, Value.Defined (b x)) ↔ ∀ y ≥ 0, Value.Defined (t y) := by
    have atX (x : ℝ) : Value.Defined (b x) ↔ Value.Defined (t (square x)) := by
      cases h : t (square x) <;> simp [b, Value.Defined, Value.mul, h]
    constructor
    · intro h y hy
      simpa only [square, Real.sq_sqrt hy] using (atX (√y)).mp (h _)
    · intro h x
      exact (atX x).mpr (h _ (sq_nonneg x))
  change partialIntegral volume b = _
  simp only [partialIntegral, dom, body, integrable_indicator_iff measurableSet_Ioi,
    integral_indicator measurableSet_Ioi]
  rw [← hi, ← he]

private theorem sqrt_substitution (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (fun y => jac y * g (√y)) (Ioi 0) ∧
    (∫ x in Ioi 0, g x) = ∫ y in Ioi 0, jac y * g (√y) := by
  have image : Real.sqrt '' Ioi (0 : ℝ) = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact Real.sqrt_pos.mpr hy
    · intro (hx : 0 < x)
      exact ⟨x^2, sq_pos_of_pos hx, Real.sqrt_sq (le_of_lt hx)⟩
  have inj : InjOn Real.sqrt (Ioi 0) := by
    intro x (hx : 0 < x) y (hy : 0 < y) h
    exact (Real.sq_sqrt hx.le).symm.trans ((congrArg (fun z : ℝ => z ^ 2) h).trans (Real.sq_sqrt hy.le))
  have derivS : ∀ y ∈ Ioi (0 : ℝ), HasDerivWithinAt Real.sqrt (jac y) (Ioi 0) y := by
    intro y hy
    simpa [jac, one_div] using (Real.hasDerivAt_sqrt (ne_of_gt hy)).hasDerivWithinAt (s := Ioi 0)
  have ha := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi derivS inj g
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi derivS inj g
  rw [image] at ha he
  have hj (y : ℝ) : |jac y| = jac y := abs_of_nonneg (by unfold jac; positivity)
  simpa only [hj, smul_eq_mul] using And.intro (ha.mp hg) he

/-- Change of variables for a measurable part of the positive square branch.
The test only needs to be integrable along the graph over the selected source. -/
theorem square_positiveSource_integral {s : Set ℝ} (hs : MeasurableSet s) (hp : s ⊆ Ioi 0)
    (k : ℝ → ℝ) (hk : IntegrableOn (fun x => k (square x)) s) :
    (∫ x in s, k (square x)) = ∫ y, (marginalOn s square y).getD 0 * k y := by
  classical
  let g := s.indicator (fun x => k (square x))
  have hg : Integrable g := hk.integrable_indicator hs
  obtain ⟨_, sub⟩ := sqrt_substitution g hg.integrableOn
  calc
    _ = ∫ x in Ioi 0, g x := by
      simp only [g, setIntegral_indicator hs, inter_eq_right.mpr hp]
    _ = ∫ y in Ioi 0, jac y * g (√y) := sub
    _ = _ := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with y
      rw [square_marginalOn_positiveSource hp]
      by_cases hy : 0 < y
      · by_cases hm : √y ∈ s <;>
          simp [g, Set.indicator, mem_Ioi, hy, hm, square, Real.sq_sqrt hy.le]
      · have hm : √y ∉ s := fun h => hy (Real.sqrt_pos.mp (hp h))
        simp [Set.indicator, mem_Ioi, hy, hm]

theorem square_positiveSource_test {s : Set ℝ} (hs : MeasurableSet s) (hp : s ⊆ Ioi 0)
    (k : ℝ → ℝ) (hk : IntegrableOn (fun x => k (square x)) s) :
    pushforwardTest s square (fun y => some (k y)) =
      some (∫ y, (marginalOn s square y).getD 0 * k y) := by
  rw [pushforwardTest_total hs square k hk, square_positiveSource_integral hs hp k hk]

/-- Reconstruction of the original joint graph for every integrable real test
on it. The target integral uses only regular values. -/
theorem square_disintegrates (h : ℝ → ℝ → ℝ) (hi : Integrable (fun x => h x (square x))) :
    (∫ x, h x (square x)) = ∫ y in Ioi 0,
      ((fibre square y).bind (fun atoms => observe atoms (fun x => some (h x y)))).getD 0 := by
  let g := fun x => h x (square x)
  have hneg : Integrable (fun x => g (-x)) := hi.comp_neg
  obtain ⟨ip,ep⟩ := sqrt_substitution g hi.integrableOn
  obtain ⟨im,em⟩ := sqrt_substitution (fun x => g (-x)) hneg.integrableOn
  calc
    _ = (∫ x in Iic 0, g x) + ∫ x in Ioi 0, g x :=
      (intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn).symm
    _ = (∫ y in Ioi 0, jac y * g (-√y)) + ∫ y in Ioi 0, jac y * g (√y) := by
      rw [← ep, ← em, integral_comp_neg_Ioi, neg_zero]
    _ = _ := by
      rw [← integral_add im ip]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [square_observe hy]
      simp [g, square, Value.add, Value.mul, Real.sq_sqrt (le_of_lt hy)]

/-- Testing only the target recovers the scalar pushforward. The value of the
pointwise marginal at the critical target is specified separately. -/
theorem square_marginal_integral (k : ℝ → ℝ) (hi : Integrable (fun x => k (square x))) :
    (∫ x, k (square x)) = ∫ y in Ioi 0,
      (marginal (some (fun x => some (square x))) (some y)).getD 0 * k y := by
  rw [square_disintegrates (fun _ y => k y) hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [square_observe hy, square_marginal_positive hy]
  simp [Value.add, Value.mul, jac]
  <;> ring

open Filter Topology in
/-- Every finite completion of the partial marginal diverges from the right
at zero. Assigning a value at the critical point cannot make it continuous. -/
theorem square_marginal_tendsto (fallback : ℝ) :
    Tendsto (fun y => (marginal (some (fun x => some (square x))) (some y)).getD fallback)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy using Real.sqrt_pos.mpr hy
  apply (tendsto_inv_nhdsGT_zero.comp hs).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [Function.comp_apply, square_marginal_positive hy]

end QSym.Distribution.GraphFibre
