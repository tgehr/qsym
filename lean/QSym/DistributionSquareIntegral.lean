import QSym.DistributionGraph
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set

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

end QSym.Distribution.GraphFibre
