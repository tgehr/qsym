import QSym.DistributionGraph
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section
namespace QSym.Distribution.GraphFibre
open Set MeasureTheory

private theorem affine_derivative (a b x : ℝ) :
    HasStrictDerivAt (fun u : ℝ => a*u+b) a x := by
  simpa using ((hasStrictDerivAt_id x).const_mul a).add_const b

open Classical in
/-- A nonzero slope has exactly one possible active preimage, including at
endpoints and isolated holes of the source set. -/
theorem affine_fibreOn (s : Set ℝ) (a b : ℝ) (ha : a ≠ 0) (y : ℝ) :
    fibreOn s (fun x => a*x+b) y =
      some (if (y-b)/a ∈ s then [((y-b)/a, |a|⁻¹)] else []) := by
  classical
  let z := (y-b)/a
  have root (x : ℝ) : x = z ↔ a*x+b = y := by
    rw [eq_div_iff ha]
    constructor <;> intro h <;> linarith [mul_comm x a]
  have hd (x : ℝ) : deriv (fun u : ℝ => a*u+b) x = a := (affine_derivative a b x).hasDerivAt.deriv
  by_cases hz : z ∈ s
  · have roots : RegularRootList (fun x => a*x+b) (fun x => x ∈ s ∧ a*x+b = y) [z] := by
      constructor
      · simp [List.Sorted]
      · intro x
        simp only [List.mem_singleton]
        exact ⟨fun h => ⟨h ▸ hz, (root x).mp h⟩, fun h => (root x).mpr h.2⟩
      · intro x _
        rw [hd]
        exact ⟨affine_derivative a b x, ha⟩
    simp [fibreOn_of_regular roots, hd, show (y-b)/a = z from rfl, hz]
  · have roots : RegularRootList (fun x => a*x+b) (fun x => x ∈ s ∧ a*x+b = y) [] := by
      constructor
      · simp [List.Sorted]
      · intro x
        simp only [List.not_mem_nil, false_iff]
        rintro ⟨hx, he⟩
        exact hz ((root x).mpr he ▸ hx)
      · simp
    simp [fibreOn_of_regular roots, show (y-b)/a = z from rfl, hz]

theorem affine_marginalOn (s : Set ℝ) (a b : ℝ) (ha : a ≠ 0) (y : ℝ) :
    marginalOn s (fun x => a*x+b) y = some (sourceWeight s ((y-b)/a) * |a|⁻¹) := by
  rw [marginalOn, affine_fibreOn s a b ha]
  by_cases h : (y-b)/a ∈ s <;> simp [h, observe, sourceWeight, Value.mul, Value.add]

/-- Change coordinates on the entire real line. Applying the Jacobian theorem
to the weighted test itself proves both integrability directions without any
measurability assumption on the source predicate. -/
theorem affine_lebesgue (s : Set ℝ) [DecidablePred (· ∈ s)] (a b : ℝ) (ha : a ≠ 0) :
    realPushforwardOnValue (some (fun x => some (decide (x ∈ s)))) (some (fun x => some (a*x+b))) =
      densityValue (some (fun y => some (sourceWeight s ((y-b)/a) * |a|⁻¹))) := by
  let f := fun x : ℝ => a*x+b
  let d : D ℝ := .density (fun x => Value.mask (some (decide (x ∈ s))) (some 1)) (fun x => some (f x))
  change some (inLebesgueCoordinates d) = some (.density _ some)
  apply congrArg some
  apply inLebesgueCoordinates_of_chart
  constructor
  · funext y
    exact (pushforwardOn_density s f (by dsimp [f]; fun_prop) y).trans (affine_marginalOn s a b ha y)
  · intro y
    exact ⟨_, rfl⟩
  · intro t
    classical
    let g := fun y => (sourceWeight s ((y-b)/a) * |a|⁻¹) * t y
    have retract (x : ℝ) : (f x-b)/a = x := by dsimp [f]; field_simp [ha]
    have onto : Function.Surjective f := fun y => ⟨(y-b)/a, by dsimp [f]; field_simp [ha]⟩
    have inj : InjOn f univ := fun x _ z _ h => (retract x).symm.trans ((congrArg (fun y => (y-b)/a) h).trans (retract z))
    have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt f a univ x :=
      fun x _ => (affine_derivative a b x).hasDerivAt.hasDerivWithinAt
    have hj (x : ℝ) : |a| • g (f x) = sourceWeight s x * t (f x) := by
      simp only [g, retract, smul_eq_mul]
      field_simp [abs_ne_zero.mpr ha]
    have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd inj g
    have he := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd inj g
    simp only [image_univ, onto.range_eq, integrableOn_univ, hj, setIntegral_univ] at hi he
    have mask (x : ℝ) : Value.mask (some (decide (x ∈ s))) (some (1 : ℝ)) = some (sourceWeight s x) := by
      by_cases hx : x ∈ s <;> simp [Value.mask, sourceWeight, hx]
    change partialIntegral volume (fun x => Value.mul _ (some (t (f x)))) =
      partialIntegral volume (fun y => Value.mul _ (some (t y)))
    simp only [mask, Value.mul, partialIntegral, Value.Defined, Option.some.injEq, exists_eq', implies_true, true_and,
      Option.getD_some]
    change (if Integrable (fun x => sourceWeight s x * t (f x)) volume then
        some (∫ x, sourceWeight s x * t (f x)) else none) =
      (if Integrable g volume then some (∫ y, g y) else none)
    rw [hi, he]

end QSym.Distribution.GraphFibre
