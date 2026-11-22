import QSym.DistributionGraph
import QSym.DistributionBranch
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section
namespace QSym.Distribution.GraphFibre
open Set MeasureTheory

theorem affine_derivative (a b x : ℝ) :
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
  have hi : InjOn (fun x => a*x+b) s := fun _ _ _ _ he => mul_left_cancel₀ ha (add_right_cancel he)
  by_cases hz : z ∈ s
  · rw [if_pos hz]
    exact (congrArg (fibreOn s (fun x => a*x+b)) ((root z).mp rfl).symm).trans
      (fibreOn_of_injOn hi hz (affine_derivative a b z) ha)
  · rw [if_neg hz]
    apply fibreOn_of_notMem_image
    rintro ⟨x, hx, he⟩
    exact hz ((root x).mpr he ▸ hx)

/-- Disintegration over the whole source retains its unique inverse point. -/
theorem affine_fibre (a b : ℝ) (ha : a ≠ 0) (y : ℝ) :
    fibre (fun x => a*x+b) y = some [((y-b)/a, |a|⁻¹)] := by
  simpa using affine_fibreOn univ a b ha y

theorem affine_marginalOn (s : Set ℝ) (a b : ℝ) (ha : a ≠ 0) (y : ℝ) :
    marginalOn s (fun x => a*x+b) y = some (sourceWeight s ((y-b)/a) * |a|⁻¹) := by
  rw [marginalOn, affine_fibreOn s a b ha]
  by_cases h : (y-b)/a ∈ s <;> simp [h, observe, sourceWeight, Value.mul, Value.add]

/-- Transport strict finite integration through the affine bijection. The
pointwise hypothesis transports missing values as well as signed weights. -/
theorem affine_integral (a b : ℝ) (ha : a ≠ 0) (g k : ℝ → Option ℝ)
    (hk : ∀ x, k (a*x+b) = Value.mul (some |a|⁻¹) (g x)) :
    partialIntegral volume g = partialIntegral volume k := by
  classical
  let f := fun x : ℝ => a*x+b
  have retract (x : ℝ) : (f x-b)/a = x := by dsimp [f]; field_simp [ha]
  have onto : Function.Surjective f := fun y => ⟨(y-b)/a, by dsimp [f]; field_simp [ha]⟩
  have inj : InjOn f univ := fun x _ z _ h =>
    (retract x).symm.trans ((congrArg (fun y => (y-b)/a) h).trans (retract z))
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt f a univ x :=
    fun x _ => (affine_derivative a b x).hasDerivAt.hasDerivWithinAt
  have transport := branchIntegral_image MeasurableSet.univ inj hd k
  rw [image_univ, onto.range_eq, branchIntegral_univ, branchIntegral_univ] at transport
  rw [transport]
  apply congrArg (partialIntegral volume)
  funext x
  rw [show k (f x) = _ from hk x]
  cases g x <;> simp [Value.mul, smul_eq_mul, ← mul_assoc, abs_ne_zero.mpr ha]

/-- Empty fibres skip the test, whereas multiplication by a zero source
weight is strict. Definedness at discarded graph points suffices to relate
the two operations; on active points the test can still be partial. -/
theorem affine_disintegratesOn (s : Set ℝ) (a b : ℝ) (ha : a ≠ 0) (h : ℝ → ℝ → Option ℝ)
    (outside : ∀ x ∉ s, Value.Defined (h x (a*x+b))) :
    partialIntegral volume (fun x => Value.mul (some (sourceWeight s x)) (h x (a*x+b))) =
      partialIntegral volume (fun y => (fibreOn s (fun x => a*x+b) y).bind
        (fun atoms => observe atoms (fun x => h x y))) := by
  classical
  apply affine_integral a b ha
  intro x
  rw [affine_fibreOn s a b ha, show (a*x+b-b)/a = x by field_simp [ha]]
  by_cases hx : x ∈ s
  · simp [hx, sourceWeight, observe, Value.add_zero_right, Value.mul_one_left]
  · obtain ⟨v, hv⟩ := outside x hx
    simp [hx, hv, sourceWeight, observe, Value.mul]

open Classical in
/-- Without a domain hypothesis, the excluded points contribute exactly
one definedness guard to reconstruction by the restricted fibres. -/
theorem affine_disintegratesOn_strict (s : Set ℝ) (a b : ℝ) (ha : a ≠ 0) (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mul (some (sourceWeight s x)) (h x (a*x+b))) =
      if ∀ x ∉ s, Value.Defined (h x (a*x+b)) then
        partialIntegral volume (fun y => (fibreOn s (fun x => a*x+b) y).bind
          (fun atoms => observe atoms (fun x => h x y)))
      else none := by
  split
  · exact affine_disintegratesOn s a b ha h ‹_›
  · rename_i missing
    cases he : partialIntegral volume (fun x => Value.mul (some (sourceWeight s x)) (h x (a*x+b))) with
    | none => rfl
    | some v =>
      exfalso
      apply missing
      intro x _
      obtain ⟨r, hr⟩ := ((partialIntegral_defined_iff _ _).mp ⟨v, he⟩).1 x
      cases hx : h x (a*x+b) with
      | none => simp [hx, Value.mul] at hr
      | some z => exact ⟨z, rfl⟩

/-- Testing the disintegrated fibre against a joint partial test reconstructs
the original graph integral, including its finite-integrability domain. -/
theorem affine_disintegrates (a b : ℝ) (ha : a ≠ 0) (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => h x (a*x+b)) =
      partialIntegral volume (fun y => (fibre (fun x => a*x+b) y).bind
        (fun atoms => observe atoms (fun x => h x y))) := by
  simpa [sourceWeight, Value.mul_one_left] using affine_disintegratesOn univ a b ha h (by simp)

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
    change partialIntegral volume (fun x => Value.mul _ (some (t (f x)))) =
      partialIntegral volume (fun y => Value.mul _ (some (t y)))
    apply affine_integral a b ha
    intro x
    have inv : (a*x+b-b)/a = x := by field_simp [ha]
    simp only [inv]
    by_cases hx : x ∈ s <;> simp [f, hx, sourceWeight, Value.mask, Value.mul]

end QSym.Distribution.GraphFibre
