import QSym.DistributionSquareChart
import QSym.Functions

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set Classical

/-- Integrate in target coordinates. A strict source test must exist at every
reachable target, including null points. Extend its restriction to that set
by zero for the finite integral. -/
def imageIntegral {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (s : Set Y)
    (j : Y → ℝ) (t : Y → Option ℝ) : Option ℝ :=
  if ∀ y ∈ s, Value.Defined (t y)
  then partialIntegral ν (fun y => some (j y * s.indicator (fun z => (t z).getD 0) y)) else none

/-- A target chart can use an ordinary masked integral on its regular set.
An exceptional target with zero integration coefficient still checks the test.
The regular coefficient need only exist on the regular set. -/
theorem imageIntegral_split {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (regular exceptional : Set Y) (w : Y → Option ℝ) (t : Y → Option ℝ)
    (hw : ∀ y ∈ regular, Value.Defined (w y))
    (hz : ∀ y ∈ exceptional, y ∉ regular → (w y).getD 0 = 0) :
    imageIntegral ν (regular ∪ exceptional) (fun y => (w y).getD 0) t =
      if ∀ y ∈ exceptional, Value.Defined (t y) then
        partialIntegral ν (fun y => if y ∈ regular then Value.mul (w y) (t y) else some 0)
      else none := by
  classical
  unfold imageIntegral
  by_cases he : ∀ y ∈ exceptional, Value.Defined (t y)
  · rw [if_pos he]
    by_cases hr : ∀ y ∈ regular, Value.Defined (t y)
    · rw [if_pos (fun y hy => hy.elim (hr y) (he y))]
      apply congrArg (partialIntegral ν)
      funext y
      by_cases hy : y ∈ regular
      · obtain ⟨a, ha⟩ := hw y hy
        obtain ⟨b, hb⟩ := hr y hy
        simp [hy, ha, hb, Value.mul]
      · by_cases hx : y ∈ exceptional <;> simp [hy, hx, hz, *]
    · rw [if_neg (fun h => hr (fun y hy => h y (Or.inl hy)))]
      symm
      cases h : partialIntegral ν (fun y => if y ∈ regular then Value.mul (w y) (t y) else some 0) with
      | none => rfl
      | some a =>
        exfalso
        apply hr
        intro y hy
        have d := ((partialIntegral_defined_iff _ _).mp ⟨a,h⟩).1 y
        obtain ⟨v,hv⟩ := hw y hy
        cases ht : t y <;> simp_all [Value.Defined, Value.mul]
  · rw [if_neg he, if_neg (fun h => he (fun y hy => h y (Or.inr hy)))]

/-- A change of variables proved for all total tests extends to strict partial
tests by retaining the exact image of the source map. Zero source weights
still demand a defined test at their output. -/
theorem imageIntegral_of_transport {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (w : X → ℝ) (j : Y → ℝ)
    (transport : ∀ u : Y → ℝ,
      partialIntegral μ (fun x => some (w x * u (f x))) =
        partialIntegral ν (fun y => some (j y * u y))) (t : Y → Option ℝ) :
    partialIntegral μ (fun x => Value.mul (some (w x)) (t (f x))) =
      imageIntegral ν (range f) j t := by
  unfold imageIntegral
  split
  · rename_i h
    rw [← transport]
    apply congrArg (partialIntegral μ)
    funext x
    obtain ⟨v, hv⟩ := h (f x) ⟨x, rfl⟩
    simp [hv, Value.mul, Set.indicator_of_mem (mem_range_self x)]
  · rename_i h
    cases hi : partialIntegral μ (fun x => Value.mul (some (w x)) (t (f x))) with
    | none => rfl
    | some v =>
      exfalso
      apply h
      rintro _ ⟨x, rfl⟩
      have hx := ((partialIntegral_defined_iff _ _).mp ⟨v, hi⟩).1 x
      cases ht : t (f x) <;> simp_all [Value.Defined, Value.mul]

def affineSquareIntegralWeight (a y : ℝ) : ℝ :=
  if 0 < y then (|a| * √y)⁻¹ else 0

/-- The closed guard selects the singular reciprocal at zero. It short-circuits
the square root at negative targets. This coefficient is a density observation. -/
def unrestrictedSquareDensity (j y : Option ℝ) : Option ℝ :=
  Value.mask (Value.le (some ((0 : ℤ) : ℝ)) y)
    (Value.mul (Value.inv (Functions.sqrtR.apply y)) j)

theorem unrestrictedSquareDensity_zero (j : Option ℝ) :
    unrestrictedSquareDensity j (some ((0 : ℤ) : ℝ)) = none := by
  simp [unrestrictedSquareDensity, Function1.apply, Functions.sqrtR, Value.mask, Value.le,
    Value.inv, Value.mul]

abbrev affineSquareSource (a b : ℝ) : D ℝ :=
  .density (fun _ => some 1) (fun x => some ((a*x+b)^2))

theorem affine_square_critical_density (a b : ℝ) (ha : a ≠ 0) :
    densityAt (inLebesgueCoordinates (affineSquareSource a b)) 0 = none := by
  rw [coordinates_density]
  let f := fun x : ℝ => (a*x+b)^2
  let c := -b/a
  have hc : a*c+b = 0 := by dsimp [c]; field_simp; ring
  have hd := ((affine_derivative a b c).hasDerivAt.pow 2).deriv
  have hz : deriv f c = 0 := by simpa [f, hc] using hd
  have crit := fibreOn_of_critical (mem_univ c) (show f c = 0 by simp [f,hc]) hz
  have h := pushforwardOn_density univ f (by dsimp [f]; fun_prop) 0
  simpa [affineSquareSource, f, densityAtValue, pushforwardOnValue, Value.mask, marginalOn, crit]
    using h

/-- The unrestricted graph keeps its undefined density at the critical value.
For integration it suffices to store its regular Jacobian and the closed
half-line on which tests must exist. -/
theorem affine_square_image_integral (a b : ℝ) (ha : a ≠ 0) (t : ℝ → Option ℝ) :
    integrate (inLebesgueCoordinates (affineSquareSource a b)) t =
      imageIntegral volume (Ici 0) (affineSquareIntegralWeight a) t := by
  have critical := affine_square_critical_density a b ha
  rw [coordinates_density] at critical
  rw [coordinates_of_missing_density critical]
  let f := fun x : ℝ => (a*x+b)^2
  have image : range f = Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact sq_nonneg (a*x+b)
    · intro hy
      refine ⟨(√y-b)/a, ?_⟩
      have h : a*((√y-b)/a)+b = √y := by field_simp
      exact (congrArg (· ^ 2) h).trans (Real.sq_sqrt hy)
  rw [← image]
  apply imageIntegral_of_transport volume volume f (fun _ => 1)
  intro u
  have h := affine_square_integral univ MeasurableSet.univ a b ha u
  have weight (y : ℝ) : squareChartWeight univ y * |a|⁻¹ = affineSquareIntegralWeight a y := by
    by_cases hy : 0 < y
    · simp [squareChartWeight, affineSquareIntegralWeight, jac, hy, ha, mul_inv_rev]
      ring
    · simp [squareChartWeight, affineSquareIntegralWeight, hy]
  simpa only [f, mem_univ, if_true, one_mul, preimage_univ, weight] using h

/-- The same closed Iverson expression can supply the integration coefficient
after filling its single missing value. The test is still checked separately
on the entire reachable half-line, including zero. -/
theorem affine_square_masked_image_integral (a b : ℝ) (ha : a ≠ 0) (t : ℝ → Option ℝ) :
    integrate (inLebesgueCoordinates (affineSquareSource a b)) t =
      imageIntegral volume (Ici 0)
        (fun y => (unrestrictedSquareDensity (some |a|⁻¹) (some y)).getD 0) t := by
  rw [affine_square_image_integral a b ha]
  have weights (y : ℝ) : affineSquareIntegralWeight a y =
      (unrestrictedSquareDensity (some |a|⁻¹) (some y)).getD 0 := by
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · simp [affineSquareIntegralWeight, unrestrictedSquareDensity, Value.le, Value.mask,
        not_le_of_gt hy, not_lt_of_gt hy]
    · simp [affineSquareIntegralWeight, unrestrictedSquareDensity, Value.le, Value.mask,
        Value.mul, Value.inv, Function1.apply, Functions.sqrtR]
    · simp [affineSquareIntegralWeight, unrestrictedSquareDensity, Value.le, Value.mask,
        Value.mul, Value.inv, Function1.apply, Functions.sqrtR, hy, hy.le, (Real.sqrt_pos.mpr hy).ne',
        mul_inv_rev]
  rw [funext weights]

end QSym.Distribution.GraphFibre
