import QSym.DistributionSquareChart

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

end QSym.Distribution.GraphFibre
