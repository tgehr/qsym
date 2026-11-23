import QSym.DistributionWeightedSquare
import QSym.DistributionAffineSquare
import QSym.DistributionAtomRows

noncomputable section
namespace QSym.Distribution.GraphFibre

/-- Evidence for eliminating a square integral built from weighted Dirac rows. -/
structure SquareWeightSource (w : ℝ → Option ℝ) : Prop where
  total : ∀ x, Value.Defined (w x)
  borel : BorelReal w
  critical : w 0 = some 0
  compatible : ∀ x, 0 ≤ (w (-x)).getD 0 * (w x).getD 0

/-- The sign test is local to a reflected pair. A source can carry positive
and negative weights on different fibres. Its strict comparison certifies
that both evaluations exist as well. -/
theorem squareWeightSource_of_product (w : ℝ → Option ℝ) (hm : BorelReal w)
    (hs : ∀ x, Value.le (some ((0 : ℤ) : ℝ))
      (Value.mul (w (((-1 : ℤ) : ℝ) * x)) (w x)) = some true)
    (h0 : Value.nonzero (w ((0 : ℤ) : ℝ)) = some false) : SquareWeightSource w := by
  have rows (x) : ∃ a b, w (-x) = some a ∧ w x = some b ∧ 0 ≤ a*b := by
    have h := hs x
    cases l : w (-x) <;> cases r : w x <;> simp_all [Value.le, Value.mul]
  have zero : w 0 = some 0 := by
    cases e : w 0 <;> simp_all [Value.nonzero]
  refine ⟨?_, hm, zero, ?_⟩
  · intro x
    obtain ⟨_, b, _, hb, _⟩ := rows x
    exact ⟨b,hb⟩
  · intro x
    obtain ⟨a, b, ha, hb, h⟩ := rows x
    simpa only [ha,hb,Option.getD_some] using h

private def regularSquareValue (w : ℝ → Option ℝ) (y : Option ℝ) : Option ℝ :=
  let r := Functions.sqrtR.apply y
  let l := Value.mul (some ((-1 : ℤ) : ℝ)) r
  Value.mul (Value.add (l.bind w) (r.bind w)) (Value.inv (Value.mul (some ((2 : ℤ) : ℝ)) r))

def weightedSquareValue (w : ℝ → Option ℝ) (y : ℝ) : Option ℝ :=
  Value.mask (Value.lt (some ((0 : ℤ) : ℝ)) (some y)) (regularSquareValue w (some y))

namespace SquareRows

abbrev source (w : ℝ → Option ℝ) :=
  some (inLebesgueCoordinates (.density w (fun x => some (square x))))

variable {w : ℝ → Option ℝ} (ht : ∀ x, Value.Defined (w x))

include ht in
private theorem eq_some (x : ℝ) : w x = some ((w x).getD 0) := by
  obtain ⟨v,h⟩ := ht x
  simp [h]

private theorem map_eq (product : Bool) (x : ℝ) : squareInput product (some x) = some (square x) := by
  cases product <;> simp [squareInput, square, Value.mul, pow_two]

include ht

theorem integral (product : Bool) :
    realIntegralValue (some fun x => scaleValue (w x) (diracValue (squareInput product (some x)))) = source w := by
  simp_rw [map_eq]
  rw [funext (eq_some ht)]
  exact realIntegral_dirac _ _

theorem bind (product : Bool) :
    realBindValue lebesgueValue (some fun x => scaleValue (w x) (diracValue (squareInput product (some x)))) = source w := by
  simp_rw [map_eq]
  rw [funext (eq_some ht)]
  exact realBind_dirac _ _

theorem weighted_bind (product : Bool) :
    realBindValue (weightValue (some w) lebesgueValue) (some fun x => diracValue (squareInput product (some x))) =
      source w := by
  simp_rw [map_eq]
  rw [funext (eq_some ht)]
  exact realBind_weight_dirac _ _

private theorem regular_eq {y : ℝ} (hy : 0 < y) :
    regularSquareValue w (some y) = some (weightedSquareDensity (fun x => (w x).getD 0) y) := by
  have hr := (Real.sqrt_pos.mpr hy).ne'
  obtain ⟨l,hl⟩ := ht (-√y)
  obtain ⟨r,hr'⟩ := ht (√y)
  simp [regularSquareValue, weightedSquareDensity, Function1.apply, Functions.sqrtR, hy, hy.le,
    Value.mul, hl, hr', Value.add, Value.inv, jac, hr]

/-- A single density query needs total Dirac rows. Only a query at zero
inspects the critical weight. No sign or measurability proof is needed. -/
theorem density (y : Option ℝ) : densityAtValue (source w) y =
    squareCases y (regularSquareValue w y) (some ((0 : ℤ) : ℝ))
      (Binding.conditionalValue (Value.nonzero (w ((0 : ℤ) : ℝ))) none (some ((0 : ℤ) : ℝ))) := by
  cases y with
  | none => rfl
  | some y =>
    change densityAt (inLebesgueCoordinates _) y = _
    rw [coordinates_density, funext (eq_some ht), weighted_square_density]
    let g := fun x => (w x).getD 0
    rcases lt_trichotomy y 0 with hn | rfl | hp
    · simp [squareCases, Value.lt, Binding.conditionalValue, weightedSquareDensity, hn, hn.ne, not_lt_of_gt hn]
    · by_cases h : g 0 = 0 <;> simp_all [g, squareCases, Binding.conditionalValue, weightedSquareDensity, Value.lt, Value.nonzero]
    · simp [squareCases, Value.lt, Binding.conditionalValue, hp, hp.ne']
      exact (regular_eq (w := fun x => some (g x)) (fun _ => ⟨_,rfl⟩) hp).symm

end SquareRows

namespace SquareWeightSource
variable {w : ℝ → Option ℝ} (c : SquareWeightSource w)
include c

theorem chart : SquareRows.source w = weightValue (some (weightedSquareValue w)) lebesgueValue := by
  let g := fun x => (w x).getD 0
  have e : w = fun x => some (g x) := funext (SquareRows.eq_some c.total)
  change some (inLebesgueCoordinates (.density w _)) = _
  rw [e, weighted_square_chart g (by simp [g,c.critical]) c.borel.val c.compatible]
  simp only [weightValue, weight, lebesgueValue, densityValue, Option.some_bind, Option.map_some, Value.mul_one_left]
  congr 2
  funext y
  by_cases hy : 0 < y
  · have hr := (Real.sqrt_pos.mpr hy).ne'
    simp [weightedSquareDensity, weightedSquareValue, regularSquareValue, Function1.apply, Functions.sqrtR, hy.le, hy,
      Value.lt, Value.inv, Value.mask, Value.mul, Value.add, jac, hr]
  · simp [weightedSquareDensity, weightedSquareValue, hy, Value.lt, Value.mask, Value.mul]

end SquareWeightSource

theorem absSquareSource : SquareWeightSource (fun x : ℝ => Value.abs (some x)) :=
  ⟨fun _ => ⟨_,rfl⟩, BorelReal.abs BorelReal.var, by simp [Value.abs],
    fun x => mul_nonneg (abs_nonneg (-x)) (abs_nonneg x)⟩

theorem absSquareChart : SquareRows.source (fun x : ℝ => Value.abs (some x)) =
    weightValue (some fun y => Value.mask (Value.lt (some ((0 : ℤ) : ℝ)) (some y))
      (some ((1 : ℤ) : ℝ))) lebesgueValue := by
  rw [absSquareSource.chart]
  apply congrArg (fun v => weightValue (some v) lebesgueValue)
  funext y
  by_cases hy : 0 < y
  · have hr := Real.sqrt_pos.mpr hy
    simp [weightedSquareValue, regularSquareValue, Function1.apply, Functions.sqrtR, hy, hy.le, Value.lt,
      Value.abs, Value.mask, Value.mul, Value.add, Value.inv, abs_of_pos hr, hr.ne']
    field_simp
    ring
  · simp [weightedSquareValue, hy, Value.lt, Value.mask, Value.mul]

end QSym.Distribution.GraphFibre
