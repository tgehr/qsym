import QSym.DistributionInverseCover
import QSym.DistributionSquareIntegral

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set Classical

private def sqrtSheet (negative : Bool) : InverseSheet square where
  target := Ioi 0
  point := fun y => if negative then -√y else √y
  slope := fun y => if negative then -jac y else jac y
  measurable := measurableSet_Ioi
  rightInv := by intro y hy; cases negative <;> simp [square, Real.sq_sqrt (le_of_lt hy)]
  derivWithin := by
    intro y hy
    have d : HasDerivWithinAt Real.sqrt (jac y) (Ioi 0) y := by
      simpa [jac, one_div] using (Real.hasDerivAt_sqrt (ne_of_gt hy)).hasDerivWithinAt (s := Ioi 0)
    cases negative
    · exact d
    · exact d.neg

private theorem sqrtSheet_source (negative : Bool) :
    (sqrtSheet negative).source = if negative then Iio 0 else Ioi 0 := by
  ext x
  cases negative <;> constructor
  · rintro ⟨y,hy,rfl⟩; exact Real.sqrt_pos.mpr hy
  · intro (hx : 0 < x); exact ⟨x^2, sq_pos_of_pos hx, Real.sqrt_sq hx.le⟩
  · rintro ⟨y,hy,rfl⟩; exact neg_lt_zero.mpr (Real.sqrt_pos.mpr hy)
  · intro (hx : x < 0)
    exact ⟨x^2, sq_pos_of_ne_zero hx.ne, by simp [sqrtSheet, Real.sqrt_sq_eq_abs, abs_of_neg hx]⟩

/-- Both regular sheets overlap on the whole positive target. Keep the two
signed integrals separate and retain the original joint probe at (0,0). -/
theorem square_joint_inverse_split (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => h x (square x)) =
      Value.add (partialIntegral volume (fun y => if 0 < y then (h (-√y) y).map (jac y * ·) else some 0))
        (Value.add (partialIntegral volume (fun y => if 0 < y then (h (√y) y).map (jac y * ·) else some 0))
          ((h 0 0).map (fun _ => 0))) := by
  rw [← branchIntegral_univ, InverseSheet.reconstruct [sqrtSheet true, sqrtSheet false] univ MeasurableSet.univ]
  simp only [InverseSheet.sum, sqrtSheet_source, Bool.true_eq, if_true, Bool.false_eq_true, if_false,
    compl_Iio]
  rw [show (univ : Set ℝ) \ Iio 0 = Ici 0 by ext x; simp]
  have residual : Ici (0:ℝ) \ Ioi 0 = {0} := by ext x; simp
  rw [residual]
  have endpoint : branchIntegral {0} (fun x => h x (square x)) = (h 0 0).map (fun _ => 0) := by
    cases e : h 0 0 <;> simp [branchIntegral, square, e, Value.Defined]
  rw [endpoint]
  have j (y : ℝ) : 0 ≤ jac y := by unfold jac; positivity
  simp [InverseSheet.contribution, sqrtSheet, abs_of_nonneg (j _), Real.sqrt_nonneg]

private def rootAt (negative : Bool) (y : ℝ) :=
  let z := Functions.sqrtR.apply (some y)
  if negative then Value.mul (some ((-1 : ℤ) : ℝ)) z else z

private abbrev squareCoordinates :=
  Tensor.consValue (some (rootAt true)) (Tensor.consValue (some (rootAt false)) Tensor.nilValue)

private theorem restricted_square_coordinates (p : Option (ℝ → Option Bool)) :
    Coordinates.restricted p squareCoordinates = inverseSourcePartValue p squareCoordinates := by
  apply Coordinates.restricted_of_gap (x := -1)
  have gap : Functions.sqrtR.apply (some (-1)) = none := by norm_num [Functions.sqrtR, Function1.apply]
  intro i; fin_cases i
  · change Value.mul _ (Functions.sqrtR.apply (some (-1))) = none
    rw [gap]; rfl
  · exact gap

private theorem squareCoordinates_output :
    squareCoordinates.map inverseCoverOutput = some (fun x => some (square x)) := by
  let g : Fin 2 → ℝ → Option ℝ := Fin.cases (rootAt true) (Fin.cases (rootAt false) Fin.elim0)
  change some (inverseCoverOutput g) = _
  apply congrArg some
  apply inverseCoverOutput_eq
  intro x y
  have two : (∃ i, g i y = some x) ↔ rootAt true y = some x ∨ rootAt false y = some x := by
    constructor
    · rintro ⟨i,hi⟩; fin_cases i <;> tauto
    · exact fun h => h.elim (fun hl => ⟨0,hl⟩) (fun hr => ⟨1,hr⟩)
  rw [two]
  by_cases hy : 0 ≤ y
  · simp only [rootAt, Function1.apply, Functions.sqrtR, hy, if_true, Option.some_bind,
      Value.mul, Int.cast_neg, Int.cast_one, neg_one_mul, Bool.false_eq_true, if_false, Option.some.injEq]
    constructor
    · rintro (rfl | rfl) <;> simp [square, Real.sq_sqrt hy]
    · intro e
      have eq := (congrArg Real.sqrt e).symm
      rw [square, Real.sqrt_sq_eq_abs] at eq
      rcases le_total 0 x with hx | hx
      · right; simpa [abs_of_nonneg hx] using eq
      · left; simpa [abs_of_nonpos hx] using congrArg Neg.neg eq
  · simp [rootAt, Functions.sqrtR, Function1.apply, Value.mul, hy, square,
      ne_of_gt ((lt_of_not_ge hy).trans_le (sq_nonneg x))]

private def probe (p : Option (ℝ → Option Bool)) (t : Option (ℝ → Option ℝ))
    (x y : Option ℝ) := Value.mul (Value.mask (p.bind (fun pred => x.bind pred)) (some ((1 : ℤ) : ℝ)))
      (t.bind (fun test => y.bind test))

private def regularMass (negative : Bool) (p : Option (ℝ → Option Bool)) (t : Option (ℝ → Option ℝ)) :=
  massValue (weightValue (some fun y => Value.mask (Value.lt (some ((0 : ℤ) : ℝ)) (some y))
    (Value.mul (probe p t (rootAt negative y) (some y))
      (Value.inv (Value.mul (some ((2 : ℤ) : ℝ)) (Functions.sqrtR.apply (some y)))))) lebesgueValue)

private theorem regularMass_eq (neg : Bool) (p : ℝ → Option Bool) (t : ℝ → Option ℝ) :
    regularMass neg (some p) (some t) = partialIntegral volume (fun y => if 0 < y then
      (probe (some p) (some t) (some (if neg then -√y else √y)) (some y)).map (jac y * ·)
      else some 0) := by
  apply congrArg (partialIntegral volume)
  funext y
  change Value.mul (Value.mul (some 1) (Value.mask _ _)) (some 1) = _
  rw [Value.mul_one_left, Value.mul_one_right]
  by_cases hy : 0 < y
  · have hn : 2 * √y ≠ 0 := by positivity
    simp [rootAt, Value.lt, Value.mask, hy, hy.le, Functions.sqrtR, Function1.apply, Value.mul,
      Value.inv, hn, jac]
    cases neg <;> simp only [Bool.false_eq_true, if_false, if_true, neg_one_mul]
    · cases probe (some p) (some t) (some √y) (some y) <;> simp [mul_comm]
    · cases probe (some p) (some t) (some (-√y)) (some y) <;> simp [mul_comm]
  · simp [Value.lt, Value.mask, hy]

theorem inversePart_square_pairing (p : Option (ℝ → Option Bool)) (t : Option (ℝ → Option ℝ)) :
    massValue (weightValue t (inverseSourcePartValue p squareCoordinates)) =
      Value.add (regularMass true p t) (Value.add (regularMass false p t)
        ((probe p t (some ((0 : ℤ) : ℝ)) (some ((0 : ℤ) : ℝ))).bind (fun _ => some ((0 : ℤ) : ℝ)))) := by
  have strictZero (v : Option ℝ) : (v.bind (fun _ => some ((0 : ℤ) : ℝ))) =
      v.map (fun _ => ((0 : ℤ) : ℝ)) := by cases v <;> rfl
  rw [strictZero]
  unfold inverseSourcePartValue
  rw [squareCoordinates_output]
  cases p with
  | none =>
    cases t <;> simp [massValue, weightValue, pushforwardOnValue, probe, Value.mask, Value.mul, Value.add]
  | some pred =>
    cases t with
    | none => simp [massValue, weightValue, probe, Value.mul, Value.add]
    | some test =>
      rw [regularMass_eq, regularMass_eq, Int.cast_zero]
      let h := fun x y : ℝ => probe (some pred) (some test) (some x) (some y)
      have eq := square_joint_inverse_split h
      convert eq using 1
      apply congrArg (partialIntegral volume)
      funext x
      simp [h, probe, Value.mul_one_right]

/-- A point query can reuse the forward graph's finite-root rule, even where
canonicalizing the distribution itself would change its other observations. -/
theorem inversePart_square_density (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    densityAtValue (inverseSourcePartValue p squareCoordinates) y =
      densityAtValue (realPushforwardOnValue p (some fun x => (some x).map (· ^ 2))) y := by
  unfold inverseSourcePartValue
  rw [squareCoordinates_output]
  cases p with
  | none => rfl
  | some pred =>
    cases y with
    | none => rfl
    | some y => exact (congrFun (coordinates_density _) y).symm

/-- With no target test, integrate the source predicate directly. -/
theorem inversePart_square_mass (p : Option (ℝ → Option Bool)) :
    massValue (inverseSourcePartValue p squareCoordinates) =
      p.bind fun _ => massValue (weightValue
        (some fun x => Value.mask (p.bind (fun pred => pred x)) (some ((1 : ℤ) : ℝ))) lebesgueValue) := by
  unfold inverseSourcePartValue
  rw [squareCoordinates_output, mass_pushforwardOn_total]
  cases p <;> rfl

namespace Coordinates

theorem square_pairing (p : Option (ℝ → Option Bool)) (t : Option (ℝ → Option ℝ)) :
    massValue (weightValue t (restricted p squareCoordinates)) =
      Value.add (regularMass true p t) (Value.add (regularMass false p t)
        ((probe p t (some ((0 : ℤ) : ℝ)) (some ((0 : ℤ) : ℝ))).bind (fun _ => some ((0 : ℤ) : ℝ)))) := by
  rw [restricted_square_coordinates]
  exact inversePart_square_pairing p t

theorem square_mass (p : Option (ℝ → Option Bool)) :
    massValue (restricted p squareCoordinates) =
      p.bind fun _ => massValue (weightValue
        (some fun x => Value.mask (p.bind (fun pred => pred x)) (some ((1 : ℤ) : ℝ))) lebesgueValue) := by
  rw [restricted_square_coordinates]
  exact inversePart_square_mass p

theorem square_density (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    densityAtValue (restricted p squareCoordinates) y =
      densityAtValue (realPushforwardOnValue p (some fun x => (some x).map (· ^ 2))) y := by
  rw [restricted_square_coordinates]
  exact inversePart_square_density p y

end Coordinates
end QSym.Distribution.GraphFibre
