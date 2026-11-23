import QSym.DistributionAffineSquare
import QSym.DistributionRadius

noncomputable section
namespace QSym.Distribution.GraphFibre
open Classical MeasureTheory

theorem affineSquare_radius_image (a b j : ℚ) (ha : a ≠ 0) (hj : j = |a⁻¹|)
    {f : ℝ → Option ℝ} (hf : StepSource.Affine f a b) {z v : Option ℝ}
    (hz : z = some ((-b/a : ℚ) : ℝ)) (hv : v = some (j : ℝ)) (product : Bool) :
    realPushforwardOnValue (some fun _ => some true) (some fun x => squareInput product (f x)) =
      radiusImageValue z (some (sqrtRadius v)) := by
  rw [hz, hv, hj]
  change _ = realPushforwardOnValue (some fun _ => some true) (some (radiusOutput _ _))
  simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_abs, Rat.cast_inv, abs_inv]
  rw [sqrtRadius_output _ _ (by exact_mod_cast ha), funext hf.equation]
  cases product <;> simp [squareInput, Value.mul, pow_two]

theorem sqrtRadius_left (v : Option ℝ) :
    (fun y => Value.mul v (Functions.sqrtR.apply (some y))) = sqrtRadius v := rfl

theorem sqrtRadius_right (v : Option ℝ) :
    (fun y => Value.mul (Functions.sqrtR.apply (some y)) v) = sqrtRadius v := by
  funext y
  unfold sqrtRadius
  cases Functions.sqrtR.apply (some y) <;> cases v <;> simp [Value.mul, mul_comm]

theorem sqrtRadius_one :
    (fun y => Functions.sqrtR.apply (some y)) = sqrtRadius (some ((1 : ℚ) : ℝ)) := by
  funext y
  simp [sqrtRadius, Value.mul_one_left]

theorem sqrtRadius_guardedOne :
    (fun y => Binding.guardValue (Value.le (some ((0 : ℤ) : ℝ)) (some y))
      (Functions.sqrtR.apply (some y))) = sqrtRadius (some ((1 : ℚ) : ℝ)) := by
  rw [← sqrtRadius_one]
  funext y
  by_cases hy : 0 ≤ y <;> simp [Binding.guardValue, Value.le, Function1.apply, Functions.sqrtR, hy]

theorem radius_sqrt_density (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ}
    (hr : r = sqrtRadius v) (y : Option ℝ) :
    densityAtValue (radiusImageValue z (some r)) y = unrestrictedSquareDensity v y := by
  let a := j⁻¹
  let b := -c/j
  have ha : a ≠ 0 := inv_ne_zero hj.ne'
  have jac : j = |a⁻¹| := by simp [a, abs_of_pos hj]
  let aff := fun (m k : ℚ) (x : ℝ) => some ((m : ℝ)*x+k)
  have eq (m k) : StepSource.Affine (aff m k) m k := ⟨fun _ => rfl⟩
  have centre : z = some ((-b/a : ℚ) : ℝ) := by rw [hz]; congr 2; dsimp [a,b]; field_simp
  rw [hr, ← affineSquare_radius_image _ _ _ ha jac (eq a b) centre hv false]
  exact affineSquare_unrestricted_density a b j ha jac (eq a b) (eq a⁻¹ (-b/a)) hv
    (2*|a|) 1 one_ne_zero (mul_one _).symm rfl rfl false y

/-- Scalar normalization may represent an Iverson bracket as a natural mask
followed by the three exact casts to real. -/
def sublevelWeight (casts : Bool) (q : Option ℝ) (y : ℝ) : Option ℝ :=
  let p := Value.le (some y) q
  if casts then Functions.castQR.apply (Functions.castZQ.apply
    (Functions.castNZ.apply (Value.mask p (some 1))))
  else Value.mask p (some ((1 : ℤ) : ℝ))

theorem sublevelWeight_eq (casts : Bool) (q : Option ℝ) : sublevelWeight casts q = sublevelWeight false q := by
  funext y
  unfold sublevelWeight
  cases Value.le (some y) q with
  | none => cases casts <;> rfl
  | some p => cases p <;> cases casts <;> norm_num [Value.mask, Function1.apply,
      Functions.castNZ, Functions.castZQ, Functions.castQR]

theorem radius_sqrt_sublevel (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ}
    (hr : r = sqrtRadius v) (casts : Bool) (q : Option ℝ) :
    massValue (weightValue (some (sublevelWeight casts q)) (radiusImageValue z (some r))) =
      Value.mask (Value.le (some ((0 : ℤ) : ℝ)) q)
        (Value.mul (Value.mul (some ((2 : ℤ) : ℝ)) v) (Functions.sqrtR.apply q)) := by
  rw [sublevelWeight_eq casts q, hr, hv, hz]
  exact radius_sublevel c j (by exact_mod_cast hj) q

end QSym.Distribution.GraphFibre
