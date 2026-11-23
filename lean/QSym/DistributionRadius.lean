import QSym.DistributionImageIntegral
import QSym.DistributionIntegralCertificate

noncomputable section
namespace QSym.Distribution.GraphFibre
open Classical MeasureTheory

/-- A target with nonnegative radius r(y) proposes the two source coordinates
c ± r(y), which coincide at radius zero. At a source coordinate the output
is defined exactly when there is a unique target proposing that coordinate. -/
def radiusOutput (c : ℝ) (r : ℝ → Option ℝ) (x : ℝ) : Option ℝ :=
  if h : ∃! y, r y = some |x-c| then some h.choose else none

def radiusImageValue (c : Option ℝ) (r : Option (ℝ → Option ℝ)) : Option (D ℝ) := do
  let c ← c
  let r ← r
  realPushforwardOnValue (some fun _ => some true) (some (radiusOutput c r))

def sqrtRadius (j : Option ℝ) (y : ℝ) :=
  Value.mul j (Functions.sqrtR.apply (some y))

theorem radiusOutput_of_inverse {c : ℝ} {r f : ℝ → Option ℝ}
    (complete : ∀ x y, r y = some |x-c| ↔ f x = some y) : radiusOutput c r = f := by
  funext x
  cases hz : f x with
  | none =>
    have empty : ¬ ∃! y, r y = some |x-c| := fun ⟨y, hy, _⟩ =>
      Option.noConfusion (hz.symm.trans ((complete x y).1 hy))
    rw [radiusOutput, dif_neg empty]
  | some z =>
    have unique : ∃! y, r y = some |x-c| := ⟨z, (complete x z).2 hz, fun y hy =>
      Option.some.inj (((complete x y).1 hy).symm.trans hz)⟩
    rw [radiusOutput, dif_pos unique]
    exact ((complete x _).1 unique.choose_spec.1).symm.trans hz

theorem radiusImage_of_inverse {c : ℝ} {r f : ℝ → Option ℝ}
    (complete : ∀ x y, r y = some |x-c| ↔ f x = some y) :
    realPushforwardOnValue (some fun _ => some true) (some f) = radiusImageValue (some c) (some r) := by
  change _ = realPushforwardOnValue (some fun _ => some true) (some (radiusOutput c r))
  rw [radiusOutput_of_inverse complete]

theorem sqrtRadius_output (a b : ℝ) (ha : a ≠ 0) :
    radiusOutput (-b/a) (sqrtRadius (some |a|⁻¹)) = fun x => some ((a*x+b)^2) := by
  apply radiusOutput_of_inverse
  intro x y
  have factor : a*(x- -b/a) = a*x+b := by field_simp; ring
  have hab : |a*x+b| = |a| * |x- -b/a| := by rw [← factor, abs_mul]
  by_cases hy : 0 ≤ y
  · have sr : Functions.sqrtR.apply (some y) = some (√y) := by simp [Function1.apply, Functions.sqrtR, hy]
    simp only [sqrtRadius, sr, Value.mul, Option.some.injEq]
    constructor
    · intro eq
      have h : √y = |a*x+b| := by rw [hab, ← eq]; field_simp
      exact (sq_abs _).symm.trans ((congrArg (· ^ 2) h).symm.trans (Real.sq_sqrt hy))
    · rintro rfl
      rw [Real.sqrt_sq_eq_abs, hab]
      field_simp
  · have ne : (a*x+b)^2 ≠ y := ne_of_gt ((lt_of_not_ge hy).trans_le (sq_nonneg _))
    simp [sqrtRadius, Function1.apply, Functions.sqrtR, Value.mul, hy, ne]

/-- The inverse chart denotes the same parameterized distribution, including the
source coordinate needed by higher-order contexts. -/
theorem sqrtRadius_image (a b : ℝ) (ha : a ≠ 0) :
    radiusImageValue (some (-b/a)) (some (sqrtRadius (some |a|⁻¹))) =
      some (inLebesgueCoordinates (affineSquareSource a b)) := by
  change some (inLebesgueCoordinates (.density _ (radiusOutput _ _))) = _
  rw [sqrtRadius_output a b ha]
  rfl

/-- Pair directly in target coordinates with an arbitrary partial test. The
regular coefficient may be filled at zero, but the test must exist there. -/
theorem sqrtRadius_image_integral (a b : ℝ) (ha : a ≠ 0) (t : ℝ → Option ℝ) :
    (radiusImageValue (some (-b/a)) (some (sqrtRadius (some |a|⁻¹)))).bind
        (fun d => integrate d t) =
      imageIntegral volume (Set.Ici 0)
        (fun y => (unrestrictedSquareDensity (some |a|⁻¹) (some y)).getD 0) t := by
  rw [sqrtRadius_image a b ha]
  exact affine_square_masked_image_integral a b ha t

theorem radius_coordinates (c j : ℝ) (hj : 0 < j) :
    radiusImageValue (some c) (some (sqrtRadius (some j))) =
      some (affineSquareSource j⁻¹ (-c/j)) := by
  have centre : -(-c/j)/j⁻¹ = c := by field_simp
  have scale : |j⁻¹|⁻¹ = j := by rw [abs_of_pos (inv_pos.mpr hj), inv_inv]
  have ha := inv_ne_zero hj.ne'
  have h := sqrtRadius_image j⁻¹ (-c/j) ha
  have critical := affine_square_critical_density j⁻¹ (-c/j) ha
  rw [coordinates_density] at critical
  rwa [centre, scale, coordinates_of_missing_density critical] at h

/-- The preimage of a closed sublevel set of the squared affine map has
length twice the inverse radius. This includes the zero-length critical fibre. -/
theorem radius_sublevel (c j : ℝ) (hj : 0 < j) (q : Option ℝ) :
    massValue (weightValue (some (fun y => Value.mask (Value.le (some y) q) (some ((1 : ℤ) : ℝ))))
      (radiusImageValue (some c) (some (sqrtRadius (some j))))) =
      Value.mask (Value.le (some ((0 : ℤ) : ℝ)) q)
        (Value.mul (Value.mul (some ((2 : ℤ) : ℝ)) (some j)) (Functions.sqrtR.apply q)) := by
  rw [radius_coordinates c j hj]
  let f (x : ℝ) := (j⁻¹*x + -c/j)^2
  change partialIntegral volume (fun x => Value.mul (Value.mul (some 1)
    (Value.mask (Value.le (some (f x)) q) (some ((1 : ℤ) : ℝ)))) (some 1)) = _
  simp only [Value.mul_one_left, Value.mul_one_right, Int.cast_one, Int.cast_zero, Int.cast_ofNat]
  cases q with
  | none =>
    unfold partialIntegral
    split
    · rename_i h
      simpa [Value.le, Value.mask, Value.Defined] using h.1 0
    · rfl
  | some t =>
    by_cases ht : 0 ≤ t
    · let r := j*√t
      have hr : 0 ≤ r := mul_nonneg hj.le (Real.sqrt_nonneg t)
      have band (x : ℝ) : f x ≤ t ↔ c-r ≤ x ∧ x ≤ c+r := by
        have mul_eq : j*(j⁻¹*x + -c/j) = x-c := by field_simp; ring
        have eq : |x-c| = j * |j⁻¹*x + -c/j| := by rw [← mul_eq, abs_mul, abs_of_pos hj]
        have square_iff : f x ≤ t ↔ |j⁻¹*x + -c/j| ≤ √t := by
          rw [← sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _), sq_abs, Real.sq_sqrt ht]
        rw [square_iff, ← mul_le_mul_left hj, ← eq, abs_le]
        constructor <;> rintro ⟨_,_⟩ <;> constructor <;> dsimp [r] at * <;> linarith
      rw [partialIntegral_interval _ (c-r) (c+r) 1 [] (by linarith)]
      · simp [Value.mask, Value.le, Value.mul, Function1.apply, Functions.sqrtR, ht, r]
        ring
      · intro x
        by_cases h : f x ≤ t <;> simp [Value.le, Value.mask, Value.Defined, h]
      · intro x _
        by_cases h : f x ≤ t
        · rw [if_pos ((band x).mp h)]
          simp [Value.le, Value.mask, h]
        · rw [if_neg (mt (band x).mpr h)]
          simp [Value.le, Value.mask, h]
    · have absent (x : ℝ) : ¬ f x ≤ t := not_le.mpr ((lt_of_not_ge ht).trans_le (sq_nonneg _))
      simpa [Value.mask, Value.le, absent, ht] using (partialIntegral_zero (volume : Measure ℝ))

end QSym.Distribution.GraphFibre
