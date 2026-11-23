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

/-- A square cover contributes two equal regular branches. Their combined
Jacobian is j / √y. Its common endpoint is visited once, even for a partial test. -/
theorem radius_sqrt_pairing (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ}
    (hr : r = sqrtRadius v) (test : Option (ℝ → Option ℝ)) :
    massValue (weightValue test (radiusImageValue z (some r))) =
      (test.bind (fun t => t ((0 : ℤ) : ℝ))).bind (fun _ =>
        massValue (weightValue (some fun y => Value.mask (Value.lt (some ((0 : ℤ) : ℝ)) (some y))
          (Value.mul (test.bind (fun t => t y))
            (Value.mul (Value.inv (Functions.sqrtR.apply (some y))) v))) lebesgueValue)) := by
  cases test with
  | none => rfl
  | some t =>
    rw [hr, hv, hz, radius_coordinates _ _ (by exact_mod_cast hj)]
    let a : ℝ := (j : ℝ)⁻¹
    let b : ℝ := -(c : ℝ) / j
    have ha : a ≠ 0 := inv_ne_zero (by exact_mod_cast hj.ne')
    have scale : |a|⁻¹ = (j : ℝ) := by
      dsimp [a]; rw [abs_inv, inv_inv, abs_of_pos (by exact_mod_cast hj)]
    have h := affine_square_masked_image_integral a b ha t
    have crit := affine_square_critical_density a b ha
    rw [coordinates_density] at crit
    rw [coordinates_of_missing_density crit, scale] at h
    change partialIntegral volume (fun x => Value.mul (Value.mul (some 1) (t ((a*x+b)^2))) (some 1)) = _
    simp only [Value.mul_one_right, Value.mul_one_left]
    change partialIntegral volume (fun x => Value.mul (some 1) (t ((a*x+b)^2))) = _ at h
    simp only [Value.mul_one_left] at h
    rw [h, ← Set.Ioi_union_left (a := (0 : ℝ))]
    let w (y : ℝ) := unrestrictedSquareDensity (some (j : ℝ)) (some y)
    have reg (y : ℝ) (hy : 0 < y) :
        w y = Value.mul (Value.inv (Functions.sqrtR.apply (some y))) (some (j : ℝ)) := by
      simp [w, unrestrictedSquareDensity, Value.mask, Value.le, hy.le]
    rw [imageIntegral_split volume _ _ w t (fun y hy => by
      change 0 < y at hy
      simp [reg y hy, Value.Defined, Value.mul, Value.inv, Function1.apply, Functions.sqrtR,
        hy.le, (Real.sqrt_pos.mpr hy).ne']) (by
      intro y hy _; obtain rfl : y = 0 := hy
      simp [w, unrestrictedSquareDensity, Value.mask, Value.le, Value.inv,
        Function1.apply, Functions.sqrtR, Value.mul])]
    simp only [Int.cast_zero]
    cases ht : t 0 with
    | none => simp [ht, Value.Defined]
    | some v =>
      simp only [Set.mem_singleton_iff, forall_eq, ht, Value.Defined, Option.some.injEq, exists_eq',
        if_true, Option.some_bind]
      change partialIntegral volume _ = partialIntegral volume _
      apply congrArg (partialIntegral volume)
      funext y
      simp only [Option.some_bind, Value.mul_one_left, Value.mul_one_right, Int.cast_zero]
      by_cases hy : 0 < y
      · simp only [Set.mem_Ioi, hy, if_true, reg y hy, Value.lt, Option.some_bind, decide_true, Value.mask]
        generalize Value.mul (Value.inv (Functions.sqrtR.apply (some y))) (some (j : ℝ)) = k
        cases t y <;> cases k <;> simp [Value.mul, mul_comm, hy]
      · simp [hy, Set.mem_Ioi, Value.mask, Value.lt]

def windowCompare (strict : Bool) : Option ℝ → Option ℝ → Option Bool :=
  if strict then Value.lt else Value.le

/-- A real Iverson bracket, also allowing the three exact casts from a natural mask. -/
def windowWeight (strict casts : Bool) (q : Option ℝ) (y : ℝ) : Option ℝ :=
  let p := windowCompare strict (some y) q
  if casts then Functions.castQR.apply (Functions.castZQ.apply
    (Functions.castNZ.apply (Value.mask p (some 1))))
  else Value.mask p (some ((1 : ℤ) : ℝ))

abbrev sublevelWeight := windowWeight false

theorem windowWeight_eq (strict casts : Bool) (q : Option ℝ) :
    windowWeight strict casts q = windowWeight strict false q := by
  funext y
  unfold windowWeight
  cases windowCompare strict (some y) q with
  | none => cases casts <;> rfl
  | some p => cases p <;> cases casts <;> norm_num [Value.mask, Function1.apply,
      Functions.castNZ, Functions.castZQ, Functions.castQR]

theorem sublevelWeight_eq (casts : Bool) (q : Option ℝ) : sublevelWeight casts q = sublevelWeight false q :=
  windowWeight_eq false casts q

theorem radius_sqrt_sublevel (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ}
    (hr : r = sqrtRadius v) (casts : Bool) (q : Option ℝ) :
    massValue (weightValue (some (sublevelWeight casts q)) (radiusImageValue z (some r))) =
      Value.mask (Value.le (some ((0 : ℤ) : ℝ)) q)
        (Value.mul (Value.mul (some ((2 : ℤ) : ℝ)) v) (Functions.sqrtR.apply q)) := by
  rw [sublevelWeight_eq casts q, hr, hv, hz]
  exact radius_sublevel c j (by exact_mod_cast hj) q

/-- For mass with the unit test, opening a sublevel removes at most two
source points. A missing threshold remains missing on the entire source. -/
theorem radius_sqrt_open_sublevel (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ}
    (hr : r = sqrtRadius v) (casts : Bool) (q : Option ℝ) :
    massValue (weightValue (some (windowWeight true casts q)) (radiusImageValue z (some r))) =
      Value.mask (Value.le (some ((0 : ℤ) : ℝ)) q)
        (Value.mul (Value.mul (some ((2 : ℤ) : ℝ)) v) (Functions.sqrtR.apply q)) := by
  rw [← radius_sqrt_sublevel c j hj hz hv hr false q, windowWeight_eq true casts,
    hr, hv, hz, radius_coordinates _ _ (by exact_mod_cast hj)]
  let f (x : ℝ) := (j:ℝ)⁻¹*x + -(c:ℝ)/j
  change partialIntegral volume (fun x => Value.mul (Value.mul (some 1) (windowWeight true false q (f x ^ 2))) (some 1)) =
    partialIntegral volume (fun x => Value.mul (Value.mul (some 1) (windowWeight false false q (f x ^ 2))) (some 1))
  simp only [Value.mul_one_left, Value.mul_one_right]
  cases q with
  | none => rfl
  | some t =>
    apply partialIntegral_congr_away _ _ [(c:ℝ)-(j:ℝ)*√t, (c:ℝ)+(j:ℝ)*√t]
    · intro x; by_cases h : f x ^ 2 < t <;> simp [windowWeight, windowCompare, Value.lt, Value.mask, Value.Defined, h]
    · intro x; by_cases h : f x ^ 2 ≤ t <;> simp [windowWeight, windowCompare, Value.le, Value.mask, Value.Defined, h]
    · intro x hx
      have off : f x ^ 2 ≠ t := by
        rintro rfl
        rw [Real.sqrt_sq_eq_abs] at hx
        have e : (j:ℝ) * f x = x-c := by dsimp [f]; field_simp; ring
        by_cases pos : 0 ≤ f x
        · rw [abs_of_nonneg pos, e] at hx
          exact hx _ (List.mem_cons_of_mem _ List.mem_cons_self) (by ring)
        · rw [abs_of_neg (lt_of_not_ge pos), mul_neg, e] at hx
          exact hx _ List.mem_cons_self (by ring)
      have cmp : f x ^ 2 < t ↔ f x ^ 2 ≤ t := ⟨le_of_lt, fun h => lt_of_le_of_ne h off⟩
      simp [windowWeight, windowCompare, Value.le, Value.lt, cmp]

end QSym.Distribution.GraphFibre
