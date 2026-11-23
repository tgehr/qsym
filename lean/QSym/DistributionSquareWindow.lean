import QSym.DistributionRadiusImage

noncomputable section
namespace QSym.Distribution.GraphFibre
open Classical MeasureTheory Set

theorem closedBand_square_chart (a b j : ℚ) (ha : a ≠ 0) (hj : j = |a⁻¹|)
    {f : ℝ → Option ℝ} (hf : StepSource.Affine f a b) {z v : Option ℝ}
    (hz : z = some ((-b/a : ℚ) : ℝ)) (hv : v = some (j : ℝ)) (product : Bool)
    (l h u : ℚ) (order : l ≤ h) (mid : a*(l+h)+2*b = 0) (cap : u = (a*h+b)^2)
    {lo hi top : Option ℝ} (hl : lo = some (l : ℝ)) (hh : hi = some (h : ℝ))
    (hu : top = some (u : ℝ)) :
    realPushforwardOnValue (some fun x => Value.and (Value.le lo (some x)) (Value.le (some x) hi))
        (some fun x => squareInput product (f x)) =
      weightValue (some (sublevelWeight false top)) (radiusImageValue z (some (sqrtRadius v))) := by
  rw [hl, hh, hu, ← affineSquare_radius_image a b j ha hj hf hz hv product]
  let F (x : ℝ) := ((a : ℝ)*x+b)^2
  have map_eq : (fun x => squareInput product (f x)) = fun x => some (F x) := by
    funext x
    rw [hf.equation]
    cases product <;> simp [F, squareInput, Value.mul, pow_two]
  rw [map_eq]
  have m : (a : ℝ)*(l+h)+2*b = 0 := by exact_mod_cast mid
  have k : (u : ℝ) = ((a : ℝ)*h+b)^2 := by exact_mod_cast cap
  have nonzero : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ordered : (l : ℝ) ≤ h := by exact_mod_cast order
  have band (x : ℝ) : (l : ℝ) ≤ x ∧ x ≤ h ↔ F x ≤ u := by
    have factor : (u : ℝ) - F x = (a : ℝ)^2*(x-l)*(h-x) := by
      rw [k]; dsimp [F]; linear_combination (a : ℝ)*(h-x)*m
    rw [show (F x ≤ (u:ℝ)) ↔ 0 ≤ (u:ℝ)-F x from sub_nonneg.symm, factor, mul_assoc, mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero nonzero)]
    exact ⟨fun ⟨p,q⟩ => mul_nonneg (sub_nonneg.mpr p) (sub_nonneg.mpr q),
      fun w => by rcases mul_nonneg_iff.mp w with ⟨_,_⟩ | ⟨_,_⟩ <;> constructor <;> linarith⟩
  have pred : (fun x : ℝ => Value.and (Value.le (some (l : ℝ)) (some x)) (Value.le (some x) (some (h : ℝ)))) =
      (fun x => some (decide (F x ≤ u))) := by
    funext x
    by_cases lo : (l : ℝ) ≤ x <;> by_cases hi : x ≤ (h : ℝ) <;> simp [← band, lo, hi, Value.and, Value.le]
  rw [pred]
  have crit := affine_square_critical_density (a : ℝ) b nonzero
  rw [coordinates_density] at crit
  have bad : densityAtValue (pushforwardOnValue (some fun _ => some true)
    (some fun x => some (F x))) (some 0) = none := crit
  have active : (0 : ℝ) ≤ u := k ▸ sq_nonneg _
  have weight : sublevelWeight false (some (u : ℝ)) =
      fun y => Value.mask (some (decide (y ≤ (u : ℝ)))) (some (1 : ℝ)) := by
    funext y
    simp [sublevelWeight, Value.le]
  rw [weight]
  simpa only [Set.mem_Iic] using
    (restrict_target_chart F (by dsimp [F]; fun_prop) (Set.Iic (u : ℝ)) (critical := 0)
      active bad)

theorem graph_square_congr (p : Option (ℝ → Option Bool)) {f g : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (f x) (Value.mul (some ((-1 : ℤ) : ℝ)) (g x)) = some 0) :
    realPushforwardOnValue p (some f) = realPushforwardOnValue p (some g) := by
  have eq : f = g := by
    funext x
    have h := equal x
    cases hf : f x <;> cases hg : g x <;> simp_all [Value.add, Value.mul] <;> linarith
  rw [eq]

theorem radius_sqrt_cutoff_density (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ}
    (hr : r = sqrtRadius v) (casts : Bool) (k : ℚ) {q : Option ℝ}
    (hq : q = some (k : ℝ)) (y : Option ℝ) :
    densityAtValue (weightValue (some (sublevelWeight casts q)) (radiusImageValue z (some r))) y =
      Value.mask (Value.le y q) (unrestrictedSquareDensity v y) := by
  rw [← radius_sqrt_density c j hj hz hv hr, sublevelWeight_eq casts q, hr, hv, hz, hq,
    radius_coordinates _ _ (by exact_mod_cast hj)]
  cases y with
  | none => rfl
  | some y =>
    let f (x : ℝ) := ((j : ℝ)⁻¹*x + -(c : ℝ)/j)^2
    have weight : (fun x => Value.mul (some (1 : ℝ)) (sublevelWeight false (some (k : ℝ)) (f x))) =
        fun x => Value.mask (some (decide (f x ≤ k))) (some (1 : ℝ)) := by
      funext x
      simp [sublevelWeight, Value.le, Value.mul_one_left]
    change densityAt (.density (fun x => Value.mul (some 1) (sublevelWeight false (some (k : ℝ)) (f x))) (fun x => some (f x))) y = _
    rw [weight]
    exact restrict_target_density f (by dsimp [f]; fun_prop) (Set.Iic (k : ℝ)) y

end QSym.Distribution.GraphFibre
