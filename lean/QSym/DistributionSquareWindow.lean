import QSym.DistributionRadiusImage

noncomputable section
namespace QSym.Distribution.GraphFibre
open Classical MeasureTheory Set

/-- Transport a source predicate through the affine square, preserving the
entire distribution when the target restriction retains the critical value. -/
private theorem square_target_window (a b j : ℚ) (ha : a ≠ 0) (hj : j = |a⁻¹|)
    {f : ℝ → Option ℝ} (hf : StepSource.Affine f a b) {z v : Option ℝ}
    (hz : z = some ((-b/a : ℚ) : ℝ)) (hv : v = some (j : ℝ)) (product : Bool)
    (s : Set ℝ) [DecidablePred (· ∈ s)] (active : 0 ∈ s)
    (p : ℝ → Option Bool) (w : ℝ → Option ℝ)
    (hp : ∀ x : ℝ, p x = some (decide (((a:ℝ)*x+b)^2 ∈ s)))
    (hw : ∀ y : ℝ, w y = Value.mask (some (decide (y ∈ s))) (some 1)) :
    realPushforwardOnValue (some p) (some fun x => squareInput product (f x)) =
      weightValue (some w) (radiusImageValue z (some (sqrtRadius v))) := by
  rw [← affineSquare_radius_image a b j ha hj hf hz hv product]
  let F (x : ℝ) := ((a:ℝ)*x+b)^2
  have map_eq : (fun x => squareInput product (f x)) = fun x => some (F x) := by
    funext x; rw [hf.equation]; cases product <;> simp [F, squareInput, Value.mul, pow_two]
  have crit := affine_square_critical_density (a:ℝ) b (by exact_mod_cast ha)
  rw [coordinates_density] at crit
  rw [map_eq, funext hp, funext hw]
  exact restrict_target_chart F (by dsimp [F]; fun_prop) s active crit

private theorem square_window_gap (a b l h u : ℚ) (mid : a*(l+h)+2*b = 0)
    (cap : u = (a*h+b)^2) (x : ℝ) :
    (u:ℝ) - ((a:ℝ)*x+b)^2 = (a:ℝ)^2*(x-l)*(h-x) := by
  have m : (a:ℝ)*(l+h)+2*b = 0 := by exact_mod_cast mid
  have k : (u:ℝ) = ((a:ℝ)*h+b)^2 := by exact_mod_cast cap
  rw [k]; linear_combination (a:ℝ)*(h-x)*m

theorem closedBand_square_chart (a b j : ℚ) (ha : a ≠ 0) (hj : j = |a⁻¹|)
    {f : ℝ → Option ℝ} (hf : StepSource.Affine f a b) {z v : Option ℝ}
    (hz : z = some ((-b/a : ℚ) : ℝ)) (hv : v = some (j : ℝ)) (product : Bool)
    (l h u : ℚ) (order : l ≤ h) (mid : a*(l+h)+2*b = 0) (cap : u = (a*h+b)^2)
    {lo hi top : Option ℝ} (hl : lo = some (l : ℝ)) (hh : hi = some (h : ℝ))
    (hu : top = some (u : ℝ)) :
    realPushforwardOnValue (some fun x => Value.and (Value.le lo (some x)) (Value.le (some x) hi))
        (some fun x => squareInput product (f x)) =
      weightValue (some (sublevelWeight false top)) (radiusImageValue z (some (sqrtRadius v))) := by
  subst lo; subst hi; subst top
  have k : (u : ℝ) = ((a : ℝ)*h+b)^2 := by exact_mod_cast cap
  have nonzero : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ordered : (l : ℝ) ≤ h := by exact_mod_cast order
  let F (x : ℝ) := ((a:ℝ)*x+b)^2
  have band (x : ℝ) : (l : ℝ) ≤ x ∧ x ≤ h ↔ F x ≤ u := by
    have factor := square_window_gap a b l h u mid cap x
    rw [show (F x ≤ (u:ℝ)) ↔ 0 ≤ (u:ℝ)-F x from sub_nonneg.symm, factor, mul_assoc, mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero nonzero)]
    exact ⟨fun ⟨p,q⟩ => mul_nonneg (sub_nonneg.mpr p) (sub_nonneg.mpr q),
      fun w => by rcases mul_nonneg_iff.mp w with ⟨_,_⟩ | ⟨_,_⟩ <;> constructor <;> linarith⟩
  have active : (0:ℝ) ≤ u := k ▸ sq_nonneg _
  apply square_target_window a b j ha hj hf hz hv product (Iic (u:ℝ)) active
  · intro x; change _ = some (decide (F x ≤ u))
    by_cases lo : (l : ℝ) ≤ x <;> by_cases hi : x ≤ (h : ℝ) <;> simp [← band, lo, hi, Value.and, Value.le]
  · intro y; simp [sublevelWeight, windowWeight, windowCompare, Value.le]

theorem openBand_square_chart (a b j : ℚ) (ha : a ≠ 0) (hj : j = |a⁻¹|)
    {f : ℝ → Option ℝ} (hf : StepSource.Affine f a b) {z v : Option ℝ}
    (hz : z = some ((-b/a : ℚ) : ℝ)) (hv : v = some (j : ℝ)) (product : Bool)
    (l h u : ℚ) (order : l < h) (mid : a*(l+h)+2*b = 0) (cap : u = (a*h+b)^2)
    {lo hi top : Option ℝ} (hl : lo = some (l : ℝ)) (hh : hi = some (h : ℝ))
    (hu : top = some (u : ℝ)) :
    realPushforwardOnValue (some fun x => Value.and (Value.lt lo (some x)) (Value.lt (some x) hi))
        (some fun x => squareInput product (f x)) =
      weightValue (some (windowWeight true false top)) (radiusImageValue z (some (sqrtRadius v))) := by
  subst lo; subst hi; subst top
  have nonzero : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ordered : (l : ℝ) < h := by exact_mod_cast order
  let F (x : ℝ) := ((a:ℝ)*x+b)^2
  have band (x : ℝ) : (l : ℝ) < x ∧ x < h ↔ F x < u := by
    have factor := square_window_gap a b l h u mid cap x
    rw [show (F x < (u:ℝ)) ↔ 0 < (u:ℝ)-F x from sub_pos.symm, factor, mul_assoc,
      mul_pos_iff_of_pos_left (sq_pos_of_ne_zero nonzero)]
    constructor
    · rintro ⟨hx, hy⟩; exact mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)
    · intro h; rcases mul_pos_iff.mp h with ⟨_,_⟩ | ⟨_,_⟩ <;> constructor <;> linarith
  have active : (0:ℝ) < u := by
    have hmid := (band (((l:ℝ)+h)/2)).mp ⟨by linarith, by linarith⟩
    exact (sq_nonneg _).trans_lt hmid
  apply square_target_window a b j ha hj hf hz hv product (Iio (u:ℝ)) active
  · intro x; change _ = some (decide (F x < u))
    by_cases lo : (l : ℝ) < x <;> by_cases hi : x < (h : ℝ) <;> simp [← band, lo, hi, Value.and, Value.lt]
  · intro y; simp [windowWeight, windowCompare, Value.lt]

theorem graph_square_congr (p : Option (ℝ → Option Bool)) {f g : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (f x) (Value.mul (some ((-1 : ℤ) : ℝ)) (g x)) = some 0) :
    realPushforwardOnValue p (some f) = realPushforwardOnValue p (some g) := by
  have eq : f = g := by
    funext x
    have h := equal x
    cases hf : f x <;> cases hg : g x <;> simp_all [Value.add, Value.mul] <;> linarith
  rw [eq]

theorem radius_sqrt_window_density (strict : Bool) (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ}
    (hr : r = sqrtRadius v) (casts : Bool) (k : ℚ) {q : Option ℝ}
    (hq : q = some (k : ℝ)) (y : Option ℝ) :
    densityAtValue (weightValue (some (windowWeight strict casts q)) (radiusImageValue z (some r))) y =
      Value.mask (windowCompare strict y q) (unrestrictedSquareDensity v y) := by
  rw [← radius_sqrt_density c j hj hz hv hr, windowWeight_eq strict casts q, hr, hv, hz, hq,
    radius_coordinates _ _ (by exact_mod_cast hj)]
  cases y with
  | none => cases strict <;> rfl
  | some y =>
    let f (x : ℝ) := ((j : ℝ)⁻¹*x + -(c : ℝ)/j)^2
    have weight : (fun x => Value.mul (some (1 : ℝ)) (windowWeight strict false (some (k : ℝ)) (f x))) =
        fun x => Value.mask (some (decide (f x ∈ (if strict then Iio (k:ℝ) else Iic (k:ℝ))))) (some (1 : ℝ)) := by
      funext x
      cases strict <;> simp [windowWeight, windowCompare, Value.le, Value.lt, Value.mul_one_left]
    change densityAt (.density (fun x => Value.mul (some 1) (windowWeight strict false (some (k : ℝ)) (f x))) (fun x => some (f x))) y = _
    rw [weight]
    cases strict
    · exact restrict_target_density f (by dsimp [f]; fun_prop) (Iic (k:ℝ)) y
    · exact restrict_target_density f (by dsimp [f]; fun_prop) (Iio (k:ℝ)) y

theorem radius_sqrt_cutoff_density (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ}
    (hr : r = sqrtRadius v) (casts : Bool) (k : ℚ) {q : Option ℝ}
    (hq : q = some (k : ℝ)) (y : Option ℝ) :
    densityAtValue (weightValue (some (sublevelWeight casts q)) (radiusImageValue z (some r))) y =
      Value.mask (Value.le y q) (unrestrictedSquareDensity v y) :=
  radius_sqrt_window_density false c j hj hz hv hr casts k hq y

end QSym.Distribution.GraphFibre
