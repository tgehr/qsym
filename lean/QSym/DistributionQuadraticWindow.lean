import QSym.DistributionQuadraticRestriction
import QSym.DistributionWeightedSquare
import QSym.DistributionBorel
import QSym.DistributionAffine

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Quadratic
open MeasureTheory

/-- Translate the two square branches and rescale the target. Equal signs
at reflected source points preserve absolute integrability of a signed test. -/
theorem weighted_integral (c a b : ℝ) (ha : a ≠ 0) (w : ℝ → ℝ)
    (hw : Measurable w) (hs : ∀ x, 0 ≤ w (-x+c) * w (x+c)) (t : ℝ → ℝ) :
    partialIntegral volume (fun x => some (w x * t (((x-c)^2-b)/a))) =
      partialIntegral volume (fun y => some (|a| * weightedSquareDensity (fun s => w (s+c)) (a*y+b) * t y)) := by
  let g := fun s => w (s+c)
  let h := fun u : ℝ => t ((u-b)/a)
  calc
    _ = partialIntegral volume (fun s => some (g s * h (GraphFibre.square s))) := by
      apply affine_integral 1 (-c) one_ne_zero
      intro x
      simp [g, h, GraphFibre.square, sub_eq_add_neg, Value.mul]
    _ = partialIntegral volume (fun u => some (weightedSquareDensity g u * h u)) :=
      weighted_square_integral g (hw.comp (measurable_id.add measurable_const)) hs h
    _ = _ := by
      apply affine_integral a⁻¹ (-b/a) (inv_ne_zero ha)
      intro u
      have input : a⁻¹*u + -b/a = (u-b)/a := by ring
      have back : a*((u-b)/a)+b = u := by field_simp
      simp only [input, back, g, h, Value.mul, Option.some_bind, Option.map_some,
        abs_inv, inv_inv, mul_assoc]

private def maskWeight (p : ℝ → Option Bool) (x : ℝ) : ℝ := if p x = some true then 1 else 0

private theorem maskWeight_eq (p : ℝ → Option Bool) (hp : ∀ x, Value.Defined (p x)) (x : ℝ) :
    Value.mask (p x) (some (1:ℝ)) = some (maskWeight p x) := by
  obtain ⟨v,h⟩ := hp x
  cases v <;> simp [maskWeight, h, Value.mask]

private theorem masked_rows (p : ℝ → Option Bool) (hp : ∀ x, Value.Defined (p x))
    (c a u : ℝ) (h0 : p c = some false) :
    guardedBranches (some p) (some c) (some |a|) (some u) =
      some (|a| * weightedSquareDensity (fun s => maskWeight p (s+c)) u) := by
  rcases lt_trichotomy u 0 with hn | rfl | hp'
  · simp [guardedBranches, weightedSquareDensity, Value.le, Value.mask, not_le.mpr hn, not_lt_of_gt hn]
  · simp [guardedBranches, weightedSquareDensity, Functions.sqrtR, Function1.apply,
        Value.le, Value.mask, Value.add, Value.mul, h0]
  · obtain ⟨l,hl⟩ := hp (-√u+c)
    obtain ⟨r,hr⟩ := hp (√u+c)
    have hs := (Real.sqrt_pos.mpr hp').ne'
    cases l <;> cases r <;> simp [guardedBranches, weightedSquareDensity, maskWeight, jac, hp', hp'.le,
      Functions.sqrtR, Function1.apply, Value.le, Value.mask, Value.add, Value.mul, Value.inv,
      hs, add_comm c, hl, hr, mul_comm, mul_assoc]
    ring

/-- A total measurable source mask excluding the quadratic vertex produces
ordinary Lebesgue coordinates with the pointwise sum of both inverse branches. -/
theorem masked_chart (c a b : ℝ) (ha : a ≠ 0) (p : ℝ → Option Bool) (hm : BorelPred p)
    (hp : ∀ x, Value.Defined (p x)) (h0 : p c = some false) :
    realPushforwardOnValue (some p) (some fun x => some (((x-c)^2-b)/a)) =
      weightValue (some fun y => guardedBranches (some p) (some c) (some |a|) (some (a*y+b))) lebesgueValue := by
  let d := Presentation.density (fun x => Value.mask (p x) (some (1:ℝ))) (fun x => some (((x-c)^2-b)/a))
  let w := fun y => guardedBranches (some p) (some c) (some |a|) (some (a*y+b))
  have chart : LebesgueChart d w := by
    constructor
    · funext y
      rw [← coordinates_density]
      exact restricted_branches c a b y ha p
    · exact fun y => ⟨_, masked_rows p hp c a _ h0⟩
    · intro test
      have meas : Measurable (maskWeight p) := measurable_const.ite (hm true) measurable_const
      have pos (s : ℝ) : 0 ≤ maskWeight p s := by unfold maskWeight; split <;> norm_num
      have law := weighted_integral c a b ha (maskWeight p) meas (fun x => mul_nonneg (pos _) (pos _)) test
      simpa only [d, w, integrate, maskWeight_eq p hp, masked_rows p hp c a _ h0, Option.some_bind,
        Value.mul, Option.map_some] using law
  change some (inLebesgueCoordinates d) = _
  rw [inLebesgueCoordinates_of_chart chart]
  simp [weightValue, weight, lebesgueValue, densityValue, Value.mul_one_left, w]

/-- A polynomial identity, a total Borel predicate, and exclusion of the
vertex suffice to certify the entire source chart. -/
theorem masked_chart_source (c a b j : ℚ) (ha : a ≠ 0) (hj : j = |a|) {h t u gain : Option ℝ}
    (hc : h = some (c:ℝ)) (ht : t = some (a:ℝ)) (hu : u = some (b:ℝ)) (hg : gain = some (j:ℝ))
    {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) u)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0)
    (p : ℝ → Option Bool) (hm : BorelPred p) (hp : ∀ x, Value.Defined (p x))
    (h0 : h.bind p = some false) :
    realPushforwardOnValue (some p) (some f) = weightValue (some fun y =>
      guardedBranches (some p) h gain (Value.add (Value.mul t (some y)) u)) lebesgueValue := by
  subst h; subst t; subst u; subst gain; subst j
  have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  rw [funext (equation c a b hn equal), Rat.cast_abs]
  exact masked_chart c a b hn p hm hp h0

end QSym.Distribution.GraphFibre.Coordinates.Quadratic
