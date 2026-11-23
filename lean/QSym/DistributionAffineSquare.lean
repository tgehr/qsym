import QSym.DistributionSquareExpression
import QSym.DistributionAffineExpression
import QSym.DistributionSquareChart
import QSym.DistributionBorel

noncomputable section
namespace QSym.Distribution.GraphFibre

def squareInput (product : Bool) (x : Option ℝ) : Option ℝ :=
  if product then Value.mul x x else x.map (· ^ 2)

def signedSqrt (neg : Bool) (y : Option ℝ) : Option ℝ :=
  let s := Functions.sqrtR.apply y
  if neg then Value.mul (some ((-1 : ℤ) : ℝ)) s else s

variable (a b j : ℚ) {f i : ℝ → Option ℝ} {v : Option ℝ}
variable (ha : a ≠ 0) (hj : j = |a⁻¹|) (hf : StepSource.Affine f a b)
variable (hi : StepSource.Affine i a⁻¹ (-b/a)) (hv : v = some (j : ℝ))
variable (num den : ℚ) {u v' : Option ℝ} (hn : den ≠ 0) (hd : num = (2 * |a|)*den)
variable (hu : u = some (num : ℝ)) (hv' : v' = some (den : ℝ))

include ha hj hf hi hv hn hd hu hv' in
def affineSquareExpression (product : Bool) :
    SquareExpression (fun x => squareInput product (f x))
      (fun y => (signedSqrt (decide (0 < a)) y).bind i)
      (fun y => (signedSqrt (!(decide (0 < a))) y).bind i)
      (fun y => rationalInvMul den u v' (Functions.sqrtR.apply y)) (i ((0 : ℤ) : ℝ)) := by
  let c := affineExpression a b j ha hj hf hi hv
  let F := fun x => (c.f x)^2
  let D := fun x => (2*c.f x)*(a : ℝ)
  have diff (x : ℝ) : HasStrictDerivAt F (D x) x := by
    have pow : HasStrictDerivAt (fun t : ℝ => t^2) (2*c.f x) (c.f x) := by
      simpa using hasStrictDerivAt_pow 2 (c.f x)
    exact pow.comp x (c.branch.derivative x)
  refine ⟨F, D, ?_, diff, ?_⟩
  · intro x
    rw [hf.equation]
    cases product <;> simp [F, c, affineExpression, squareInput, Value.mul, pow_two]
  · intro y
    have inv (t : ℝ) : i t = some (c.root t) := c.inverse_eq (some t)
    have atRoot (t : ℝ) : D (c.root t) = (2*t)*(a : ℝ) := by simp [D, c.branch.inverse t]
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · exact ⟨[], squareCover_negative c.f hy, by
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hy, not_lt_of_ge hy.le]⟩
    · exact ⟨[c.root 0], squareCover_zero c.branch, by
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, inv, atRoot, Value.inv]⟩
    · have hs := Real.sqrt_pos.mpr hy
      have zero : (0 : ℝ) ≤ y := hy.le
      have s : Functions.sqrtR.apply (some y) = some (√y) := by
        simp [Function1.apply, Functions.sqrtR, zero]
      have J : rationalInvMul den u v' (some (√y)) = Value.inv (some ((2*|(a : ℝ)|)*√y)) := by
        rw [hu, hv', hd]
        push_cast
        exact rationalInvMul_some hn _ _
      have wp (t : ℝ) (ht : |t| = √y) : |D (c.root t)| = (2*|(a : ℝ)|)*√y := by
        rw [atRoot, abs_mul, abs_mul, ht, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring
      have n := wp (-√y) (by simp [abs_of_pos hs])
      have p := wp (√y) (abs_of_pos hs)
      rcases lt_or_gt_of_ne ha with neg | pos
      · have h : (a : ℝ) < 0 := by exact_mod_cast neg
        have order : c.root (√y) < c.root (-√y) := by
          change (√y-b)/(a : ℝ) < (-√y-b)/(a : ℝ)
          exact (div_lt_div_right_of_neg h).mpr (by linarith)
        refine ⟨_, squareCover_positive c.branch hy order (Or.inr ⟨rfl,rfl⟩), ?_⟩
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hy, signedSqrt, not_lt_of_gt neg,
          s, J, Value.mul, inv, n, p]
      · have h : 0 < (a : ℝ) := by exact_mod_cast pos
        have order : c.root (-√y) < c.root (√y) := by
          change (-√y-b)/(a : ℝ) < (√y-b)/(a : ℝ)
          exact (div_lt_div_iff_of_pos_right h).mpr (by linarith)
        refine ⟨_, squareCover_positive c.branch hy order (Or.inl ⟨rfl,rfl⟩), ?_⟩
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hy, signedSqrt, pos,
          s, J, Value.mul, inv, n, p]

def affineSquareWeight (a den : ℚ) (i : ℝ → Option ℝ) (u v : Option ℝ) (p : ℝ → Option Bool) :=
  squareChartValue (fun y => (signedSqrt (decide (0 < a)) y).bind i)
    (fun y => (signedSqrt (!(decide (0 < a))) y).bind i)
    (fun y => rationalInvMul den u v (Functions.sqrtR.apply y)) p

private theorem mask_of_total {p : ℝ → Option Bool} (hp : ∀ x, Value.Defined (p x)) (x c : ℝ) :
    Value.mask (p x) (some c) = some (if p x = some true then c else 0) := by
  obtain ⟨b, hb⟩ := hp x
  cases b <;> simp [hb, Value.mask]

include ha hj hf hi hv hn hd hu hv' in
private theorem chartWeight_eq (p : ℝ → Option Bool) (hp : ∀ x, Value.Defined (p x)) (y : ℝ) :
    affineSquareWeight a den i u v' p y = some
      (squareChartWeight ((fun t : ℝ => (t-b)/a) ⁻¹' {x | p x = some true}) y * |(a : ℝ)|⁻¹) := by
  classical
  have root (t : ℝ) : i t = some ((t-b)/(a : ℝ)) := (affineExpression a b j ha hj hf hi hv).inverse_eq (some t)
  by_cases hy : 0 < y
  · have sq := Real.sqrt_pos.mpr hy
    have an : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have sr : Functions.sqrtR.apply (some y) = some (√y) := by simp [Function1.apply, Functions.sqrtR, hy.le]
    have jw : rationalInvMul den u v' (some (√y)) = some (jac y * |(a : ℝ)|⁻¹) := by
      rw [hu, hv', hd]
      push_cast
      rw [rationalInvMul_some hn]
      simp [Value.inv, jac, sq.ne', an, mul_inv_rev]
      ring
    by_cases orient : 0 < a <;>
      simp [affineSquareWeight, squareChartValue, squareChartWeight, signedSqrt, sr, orient, hy, Value.lt,
        Value.mul, jw, root, mask_of_total hp, Value.add, Set.mem_preimage, add_mul, ite_mul, add_comm] <;> rfl
  · simp [affineSquareWeight, squareChartValue, squareChartWeight, hy, Value.lt, Value.mask]

include ha hj hf hi hv hn hd hu hv' in
/-- Replace the entire graph when the source guard is total, measurable and
false at the critical source. Both positive-target branches may be active. -/
theorem affineSquare_chart_rule (product : Bool) (p : ℝ → Option Bool) (hm : BorelPred p)
    (hp : ∀ x, Value.Defined (p x)) (h0 : (i ((0 : ℤ) : ℝ)).bind p = some false) :
    realPushforwardOnValue (some p) (some fun x => squareInput product (f x)) =
      weightValue (some (affineSquareWeight a den i u v' p)) lebesgueValue := by
  classical
  let src : D ℝ := .density (fun x => Value.mask (p x) (some 1)) (fun x => squareInput product (f x))
  let w := affineSquareWeight a den i u v' p
  have weight_eq := chartWeight_eq a b j ha hj hf hi hv num den hn hd hu hv' p hp
  have an : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have forward (x : ℝ) : squareInput product (f x) = some (((a : ℝ)*x+b)^2) := by
    rw [hf.equation]
    cases product <;> simp [squareInput, Value.mul, pow_two]
  have chart : LebesgueChart src w := by
    constructor
    · funext y
      have he := (affineSquareExpression a b j ha hj hf hi hv num den hn hd hu hv' product).chart_density p h0 y
      change densityAt (inLebesgueCoordinates src) y = w y at he
      rwa [coordinates_density] at he
    · exact fun y => ⟨_, weight_eq y⟩
    · intro t
      change partialIntegral _ (fun x => Value.mul (Value.mask (p x) (some 1)) ((squareInput product (f x)).bind fun y => some (t y))) =
        partialIntegral _ (fun y => Value.mul (w y) (some (t y)))
      calc
        _ = partialIntegral _ (fun x => some (if x ∈ {x | p x = some true} then t (((a : ℝ)*x+b)^2) else 0)) := by
          apply congrArg (partialIntegral _)
          funext x
          rw [mask_of_total hp]
          by_cases hx : p x = some true <;> simp [forward, hx, Value.mul]
        _ = _ := by
          rw [affine_square_integral _ (hm true) _ _ an]
          apply congrArg (partialIntegral _)
          funext y
          rw [show w y = _ from weight_eq y]
          rfl
  change some (inLebesgueCoordinates src) = weightValue (some w) lebesgueValue
  rw [inLebesgueCoordinates_of_chart chart]
  simp [weightValue, weight, lebesgueValue, densityValue, Value.mul_one_left]

include ha hj hf hi hv hn hd hu hv' in
/-- An affine nonzero guard that excludes the critical source excludes no
regular roots. Combine their equal weights on the positive half-line. -/
theorem affineSquare_puncture_rule (product : Bool) (c d : ℚ) {g : ℝ → Option ℝ}
    (hc : c ≠ 0) (hg : StepSource.Affine g c d)
    (h0 : (i ((0 : ℤ) : ℝ)).bind (fun x => Value.nonzero (g x)) = some false) :
    realPushforwardOnValue (some fun x => Value.nonzero (g x)) (some fun x => squareInput product (f x)) =
      weightValue (some fun y => Value.mask (Value.lt (some ((0 : ℤ) : ℝ)) (some y))
        (Value.mul (Value.inv (Functions.sqrtR.apply (some y))) v)) lebesgueValue := by
  let p := fun x => Value.nonzero (g x)
  have hm : BorelReal g := by
    rw [funext hg.equation]
    exact ⟨by simp [Value.Defined], by simp only [Option.getD_some]; fun_prop⟩
  have hp (x) : Value.Defined (p x) := by
    unfold p
    rw [hg.equation]
    exact ⟨_, rfl⟩
  rw [affineSquare_chart_rule a b j ha hj hf hi hv num den hn hd hu hv' product p (BorelPred.nonzero hm) hp h0]
  apply congrArg (fun w => weightValue (some w) lebesgueValue)
  funext y
  rw [chartWeight_eq a b j ha hj hf hi hv num den hn hd hu hv' p hp]
  by_cases hy : 0 < y
  · have root : i 0 = some ((0-b)/(a : ℝ)) := (affineExpression a b j ha hj hf hi hv).inverse_eq (some 0)
    have zero : (c : ℝ)*((0-b)/(a : ℝ))+d = 0 := by simpa [root, hg.equation, Value.nonzero] using h0
    have active (t : ℝ) (ht : t ≠ 0) : p ((t-b)/(a : ℝ)) = some true := by
      have cn : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      have an : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      have nz : (c : ℝ)*((t-b)/(a : ℝ))+d ≠ 0 := by
        intro he
        have same := (div_left_inj' an).mp (mul_left_cancel₀ cn (add_right_cancel (he.trans zero.symm)))
        exact ht (sub_left_inj.mp same)
      simp [p, Value.nonzero, hg.equation, nz]
    have sq := (Real.sqrt_pos.mpr hy).ne'
    simp [squareChartWeight, Set.mem_preimage, hy, active _ sq, active _ (neg_ne_zero.mpr sq), Value.lt,
      Value.mask, Value.inv, Value.mul, Function1.apply, Functions.sqrtR, hy.le, hv, hj, jac, sq, mul_inv_rev, abs_inv, ha]
    ring
  · simp [squareChartWeight, hy, Value.lt, Value.mask]

end QSym.Distribution.GraphFibre
