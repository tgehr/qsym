import QSym.DistributionCoordinateGridChange
import QSym.DistributionInterval

/-! Total variation on a finite interval for a smooth monotone coordinate.
The interval endpoints may themselves be partial qsym values. -/
noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid
open Set Filter Topology MeasureTheory StepSource

/-- Orientation and smoothness of the actual source function. -/
def Directed (down : Bool) (f : Scalar) : Prop :=
  ∃ g : ℝ → ℝ, ContDiff ℝ 1 g ∧ (if down then Antitone g else Monotone g) ∧
    ∀ x, f x = some (g x)

namespace Directed

theorem affine {f a b} (down : Bool) (h : StepSource.Affine f a b)
    (hs : decide (if down then a ≤ 0 else 0 ≤ a) = true) : Directed down f := by
  refine ⟨fun x => (a : ℝ)*x+b, by fun_prop, ?_, h.equation⟩
  cases down
  · have ha : (0 : ℝ) ≤ a := by exact_mod_cast (of_decide_eq_true hs : (0 : ℚ) ≤ a)
    exact fun _ _ hxy => add_le_add_right (mul_le_mul_of_nonneg_left hxy ha) _
  · have ha : (a : ℝ) ≤ 0 := by exact_mod_cast (of_decide_eq_true hs : a ≤ (0 : ℚ))
    exact fun _ _ hxy => add_le_add_right (mul_le_mul_of_nonpos_left hxy ha) _

theorem constant (down : Bool) {v : Option ℝ} {r : ℝ} (h : v = some r) :
    Directed down (fun _ => v) := by
  refine ⟨fun _ => r, contDiff_const, ?_, fun _ => h⟩
  cases down <;> exact fun _ _ _ => le_rfl

theorem change {g op jac down f} (c : ScalarChange univ g op jac) (inc : Monotone g)
    (h : Directed down f) : Directed down (fun x => op (f x)) := by
  obtain ⟨v, sm, mon, src⟩ := h
  refine ⟨g ∘ v, (contDiff_iff_contDiffAt.mpr fun u => c.change.smooth u trivial).comp sm, ?_,
    fun x => by simp only [src, Function.comp_apply]; exact c.value _ trivial⟩
  cases down
  · exact inc.comp mon
  · exact inc.comp_antitone mon

theorem oddPower {down f} (n : ℕ) (odd : n % 2 = 1) (h : Directed down f) :
    Directed down (fun x => (f x).map (· ^ n)) := by
  obtain ⟨v, sm, mon, src⟩ := h
  have inc : Monotone (fun x : ℝ => x^n) := (Nat.odd_iff.mpr odd).strictMono_pow.monotone
  refine ⟨fun x => v x^n, sm.pow n, ?_, fun x => by simp [src]⟩
  cases down
  · exact inc.comp mon
  · exact inc.comp_antitone mon

theorem add {down f k} (h : Directed down f) (j : Directed down k) :
    Directed down (fun x => Value.add (f x) (k x)) := by
  obtain ⟨v, sm, mon, src⟩ := h
  obtain ⟨w, sw, m, sk⟩ := j
  refine ⟨fun x => v x+w x, sm.add sw, ?_, fun x => by simp [src, sk, Value.add]⟩
  cases down <;> exact fun _ _ hxy => add_le_add (mon hxy) (m hxy)

/-- On the interval the two endpoint values determine the mass. The mask
retains the order and definedness of the actual comparisons. -/
theorem interval {w : Scalar} (F : Option ℝ → Option ℝ) (down swap sl su : Bool) (a b m : Option ℝ)
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (h : Directed down (fun x => F (some x)))
    (hw : ∀ x, w x = Value.mask (intervalGuard swap sl su a b x) (some (1:ℝ))) :
    massValue (weightValue (some w) (value (Tensor.consValue (some fun x => F (some x)) Tensor.nilValue))) =
      Value.mask (compare (sl || su) a b)
        (if down then Value.add (F a) (Value.mul m (F b))
         else Value.add (F b) (Value.mul m (F a))) := by
  obtain ⟨g, hg, mon, src⟩ := h
  rw [singleton_length hg src (w := fun x => some |deriv g x|) (fun _ => rfl), weight_weight_lebesgue,
    weighted_lebesgue_mass_bridge, Model.densityMassValue_eq]
  apply interval_integral swap sl su a b m hm (v := fun x => some |deriv g x|)
  · constructor
    intro x
    rw [hw x]
    rcases intervalGuard swap sl su a b x with _ | _ | _ <;> simp [Value.mask, Value.mul]
  · apply IntervalTerms.value (fun _ => rfl) (hg.continuous_deriv le_rfl).abs
    intro l u ha hb hm'
    subst a b
    rw [hm']
    have hd := hg.differentiable le_rfl
    simp only [src, Value.mul, Value.add, Option.some.injEq]
    cases down
    · have sign (x : ℝ) := abs_of_nonneg (nonneg_deriv_of_monotone (g := g) mon (hd x))
      simp only [Bool.false_eq_true, ↓reduceIte, sign]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g) (fun x _ => (hd x).hasDerivAt)
        ((hg.continuous_deriv le_rfl).intervalIntegrable l u)]
      simp [sub_eq_add_neg, add_comm]
    · have dec : Monotone (fun x => -g x) := fun _ _ hxy => neg_le_neg (mon hxy)
      have sign (x : ℝ) : |deriv g x| = -deriv g x := by
        have h := nonneg_deriv_of_monotone dec (hd x).neg
        rw [deriv.neg] at h
        exact abs_of_nonpos (neg_nonneg.mp h)
      simp only [↓reduceIte, sign, intervalIntegral.integral_neg]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g) (fun x _ => (hd x).hasDerivAt)
        ((hg.continuous_deriv le_rfl).intervalIntegrable l u)]
      simp [sub_eq_add_neg, add_comm]

end Directed

/-- An increasing primitive of the absolute derivative of an outer coordinate. -/
structure VariationChange (h k : ℝ → ℝ) (op prim : Option ℝ → Option ℝ) : Prop where
  smooth : ContDiff ℝ 1 h
  smoothPrimitive : ContDiff ℝ 1 k
  increasing : Monotone k
  slope : ∀ x, deriv k x = |deriv h x|
  source : ∀ x, op (some x) = some (h x)
  endpoint : ∀ x, prim (some x) = some (k x)

namespace VariationChange

/-- Reverse the descending part of a smooth function having its minimum at zero. -/
def turn (h : ℝ → ℝ) (x : ℝ) := if x < 0 then h 0 - h x else h x - h 0

theorem ofTurn {h op prim} (sm : ContDiff ℝ 1 h) (flat : deriv h 0 = 0)
    (left : ∀ x < 0, deriv h x ≤ 0) (right : ∀ x, 0 ≤ x → 0 ≤ deriv h x)
    (ev : ∀ x, op (some x) = some (h x)) (ep : ∀ x, prim (some x) = some (turn h x)) :
    VariationChange h (turn h) op prim := by
  have d (x : ℝ) := (sm.differentiable le_rfl x).hasDerivAt
  have dl (x : ℝ) : HasDerivAt (fun t => h 0 - h t) (-deriv h x) x := (d x).const_sub _
  have dr (x : ℝ) : HasDerivAt (fun t => h t - h 0) (deriv h x) x := (d x).sub_const _
  have s : ContDiff ℝ 1 (turn h) := contDiff_join (contDiff_const.sub sm) (sm.sub contDiff_const)
    rfl (by rw [(dl 0).deriv, (dr 0).deriv, flat, neg_zero])
  have hd (x : ℝ) : HasDerivAt (turn h) |deriv h x| x := by
    have eq := hasDerivAt_join dl dr (a := 0) rfl (by rw [flat, neg_zero]) x
    by_cases hx : x < 0
    · simpa only [if_pos hx, abs_of_nonpos (left x hx)] using eq
    · simpa only [if_neg hx, abs_of_nonneg (right x (le_of_not_gt hx))] using eq
  exact ⟨sm, s, monotone_of_hasDerivAt_nonneg hd (fun x => abs_nonneg _), fun x => (hd x).deriv, ev, ep⟩

/-- A smooth substitution preserves equality of absolute derivatives. The
chart equality includes the critical points of both composed coordinates. -/
theorem length {h k op prim} {f : Scalar} {g : ℝ → ℝ} (c : VariationChange h k op prim) (sg : ContDiff ℝ 1 g)
    (fs : ∀ x, f x = some (g x)) :
    value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue) =
      value (Tensor.consValue (some fun x => prim (f x)) Tensor.nilValue) := by
  have eq (x : ℝ) : |deriv (k ∘ g) x| = |deriv (h ∘ g) x| := by
    rw [deriv_comp x (c.smoothPrimitive.differentiable le_rfl _) (sg.differentiable le_rfl _),
      deriv_comp x (c.smooth.differentiable le_rfl _) (sg.differentiable le_rfl _), c.slope,
      abs_mul, abs_abs, abs_mul]
  exact (singleton_length (c.smooth.comp sg) (fun x => by simpa [fs] using c.source (g x))
    (w := fun x => some |deriv (h ∘ g) x|) (fun _ => rfl)).trans
    (singleton_length (c.smoothPrimitive.comp sg) (fun x => by simpa [fs] using c.endpoint (g x))
      (fun x => congrArg some (eq x).symm)).symm

theorem directed {h k op prim f down} (c : VariationChange h k op prim) (v : Directed down f) :
    Directed down (fun x => prim (f x)) := by
  obtain ⟨g, sg, mon, fs⟩ := v
  refine ⟨k ∘ g, c.smoothPrimitive.comp sg, ?_, fun x => by simp only [fs]; exact c.endpoint _⟩
  cases down
  · exact c.increasing.comp mon
  · exact c.increasing.comp_antitone mon

theorem interval {h k op prim w} (F : Option ℝ → Option ℝ) (c : VariationChange h k op prim)
    (down swap sl su : Bool) (a b m : Option ℝ) (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (v : Directed down (fun x => F (some x)))
    (hw : ∀ x, w x = Value.mask (intervalGuard swap sl su a b x) (some (1:ℝ))) :
    massValue (weightValue (some w) (value (Tensor.consValue (some fun x => op (F (some x))) Tensor.nilValue))) =
      Value.mask (compare (sl || su) a b)
        (if down then Value.add (prim (F a)) (Value.mul m (prim (F b)))
         else Value.add (prim (F b)) (Value.mul m (prim (F a)))) := by
  have directed := c.directed v
  obtain ⟨g, sg, _, fs⟩ := v
  exact (congrArg (fun d => massValue (weightValue (some w) d)) (c.length sg fs)).trans
    (Directed.interval (fun z => prim (F z)) down swap sl su a b m hm directed hw)

/-- For an even power the variation primitive is x·|x|^(n−1) on the whole real line. -/
theorem evenPower (n : ℕ) (hn : 2 ≤ n) (even : n % 2 = 0) :
    VariationChange (fun x : ℝ => x^n) (turn (fun x => x^n)) (fun v => v.map (·^n))
      (fun v => Value.mul v ((Value.abs v).map (·^(n-1)))) := by
  have h0 : n ≠ 0 := by omega
  have h1 : n-1 ≠ 0 := by omega
  have odd : Odd (n-1) := Nat.odd_iff.mpr (by omega)
  have d (x : ℝ) := (hasDerivAt_pow n x).deriv
  apply ofTurn (h := fun x : ℝ => x^n) (contDiff_id.pow n) (by rw [d]; simp [h1])
  · intro x hx
    rw [d]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (odd.pow_nonpos hx.le)
  · intro x hx
    rw [d]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)
  · exact fun _ => rfl
  · intro x
    have prod : x * x^(n-1) = x^n := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    by_cases hx : x < 0
    · simp [Value.abs, Value.mul, turn, hx, abs_of_neg hx, odd.neg_pow, h0, prod]
    · simp [Value.abs, Value.mul, turn, hx, abs_of_nonneg (le_of_not_gt hx), h0, prod]

theorem square : VariationChange (fun x : ℝ => x^2) (turn (fun x => x^2)) (fun v => v.map (·^2))
    (fun v => Value.mul v (Value.abs v)) := by
  have h := evenPower 2 (by decide) rfl
  refine ⟨h.smooth, h.smoothPrimitive, h.increasing, h.slope, h.source, fun x => ?_⟩
  simpa [Value.abs] using h.endpoint x

/-- Use the signed displacement from the minimum to evaluate both sides of cosh. -/
theorem cosh (zero one minus : Option ℝ)
    (hz : zero = some (Numeric.denote (s := .real) (0 : ℚ)))
    (ho : one = some (Numeric.denote (s := .real) (1 : ℚ)))
    (hm : minus = some (Numeric.denote (s := .real) (-1 : ℚ))) :
    VariationChange Real.cosh (turn Real.cosh) Functions.coshR.apply (fun v =>
      let h := Functions.coshR.apply v
      Binding.conditionalValue (Value.lt v zero) (Value.add one (Value.mul minus h)) (Value.add h minus)) := by
  apply ofTurn Real.contDiff_cosh (by rw [(Real.hasDerivAt_cosh _).deriv, Real.sinh_zero])
    (fun x hx => by rw [(Real.hasDerivAt_cosh _).deriv]; exact Real.sinh_nonpos_iff.mpr hx.le)
    (fun x hx => by rw [(Real.hasDerivAt_cosh _).deriv]; exact Real.sinh_nonneg_iff.mpr hx)
  · intro x; simp [Function1.apply, Functions.coshR]
  · intro x
    rw [hz, ho, hm]
    by_cases hx : x < 0 <;>
      simp [Numeric.denote, Function1.apply, Functions.coshR, Binding.conditionalValue, Value.lt, Value.mul,
        Value.add, turn, hx, sub_eq_add_neg]

end VariationChange
end QSym.Distribution.GraphFibre.Coordinates.Grid
