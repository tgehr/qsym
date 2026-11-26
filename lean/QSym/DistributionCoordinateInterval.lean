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
end QSym.Distribution.GraphFibre.Coordinates.Grid
