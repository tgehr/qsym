import QSym.DistributionRootInterval
import QSym.DistributionInterval
import QSym.DistributionModelBridge

noncomputable section
namespace QSym.Distribution.RootInterval
open MeasureTheory Set

/-- The two observations of an inverse square root needed by integration. -/
structure Term (w : ℝ → Option ℝ) (a b k : ℚ) : Prop where
  regular : ∀ x, 0 < (a:ℝ)*x+b → w x = some ((k:ℝ) / √((a:ℝ)*x+b))
  missing : ∀ x, (a:ℝ)*x+b ≤ 0 → w x = none

theorem Term.inverse {v a b} (h : StepSource.Affine v a b) :
    Term (fun x => Value.inv (Functions.sqrtR.apply (v x))) a b 1 where
  regular x hx := by simp [h x, Functions.sqrtR, Function1.apply, hx.le, Value.inv,
    (Real.sqrt_pos.mpr hx).ne', one_div]
  missing x hx := by
    rcases lt_or_eq_of_le hx with hn | hz
    · simp [h x, Functions.sqrtR, Function1.apply, not_le.mpr hn, Value.inv]
    · simp [h x, Functions.sqrtR, Function1.apply, hz, Value.inv]

theorem Term.left {w a b k} (c : ℚ) {v : Option ℝ} (hc : v = some (c:ℝ)) (h : Term w a b k) :
    Term (fun x => Value.mul v (w x)) a b (c*k) where
  regular x hx := by simp [hc, h.regular x hx, Value.mul, div_eq_mul_inv, mul_assoc]
  missing x hx := by simp [hc, h.missing x hx, Value.mul]

theorem Term.right {w a b k} (c : ℚ) {v : Option ℝ} (hc : v = some (c:ℝ)) (h : Term w a b k) :
    Term (fun x => Value.mul (w x) v) a b (c*k) where
  regular x hx := by simp [hc, h.regular x hx, Value.mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  missing x hx := by simp [hc, h.missing x hx, Value.mul]

private theorem ordinary (a b l u k : ℝ) (ha : a ≠ 0) (hlu : l ≤ u)
    (hl : 0 ≤ a*l+b) (hu : 0 ≤ a*u+b) :
    IntegrableOn (fun y => k / √(a*y+b)) (Ioo l u) ∧
      (∫ y in Ioo l u, k / √(a*y+b)) = (2*k/a)*(√(a*u+b)-√(a*l+b)) := by
  let g := (Ioo l u).indicator (fun y => k / √(a*y+b))
  have obs := integral a b l u k ha hlu hl hu (fun y => some (g y)) []
    (fun _ => ⟨_,rfl⟩) (fun y _ => by simp [g, Set.indicator, Set.mem_Ioo])
  have hi : Integrable g := ((partialIntegral_defined_iff volume _).mp ⟨_,obs⟩).2
  have eq := Option.some.inj ((partialIntegral_valid volume _ (fun y => ⟨g y,rfl⟩) hi).symm.trans obs)
  exact ⟨(integrable_indicator_iff measurableSet_Ioo).mp hi,
    by simpa [g, integral_indicator measurableSet_Ioo] using eq⟩

private theorem increasing {a b l x : ℝ} (sl : Bool) (ha : 0 < a)
    (h : if sl then 0 ≤ a*l+b else 0 < a*l+b) (hx : if sl then l < x else l ≤ x) : 0 < a*x+b := by
  cases sl
  · exact lt_of_lt_of_le h (add_le_add_right (mul_le_mul_of_nonneg_left hx ha.le) _)
  · exact lt_of_le_of_lt h (add_lt_add_right (mul_lt_mul_of_pos_left hx ha) _)

private theorem decreasing {a b u x : ℝ} (su : Bool) (ha : a < 0)
    (h : if su then 0 ≤ a*u+b else 0 < a*u+b) (hx : if su then x < u else x ≤ u) : 0 < a*x+b := by
  cases su
  · exact lt_of_lt_of_le h (add_le_add_right (mul_le_mul_of_nonpos_left hx ha.le) _)
  · exact lt_of_le_of_lt h (add_lt_add_right (mul_lt_mul_of_neg_left hx ha) _)

private theorem weak {z : ℝ} (s : Bool) (h : if s then 0 ≤ z else 0 < z) : 0 ≤ z := by
  cases s
  · exact le_of_lt h
  · exact h

/-- A mask may include a regular endpoint. A singular endpoint must be
excluded before the reciprocal is evaluated. -/
theorem mass {w a b k} (term : Term w a b k) (l u p q m : ℚ) (swap sl su : Bool)
    (ha : a ≠ 0) (hlu : l ≤ u) (hp : a*l+b = p) (hq : a*u+b = q) (hm : 2*k/a = m)
    (hs : if sl then 0 ≤ p else 0 < p) (ht : if su then 0 ≤ q else 0 < q)
    {lo hi low high gain : Option ℝ} (hl : lo = some (l:ℝ)) (hu : hi = some (u:ℝ))
    (hlo : low = some (p:ℝ)) (hhi : high = some (q:ℝ)) (hg : gain = some (m:ℝ)) :
    massValue (weightValue (some fun x => Value.mask (StepSource.intervalGuard swap sl su lo hi x) (w x))
      lebesgueValue) = Value.mul gain (Value.add (Functions.sqrtR.apply high)
        (Value.mul (some ((-1:ℤ):ℝ)) (Functions.sqrtR.apply low))) := by
  subst lo; subst hi; subst low; subst high; subst gain
  have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  have hlt : (l:ℝ) ≤ u := by exact_mod_cast hlu
  have h₁ : (a:ℝ)*l+b = p := by exact_mod_cast hp
  have h₂ : (a:ℝ)*u+b = q := by exact_mod_cast hq
  have h₃ : 2*(k:ℝ)/a = m := by exact_mod_cast hm
  have ep : if sl then 0 ≤ (p:ℝ) else 0 < (p:ℝ) := by cases sl <;> exact_mod_cast hs
  have eq : if su then 0 ≤ (q:ℝ) else 0 < (q:ℝ) := by cases su <;> exact_mod_cast ht
  have hp' := weak sl ep
  have hq' := weak su eq
  have result := ordinary a b l u k hn hlt (h₁ ▸ hp') (h₂ ▸ hq')
  rw [weighted_lebesgue_mass_bridge, Model.densityMassValue_eq]
  have rule := StepSource.interval_observation_value swap sl su (l:ℝ) (u:ℝ)
    (f := fun x => Value.mask (StepSource.intervalGuard swap sl su (some l) (some u) x) (w x))
    (v := w) ⟨fun _ => rfl⟩ (g := fun y => (k:ℝ)/√((a:ℝ)*y+b)) (fun x hx => term.regular x (by
      rcases lt_or_gt_of_ne hn with neg | pos
      · exact decreasing su neg (h₂ ▸ eq) hx.2
      · exact increasing sl pos (h₁ ▸ ep) hx.1))
  change partialIntegral volume _ = _
  rw [rule.1 result.1, result.2, h₁, h₂, h₃]
  simp [Functions.sqrtR, Function1.apply, hq', hp', Value.mul, Value.add, sub_eq_add_neg]

/-- Missing values remain observable at a single included point of the mask. -/
theorem mass_missing {w a b k} (term : Term w a b k) (l u v : ℚ) (swap sl su : Bool)
    (h₁ : if sl then l < v else l ≤ v) (h₂ : if su then v < u else v ≤ u)
    (hz : a*v+b ≤ 0) {lo hi : Option ℝ} (hl : lo = some (l:ℝ)) (hu : hi = some (u:ℝ)) :
    massValue (weightValue (some fun x => Value.mask (StepSource.intervalGuard swap sl su lo hi x) (w x))
      lebesgueValue) = none := by
  subst lo; subst hi
  rw [weighted_lebesgue_mass_bridge, Model.densityMassValue_eq]
  apply StepSource.interval_observation_missing swap sl su (l:ℝ) (u:ℝ) (x := (v:ℝ))
    (v := w) ⟨fun _ => rfl⟩
  · constructor
    · cases sl <;> exact_mod_cast h₁
    · cases su <;> exact_mod_cast h₂
  · exact term.missing _ (by exact_mod_cast hz)

end QSym.Distribution.RootInterval
