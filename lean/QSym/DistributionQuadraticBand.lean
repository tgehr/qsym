import QSym.DistributionQuadraticWindow

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Quadratic

private def edge (closed : Bool) (x y : Option ℝ) : Option Bool :=
  if closed then Value.le x y else Value.lt x y

private def sourceBand (right closed : Bool) (lo hi : Option ℝ) (x : ℝ) : Option Bool :=
  if right then Value.and (Value.lt lo (some x)) (edge closed (some x) hi)
  else Value.and (edge closed lo (some x)) (Value.lt (some x) hi)

private def bandDensity (closed : Bool) (cap gain z : Option ℝ) : Option ℝ :=
  Value.mask (Value.and (Value.lt (some ((0:ℤ):ℝ)) z) (edge closed z cap))
    (Value.mul (Value.inv (Value.mul (some ((2:ℤ):ℝ)) (Functions.sqrtR.apply z))) gain)

private theorem band_rows (lo hi a z : ℝ) (h : lo < hi) (right closed : Bool) :
    guardedBranches (some (sourceBand right closed (some lo) (some hi)))
      (some (if right then lo else hi)) (some |a|) (some z) =
      bandDensity closed (some ((hi-lo)^2)) (some |a|) (some z) := by
  rcases lt_trichotomy z 0 with hn | rfl | hp
  · simp [guardedBranches, bandDensity, Value.le, Value.lt, Value.and, Value.mask,
      not_le.mpr hn, not_lt_of_gt hn]
  · cases right <;> cases closed <;> simp [guardedBranches, bandDensity, sourceBand, edge,
      Functions.sqrtR, Function1.apply, Value.le, Value.lt, Value.and, Value.mask, Value.add, Value.mul, h, h.le]
  · have s := Real.sqrt_pos.mpr hp
    have r := sub_pos.mpr h
    have lt : √z < hi-lo ↔ z < (hi-lo)^2 := by
      simpa only [Real.sq_sqrt hp.le] using (sq_lt_sq₀ s.le r.le).symm
    have le : √z ≤ hi-lo ↔ z ≤ (hi-lo)^2 := by
      simpa only [Real.sq_sqrt hp.le] using (sq_le_sq₀ s.le r.le).symm
    have rlt : lo+√z < hi ↔ z < (hi-lo)^2 := by rw [← lt]; constructor <;> intro hx <;> linarith
    have rle : lo+√z ≤ hi ↔ z ≤ (hi-lo)^2 := by rw [← le]; constructor <;> intro hx <;> linarith
    have llt : lo < hi + -√z ↔ z < (hi-lo)^2 := by rw [← lt]; constructor <;> intro hx <;> linarith
    have lle : lo ≤ hi + -√z ↔ z ≤ (hi-lo)^2 := by rw [← le]; constructor <;> intro hx <;> linarith
    have rp : lo < lo+√z := by linarith
    have rn : ¬lo < lo + -√z := by linarith
    have lp : hi + -√z < hi := by linarith
    have ln : ¬hi+√z < hi := by linarith
    have farRight : lo < hi+√z := by linarith
    have farLeft : lo + -√z < hi := by linarith
    cases right <;> cases closed <;> by_cases H : z < (hi-lo)^2 <;> by_cases E : z ≤ (hi-lo)^2 <;>
      simp [guardedBranches, bandDensity, sourceBand, edge, Functions.sqrtR, Function1.apply,
        Value.le, Value.lt, Value.and, Value.mask, Value.add, Value.mul, Value.inv, hp, hp.le,
        s.ne', not_lt_of_gt s, s.not_le, rp, rn, lp, ln, rlt, rle, llt, lle, farRight,
        farRight.le, farLeft, farLeft.le, H, E]

private theorem band_borel (l u : ℝ) (right closed : Bool) :
    BorelPred (sourceBand right closed (some l) (some u)) := by
  cases right <;> cases closed <;> apply BorelPred.and
  all_goals first
    | exact BorelPred.lt (BorelReal.const _) BorelReal.var
    | exact BorelPred.lt BorelReal.var (BorelReal.const _)
    | exact BorelPred.le (BorelReal.const _) BorelReal.var
    | exact BorelPred.le BorelReal.var (BorelReal.const _)

private theorem band_total (l u x : ℝ) (right closed : Bool) :
    Value.Defined (sourceBand right closed (some l) (some u) x) := by
  have both (p q : Bool) : Value.Defined (Value.and (some p) (some q)) := by cases p <;> exact ⟨_,rfl⟩
  cases right <;> cases closed <;> exact both _ _

private theorem band_vertex (l u : ℝ) (h : l < u) (r k : Bool) :
    sourceBand r k (some l) (some u) (if r then l else u) = some false := by
  cases r <;> cases k <;> simp [sourceBand, edge, Value.lt, Value.le, Value.and, h, h.le]

/-- A one-sided interval open at the vertex has one contributing inverse
point. The other end keeps its strict or weak comparison. -/
theorem band_chart (c a b j l u v : ℚ) (right closed : Bool)
    (ha : a ≠ 0) (hj : j = |a|) (hlu : l < u) (hcentre : (if right then l else u) = c)
    (hv : v = (u-l)^2) {h t shift gain lo hi cap : Option ℝ}
    (hc : h = some (c:ℝ)) (ht : t = some (a:ℝ)) (hb : shift = some (b:ℝ)) (hg : gain = some (j:ℝ))
    (hl : lo = some (l:ℝ)) (hu : hi = some (u:ℝ)) (hcap : cap = some (v:ℝ)) {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) shift)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0) :
    realPushforwardOnValue (some (sourceBand right closed lo hi)) (some f) =
      weightValue (some fun y => bandDensity closed cap gain (Value.add (Value.mul t (some y)) shift)) lebesgueValue := by
  subst h; subst t; subst shift; subst gain; subst lo; subst hi; subst cap; subst j; subst v
  have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  have hlt : (l:ℝ) < (u:ℝ) := by exact_mod_cast hlu
  have centre : (if right then (l:ℝ) else (u:ℝ)) = (c:ℝ) := by
    cases right <;> simpa using congrArg (fun x : ℚ => (x:ℝ)) hcentre
  rw [funext (equation c a b hn equal), Rat.cast_abs, Rat.cast_pow, Rat.cast_sub]
  rw [← centre, masked_chart _ a b hn _ (band_borel _ _ _ _) (fun x => band_total _ _ x _ _) (band_vertex _ _ hlt _ _)]
  apply congrArg (fun w => weightValue (some w) lebesgueValue)
  funext y
  exact band_rows _ _ _ _ hlt right closed

end QSym.Distribution.GraphFibre.Coordinates.Quadratic
