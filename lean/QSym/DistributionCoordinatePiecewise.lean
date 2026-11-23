import QSym.DistributionInverseCover

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates
open Set Filter Topology

open Classical in
/-- Integrate over disjoint source pieces of a displayed coordinate. Their
images may overlap and their one-sided limits may differ. Each piece pays
for its own image and checks definedness of its own partial test. -/
theorem branch_pair_image {s t : Set ℝ} {l r dl dr : ℝ → ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (dis : Disjoint s t)
    (il : InjOn l s) (ir : InjOn r t)
    (hl : ∀ x ∈ s, HasDerivWithinAt l (dl x) s x)
    (hr : ∀ x ∈ t, HasDerivWithinAt r (dr x) t x) (u v : ℝ → Option ℝ) :
    branchIntegral (s ∪ t) (fun x => if x ∈ s then (u (l x)).map (|dl x| • ·)
      else (v (r x)).map (|dr x| • ·)) =
      Value.add (branchIntegral (l '' s) u) (branchIntegral (r '' t) v) := by
  rw [branchIntegral_union dis.aedisjoint ht.nullMeasurableSet,
    branchIntegral_image hs il hl, branchIntegral_image ht ir hr]
  apply congrArg₂ Value.add
  · exact branchIntegral_congr hs fun _ hx => if_pos hx
  · exact branchIntegral_congr ht fun _ hx => if_neg (fun h => Set.disjoint_left.mp dis h hx)

/-- Paste two differentiable pieces at a point where both their values
and their first derivatives agree. -/
theorem hasDerivAt_join {l r dl dr : ℝ → ℝ} {a : ℝ}
    (hl : ∀ x, HasDerivAt l (dl x) x) (hr : ∀ x, HasDerivAt r (dr x) x)
    (hv : l a = r a) (hd : dl a = dr a) (x : ℝ) :
    HasDerivAt (fun y => if y < a then l y else r y) (if x < a then dl x else dr x) x := by
  rcases lt_trichotomy x a with hx | rfl | hx
  · rw [if_pos hx]
    exact (hl x).congr_of_eventuallyEq ((gt_mem_nhds hx).mono fun y hy => if_pos hy)
  · rw [if_neg (lt_irrefl _), ← hd]
    have left : HasDerivWithinAt (fun y => if y < x then l y else r y) (dl x) (Iic x) x := by
      apply (hl x).hasDerivWithinAt.congr_of_mem _ right_mem_Iic
      intro y hy
      rcases lt_or_eq_of_le (show y ≤ x from hy) with h | rfl
      · exact if_pos h
      · simp [hv]
    have right : HasDerivWithinAt (fun y => if y < x then l y else r y) (dl x) (Ici x) x := by
      rw [hd]
      apply (hr x).hasDerivWithinAt.congr_of_mem _ left_mem_Ici
      exact fun y hy => if_neg (not_lt_of_ge (show x ≤ y from hy))
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using left.union right
  · rw [if_neg hx.not_lt]
    exact (hr x).congr_of_eventuallyEq ((lt_mem_nhds hx).mono fun y hy => if_neg hy.not_lt)

theorem contDiff_join {l r : ℝ → ℝ} {a : ℝ} (hl : ContDiff ℝ 1 l) (hr : ContDiff ℝ 1 r)
    (hv : l a = r a) (hd : deriv l a = deriv r a) :
    ContDiff ℝ 1 (fun x => if x < a then l x else r x) := by
  have d := hasDerivAt_join (fun x => (hl.differentiable le_rfl x).hasDerivAt)
    (fun x => (hr.differentiable le_rfl x).hasDerivAt) hv hd
  refine contDiff_one_iff_deriv.mpr ⟨fun x => (d x).differentiableAt, ?_⟩
  rw [funext fun x => (d x).deriv]
  have c := Continuous.if_le (contDiff_one_iff_deriv.mp hr).2 (contDiff_one_iff_deriv.mp hl).2
    (f := fun _ : ℝ => a) (g := id) continuous_const continuous_id (fun x hx => by
      change a = x at hx; simpa [← hx] using hd.symm)
  convert c using 1
  funext x
  by_cases hx : x < a
  · simp [hx, not_le_of_gt hx]
  · simp [hx, le_of_not_gt hx]

/-- The length density of two C¹ formulas pasted at a cut with matching
heights and signed slopes. The equality also covers the cut itself. -/
theorem singleton_join {l r : ℝ → ℝ} {a : ℝ} (hl : ContDiff ℝ 1 l) (hr : ContDiff ℝ 1 r)
    (hv : l a = r a) (hd : deriv l a = deriv r a) :
    value (Tensor.consValue (some fun x => some (if x < a then l x else r x)) Tensor.nilValue) =
      weightValue (some fun x => some |if x < a then deriv l x else deriv r x|) lebesgueValue := by
  apply singleton_length (contDiff_join hl hr hv hd) (fun _ => rfl)
  intro x
  rw [(hasDerivAt_join (fun x => (hl.differentiable le_rfl x).hasDerivAt)
    (fun x => (hr.differentiable le_rfl x).hasDerivAt) hv hd x).deriv]

/-- The two source spellings of a ray may include or exclude the origin. -/
def rayGuard (left closed : Bool) (x : ℝ) :=
  let z := some ((0 : ℤ) : ℝ)
  let a := if left then some x else z
  let b := if left then z else some x
  if closed then Value.le a b else Value.lt a b

private def ray (left : Bool) (f : ℝ → ℝ) (x : ℝ) :=
  if x < 0 then (if left then f x else 0) else (if left then 0 else f x)

private theorem mask_ray (left closed : Bool) {f : ℝ → ℝ} (h0 : f 0 = 0) (x : ℝ) :
    Value.mask (rayGuard left closed x) (some (f x)) = some (ray left f x) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · cases left <;> cases closed <;> simp [rayGuard, ray, Value.lt, Value.le, Value.mask, hx, hx.le, not_lt_of_gt hx, not_le_of_gt hx]
  · cases left <;> cases closed <;> simp [rayGuard, ray, Value.lt, Value.le, Value.mask, h0]
  · cases left <;> cases closed <;> simp [rayGuard, ray, Value.lt, Value.le, Value.mask, hx, hx.le, not_lt_of_gt hx, not_le_of_gt hx]

private theorem ray_deriv (left : Bool) {f d : ℝ → ℝ} (h : ∀ x, HasDerivAt f (d x) x)
    (hf : f 0 = 0) (hd : d 0 = 0) (x : ℝ) : HasDerivAt (ray left f) (ray left d x) x := by
  cases left
  · exact hasDerivAt_join (fun x => hasDerivAt_const x 0) h hf.symm hd.symm x
  · exact hasDerivAt_join h (fun x => hasDerivAt_const x 0) hf hd x

private theorem ray_smooth (left : Bool) {f : ℝ → ℝ} (h : ContDiff ℝ 1 f)
    (hf : f 0 = 0) (hd : deriv f 0 = 0) : ContDiff ℝ 1 (ray left f) := by
  cases left
  · apply contDiff_join contDiff_const h hf.symm
    simpa using hd.symm
  · apply contDiff_join h contDiff_const hf
    simpa using hd

/-- Masking a monomial of degree at least two on either side of zero
preserves C¹ regularity, since both the value and the slope vanish there. -/
theorem rayPower (left closed : Bool) (n : ℕ) (hn : 2 ≤ n) :
    value (Tensor.consValue (some fun x => Value.mask (rayGuard left closed x)
      ((some x).map (· ^ n))) Tensor.nilValue) =
    weightValue (some fun x => Value.mask (rayGuard left closed x)
      (Value.mul (some ((n : ℤ) : ℝ)) ((Value.abs (some x)).map (· ^ (n-1))))) lebesgueValue := by
  let f := fun x : ℝ => x ^ n
  let d := fun x : ℝ => (n : ℝ) * x ^ (n-1)
  have hn0 : n ≠ 0 := by omega
  have hn1 : n-1 ≠ 0 := by omega
  have hf : f 0 = 0 := zero_pow hn0
  have hd : d 0 = 0 := by simp [d, zero_pow hn1]
  have deriv (x : ℝ) : HasDerivAt f (d x) x := hasDerivAt_pow n x
  apply singleton_length (g := ray left f) (ray_smooth left (by fun_prop [f]) hf ((deriv 0).deriv.trans hd))
  · exact mask_ray left closed hf
  · intro x
    have h (x : ℝ) : |d x| = n * |x| ^ (n-1) := by simp [d, abs_mul, abs_pow]
    rw [(ray_deriv left deriv hf hd x).deriv]
    change Value.mask _ (some _) = _
    simp only [Int.cast_natCast, ← h]
    rw [mask_ray (f := fun x => |d x|) left closed (by simp [hd])]
    cases left <;> by_cases hx : x < 0 <;> simp [ray, hx]

end QSym.Distribution.GraphFibre.Coordinates
