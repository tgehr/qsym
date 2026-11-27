import QSym.DistributionQuadraticFibre

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Quadratic

private def rootObservation (c a z : ℝ) (p : Option (ℝ → Option Bool)) : Option ℝ :=
  p.bind fun pred => (sourceRoots c z).foldr (fun x acc =>
    Value.add (Value.mask (pred x) (Value.inv (some |2*(x-c)/a|))) acc) (some 0)

/-- Transfer the source identity and the exact target coordinate to the complete
fibre. The predicate can be partial at a root or can itself be missing. -/
theorem guarded_observation (c a b q z : ℚ) (ha : a ≠ 0) (hz : a*q+b = z)
    {h t u y : Option ℝ} (hc : h = some (c:ℝ)) (ht : t = some (a:ℝ))
    (hu : u = some (b:ℝ)) (hy : y = some (q:ℝ)) {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) u)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0)
    (p : Option (ℝ → Option Bool)) :
    densityAtValue (realPushforwardOnValue p (some f)) y = rootObservation c a z p := by
  subst h; subst t; subst u; subst y; subst z
  have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  rw [funext (equation c a b hn equal)]
  cases p with
  | none => rfl
  | some pred => simpa only [Rat.cast_add, Rat.cast_mul] using restricted_roots c a b q hn pred

theorem guarded_outside (c a z : ℚ) (hz : z < 0) (p : Option (ℝ → Option Bool))
    {out : Option ℝ} (h : out = some 0) : rootObservation c a z p = p.bind (fun _ => out) := by
  have hn : (z:ℝ) < 0 := by exact_mod_cast hz
  subst out; cases p <;> simp [rootObservation, sourceRoots, hn]

theorem guarded_vertex (c a : ℚ) (p : Option (ℝ → Option Bool)) {h : Option ℝ}
    (hc : h = some (c:ℝ)) : rootObservation c a ((0:ℚ):ℝ) p =
    Value.mask (p.bind fun pred => h.bind pred) (none : Option ℝ) := by
  subst h
  cases p <;> simp [rootObservation, sourceRoots, Value.inv, Value.add_zero_right, Value.mask]

private theorem inverse_slope (a r d : ℝ) (ha : a ≠ 0) (hr : 0 < r) (hd : |d| = r) :
    Value.inv (some |2*d/a|) = some (|a|/(2*r)) := by
  have hv : 2*|d|/|a| ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) (hd ▸ hr.ne')) (abs_ne_zero.mpr ha)
  simp [abs_div, abs_mul, abs_of_pos (show (0:ℝ) < 2 by norm_num), Value.inv, hv, hd, hr.ne', ha,
    div_eq_mul_inv, abs_inv, mul_comm, mul_left_comm, mul_assoc]

theorem guarded_regular (c a z r lo hi w : ℚ) (ha : a ≠ 0) (hr : 0 < r)
    (hz : r*r = z) (hl : c-r = lo) (hh : c+r = hi) (hw : w = |a|/(2*r))
    (p : Option (ℝ → Option Bool)) {l u v : Option ℝ}
    (h₁ : l = some (lo:ℝ)) (h₂ : u = some (hi:ℝ)) (hv : v = some (w:ℝ)) :
    rootObservation c a z p = Value.add (Value.mask (p.bind fun pred => l.bind pred) v)
      (Value.mask (p.bind fun pred => u.bind pred) v) := by
  subst l; subst u; subst v; subst z; subst lo; subst hi; subst w
  cases p with
  | none => rfl
  | some pred =>
    have hp : 0 < (r:ℝ) := by exact_mod_cast hr
    have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
    have hs : 0 < (r:ℝ)*r := mul_pos hp hp
    have left : -(r:ℝ)+c = (c:ℝ)-r := by ring
    have offset : (c:ℝ)-r-c = -(r:ℝ) := by ring
    simp only [rootObservation, Option.some_bind, Rat.cast_mul, sourceRoots, if_neg hs.not_lt, if_neg hs.ne',
      Real.sqrt_mul_self hp.le, List.foldr_cons, List.foldr_nil, add_sub_cancel_right, left, offset,
      inverse_slope (a:ℝ) r _ hn hp (abs_neg (r:ℝ) |>.trans (abs_of_pos hp)), inverse_slope (a:ℝ) r _ hn hp (abs_of_pos hp),
      Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_abs, Value.add_zero_right]
    rw [add_comm (r:ℝ) c]

/-- Both inverse branches are masked before their Jacobian is observed. At
the vertex the two branch contributions are either both zero or both missing. -/
def guardedBranches (p : Option (ℝ → Option Bool)) (h gain t : Option ℝ) : Option ℝ :=
  let r := Functions.sqrtR.apply t
  let lo := Value.add h (Value.mul (some ((-1:ℤ):ℝ)) r)
  let hi := Value.add h r
  let w := Value.mul (Value.inv (Value.mul (some ((2:ℤ):ℝ)) r)) gain
  p.bind fun _ => Value.mask (Value.le (some ((0:ℤ):ℝ)) t)
    (Value.add (Value.mask (p.bind fun pred => lo.bind pred) w) (Value.mask (p.bind fun pred => hi.bind pred) w))

private theorem branches_eq (c a t : ℝ) (ha : a ≠ 0) (p : ℝ → Option Bool) :
    rootObservation c a t (some p) = guardedBranches (some p) (some c) (some |a|) (some t) := by
  rcases lt_trichotomy t 0 with hn | hz | hp
  · simp [rootObservation, sourceRoots, guardedBranches, hn, not_le.mpr hn, Value.le, Value.mask]
  · subst t
    cases h : p c with
    | none => simp [rootObservation, sourceRoots, guardedBranches, Functions.sqrtR, Function1.apply, Value.mask,
        Value.le, Value.add, Value.mul, Value.inv, h]
    | some b =>
      cases b <;> simp [rootObservation, sourceRoots, guardedBranches, Functions.sqrtR, Function1.apply, Value.mask,
        Value.le, Value.add, Value.mul, Value.inv, h]
  · have hs := Real.sqrt_pos.mpr hp
    have sr : Functions.sqrtR.apply (some t) = some (√t) := by simp [Functions.sqrtR, Function1.apply, hp.le]
    have test : Value.le (some ((0:ℤ):ℝ)) (some t) = some true := by simp [Value.le, hp.le]
    have w : Value.mul (Value.inv (Value.mul (some ((2:ℤ):ℝ)) (some (√t)))) (some |a|) = some (|a|/(2*√t)) := by
      simp [Value.mul, Value.inv, hs.ne', div_eq_mul_inv, mul_comm]
    have lo : Value.add (some c) (Value.mul (some ((-1:ℤ):ℝ)) (some (√t))) = some (-√t+c) := by
      simp [Value.add, Value.mul, add_comm]
    have hi : Value.add (some c) (some (√t)) = some (√t+c) := by simp [Value.add, add_comm]
    have left := inverse_slope a (√t) (-√t) ha hs (by simp [abs_of_pos hs])
    have right := inverse_slope a (√t) (√t) ha hs (abs_of_pos hs)
    simp only [rootObservation, guardedBranches, sourceRoots, if_neg hp.not_lt, if_neg hp.ne', Option.some_bind,
      List.foldr_cons, List.foldr_nil, add_sub_cancel_right, left, right, sr, w, test, lo, hi, Value.mask_true, Value.add_zero_right]

theorem guarded_symbolic (c a b j : ℚ) (ha : a ≠ 0) (hj : j = |a|) {h t u gain : Option ℝ}
    (hc : h = some (c:ℝ)) (ht : t = some (a:ℝ)) (hu : u = some (b:ℝ)) (hg : gain = some (j:ℝ))
    {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) u)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0)
    (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    densityAtValue (realPushforwardOnValue p (some f)) y = guardedBranches p h gain (Value.add (Value.mul t y) u) := by
  subst h; subst t; subst u; subst gain; subst j
  have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  rw [funext (equation c a b hn equal), Rat.cast_abs]
  cases p with
  | none => rfl
  | some pred =>
    cases y with
    | none => rfl
    | some y => exact (restricted_roots _ _ _ _ hn pred).trans (branches_eq _ _ _ hn pred)

end QSym.Distribution.GraphFibre.Coordinates.Quadratic
