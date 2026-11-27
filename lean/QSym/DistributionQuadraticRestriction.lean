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
    have weight (d : ℝ) (hd : |d| = (r:ℝ)) :
        Value.inv (some |2*d/(a:ℝ)|) = some (|(a:ℝ)|/(2*r)) := by
      have hv : 2*|d|/|(a:ℝ)| ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) (hd ▸ hp.ne')) (abs_ne_zero.mpr hn)
      simp [abs_div, abs_mul, abs_of_pos (show (0:ℝ) < 2 by norm_num), Value.inv, hv, hd, hp.ne', hn,
        div_eq_mul_inv, abs_inv, mul_comm, mul_left_comm, mul_assoc]
    have left : -(r:ℝ)+c = (c:ℝ)-r := by ring
    have offset : (c:ℝ)-r-c = -(r:ℝ) := by ring
    simp only [rootObservation, Option.some_bind, Rat.cast_mul, sourceRoots, if_neg hs.not_lt, if_neg hs.ne',
      Real.sqrt_mul_self hp.le, List.foldr_cons, List.foldr_nil, add_sub_cancel_right, left, offset,
      weight _ (abs_neg (r:ℝ) |>.trans (abs_of_pos hp)), weight _ (abs_of_pos hp),
      Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_abs, Value.add_zero_right]
    rw [add_comm (r:ℝ) c]

end QSym.Distribution.GraphFibre.Coordinates.Quadratic
