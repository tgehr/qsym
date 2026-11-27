import QSym.DistributionMaskedRootCover
import QSym.DistributionQuadraticRestriction

noncomputable section
namespace QSym.Distribution.GraphFibre
open Set MeasureTheory

/-- A complete finite fibre makes the unrestricted disintegration agree with
the masked kernel for the everywhere-true source predicate. -/
theorem RootCover.true_kernel {f : ℝ → ℝ} {y : ℝ} {xs : List ℝ} (cover : RootCover univ f y xs)
    (hm : Measurable f) (slope : ℝ → ℝ) (hd : ∀ x ∈ xs, HasStrictDerivAt f (slope x) x) :
    value (some fun x => some (f x)) (some y) =
      (maskedKernel (some fun _ => some true) (some fun x => some (f x))).bind (fun k => k y) := by
  rw [value_total f hm, maskedKernel_total _ f hm]
  change (fibre f y).map presentation = (maskedAtoms (fun _ => some true) f y).map presentation
  rw [cover.atoms slope hd, cover.masked _ slope (fun x hx _ => hd x hx)]
  rfl

namespace Coordinates.Quadratic
inductive FibreQuery where
  | full
  | masked (p : Option (ℝ → Option Bool))

def FibreQuery.predicate : FibreQuery → Option (ℝ → Option Bool)
  | .full => some fun _ => some true
  | .masked p => p

def FibreQuery.apply (kind : FibreQuery) (f : ℝ → Option ℝ) (y : Option ℝ) : Option (D ℝ) :=
  match kind with
  | .full => GraphFibre.value (some f) y
  | .masked p => (maskedKernel p (some f)).bind (fun k => y.bind k)

private def atomFibre (c a z : ℝ) (p : Option (ℝ → Option Bool)) : Option (D ℝ) :=
  p.bind fun pred => ((sourceRoots c z).mapM (fun x =>
    (Value.mask (pred x) (Value.inv (some |2*(x-c)/a|))).map (x, ·))).map presentation

private theorem canonical_fibre (c a b y : ℝ) (ha : a ≠ 0) (kind : FibreQuery) :
    kind.apply (fun x => some (((x-c)^2-b)/a)) (some y) = atomFibre c a (a*y+b) kind.predicate := by
  let F (x : ℝ) := ((x-c)^2-b)/a
  have hm : Measurable F := by dsimp [F]; fun_prop
  have roots := sourceRoots_cover c a b y ha
  have masked (p : Option (ℝ → Option Bool)) :
      (maskedKernel p (some fun x => some (F x))).bind (fun k => k y) = atomFibre c a (a*y+b) p := by
    cases p with
    | none => rfl
    | some pred =>
      rw [maskedKernel_total pred F hm]
      change (maskedAtoms pred F y).map presentation = _
      exact congrArg (Option.map presentation) (roots.masked pred _ (fun x _ _ => derivative c a b x))
  cases kind with
  | full => exact (roots.true_kernel hm _ (fun x _ => derivative c a b x)).trans (masked _)
  | masked p => exact masked p

theorem fibre_sample (c a b q z : ℚ) (ha : a ≠ 0) (hz : a*q+b = z)
    {h t u y : Option ℝ} (hc : h = some (c:ℝ)) (ht : t = some (a:ℝ))
    (hu : u = some (b:ℝ)) (hy : y = some (q:ℝ)) {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) u)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0)
    (kind : FibreQuery) : kind.apply f y = atomFibre c a z kind.predicate := by
  subst h; subst t; subst u; subst y; subst z
  have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  rw [funext (equation c a b hn equal), Rat.cast_add, Rat.cast_mul]
  exact canonical_fibre _ _ _ _ hn kind

theorem fibre_outside (c a z : ℚ) (hz : z < 0) (p : Option (ℝ → Option Bool)) :
    atomFibre c a z p = p.bind (fun _ => zeroValue) := by
  have hn : (z:ℝ) < 0 := by exact_mod_cast hz
  cases p <;> simp [atomFibre, sourceRoots, hn, presentation, zeroValue]

theorem fibre_vertex (c a : ℚ) (p : Option (ℝ → Option Bool)) {h zero : Option ℝ}
    (hc : h = some (c:ℝ)) (hz : zero = some 0) :
    atomFibre c a ((0:ℚ):ℝ) p = Binding.guardValue (Value.not (p.bind fun pred => h.bind pred))
      (scaleValue zero (diracValue h)) := by
  subst h; subst zero
  cases p with
  | none => rfl
  | some pred =>
    cases h : pred c with
    | none => simp [atomFibre, sourceRoots, h, Value.mask, Value.inv, Value.not, Binding.guardValue, List.mapM_cons]
    | some t =>
      cases t <;> simp [atomFibre, sourceRoots, h, Value.mask, Value.inv, Value.not,
        Binding.guardValue, List.mapM_cons, presentation, scaleValue, diracValue]

private theorem positive_atoms (c a t : ℝ) (ha : a ≠ 0) (ht : 0 < t) (pred : ℝ → Option Bool) :
    atomFibre c a t (some pred) =
      addValue (scaleValue (Value.mask (pred (-√t+c)) (some (|a|/(2*√t)))) (diracValue (some (-√t+c))))
        (scaleValue (Value.mask (pred (√t+c)) (some (|a|/(2*√t)))) (diracValue (some (√t+c)))) := by
  have hr := Real.sqrt_pos.mpr ht
  simp only [atomFibre, sourceRoots, if_neg ht.not_lt, if_neg ht.ne', Option.some_bind, add_sub_cancel_right,
    inverse_slope a _ _ ha hr ((abs_neg _).trans (abs_of_pos hr)), inverse_slope a _ _ ha hr (abs_of_pos hr),
    List.mapM_cons, List.mapM_nil]
  cases Value.mask (pred (-√t+c)) (some (|a|/(2*√t))) <;>
    cases Value.mask (pred (√t+c)) (some (|a|/(2*√t))) <;> rfl

theorem fibre_regular (c a z r lo hi w : ℚ) (ha : a ≠ 0) (hr : 0 < r)
    (hz : r*r = z) (hl : c-r = lo) (hh : c+r = hi) (hw : w = |a|/(2*r))
    (p : Option (ℝ → Option Bool)) {l u v : Option ℝ}
    (h₁ : l = some (lo:ℝ)) (h₂ : u = some (hi:ℝ)) (hv : v = some (w:ℝ)) :
    atomFibre c a z p =
      addValue (scaleValue (Value.mask (p.bind fun pred => l.bind pred) v) (diracValue l))
        (scaleValue (Value.mask (p.bind fun pred => u.bind pred) v) (diracValue u)) := by
  subst l; subst u; subst v; subst z; subst lo; subst hi; subst w
  cases p with
  | none => rfl
  | some pred =>
    have hp : 0 < (r:ℝ) := by exact_mod_cast hr
    have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
    have hs : 0 < (r:ℝ)*r := mul_pos hp hp
    simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_abs, Rat.cast_ofNat,
      Real.sqrt_mul_self hp.le, neg_add_eq_sub, add_comm (r:ℝ) (c:ℝ), Option.some_bind] using
      positive_atoms c a ((r:ℝ)*r) hn hs pred

/-- Split a whole fibre by the sign of its squared radius. At the vertex
there is one source point, even if the predicate gives it weight zero. -/
def fibreBranches (kind : FibreQuery) (h gain t : Option ℝ) : Option (D ℝ) :=
  let r := Functions.sqrtR.apply t
  let lo := Value.add h (Value.mul (some ((-1:ℤ):ℝ)) r)
  let hi := Value.add h r
  let w := Value.mul (Value.inv (Value.mul (some ((2:ℤ):ℝ)) r)) gain
  let atom := fun pt =>
    let coefficient := match kind with
      | .full => w
      | .masked p => Value.mask (p.bind fun pred => pt.bind pred) w
    scaleValue coefficient (diracValue pt)
  let critical := match kind with
    | .full => none
    | .masked p => Binding.guardValue (Value.not (p.bind fun pred => h.bind pred))
        (scaleValue (some ((0:ℤ):ℝ)) (diracValue h))
  kind.predicate.bind fun _ => squareCases t (addValue (atom lo) (atom hi)) zeroValue critical

private theorem true_branches (h gain t : Option ℝ) :
    fibreBranches (.masked (some fun _ => some true)) h gain t = fibreBranches .full h gain t := by
  have atom (point w : Option ℝ) :
      scaleValue (Value.mask (point.bind fun _ => some true) w) (diracValue point) = scaleValue w (diracValue point) := by
    cases point <;> cases w <;> rfl
  have vertex : Binding.guardValue (Value.not (h.bind fun _ => some true))
      (scaleValue (some ((0:ℤ):ℝ)) (diracValue h)) = none := by cases h <;> rfl
  simp only [fibreBranches, FibreQuery.predicate, Option.some_bind, atom, vertex]

private theorem fibre_branches_eq (c a : ℚ) (t : ℝ) (ha : (a:ℝ) ≠ 0) (p : Option (ℝ → Option Bool)) :
    atomFibre c a t p = fibreBranches (.masked p) (some c) (some |(a:ℝ)|) (some t) := by
  cases p with
  | none => rfl
  | some pred =>
    rcases lt_trichotomy t 0 with hn | rfl | hp
    · simp [atomFibre, sourceRoots, fibreBranches, FibreQuery.predicate, squareCases, Binding.conditionalValue, Value.lt,
        hn, not_lt_of_ge hn.le, presentation, zeroValue]
    · simpa [fibreBranches, FibreQuery.predicate, squareCases, Binding.conditionalValue, Value.lt] using
        (fibre_vertex c a (some pred) (h := some (c:ℝ)) rfl (zero := some (0:ℝ)) rfl)
    · have hr := Real.sqrt_pos.mpr hp
      have sr : Functions.sqrtR.apply (some t) = some (√t) := by simp [Functions.sqrtR, Function1.apply, hp.le]
      have w : Value.mul (Value.inv (Value.mul (some ((2:ℤ):ℝ)) (some (√t)))) (some |(a:ℝ)|) =
          some (|(a:ℝ)|/(2*√t)) := by simp [Value.mul, Value.inv, hr.ne', div_eq_mul_inv, mul_comm]
      rw [positive_atoms _ _ _ ha hp]
      have lo : Value.add (some (c:ℝ)) (Value.mul (some ((-1:ℤ):ℝ)) (some (√t))) = some (-√t+c) := by
        simp [Value.add, Value.mul, add_comm]
      have hi : Value.add (some (c:ℝ)) (some (√t)) = some (√t+c) := by simp [Value.add, add_comm]
      simp only [fibreBranches, FibreQuery.predicate, sr, w, lo, hi, Option.some_bind, squareCases]
      simp [Binding.conditionalValue, Value.lt, hp]

theorem fibre_symbolic (c a b j : ℚ) (ha : a ≠ 0) (hj : j = |a|) {h t u gain : Option ℝ}
    (hc : h = some (c:ℝ)) (ht : t = some (a:ℝ)) (hu : u = some (b:ℝ)) (hg : gain = some (j:ℝ))
    {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) u)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0)
    (kind : FibreQuery) (y : Option ℝ) :
    kind.apply f y = fibreBranches kind h gain (Value.add (Value.mul t y) u) := by
  subst h; subst t; subst u; subst gain; subst j
  have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  rw [funext (equation c a b hn equal), Rat.cast_abs]
  cases y with
  | none =>
    cases kind with
    | full => rfl
    | masked p =>
      cases p with
      | none => rfl
      | some pred =>
        simp [FibreQuery.apply, FibreQuery.predicate, fibreBranches, squareCases, Binding.conditionalValue,
          Value.add, Value.mul, Value.lt, maskedKernel_total pred (fun x : ℝ => ((x-c)^2-b)/a) (by fun_prop)]
  | some y =>
    apply (canonical_fibre _ _ _ _ hn kind).trans
    apply (fibre_branches_eq c a _ hn _).trans
    cases kind with
    | full => exact true_branches _ _ _
    | masked p => rfl

end Coordinates.Quadratic
end QSym.Distribution.GraphFibre
