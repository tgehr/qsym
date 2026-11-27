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

theorem fibre_sample (c a b q z : ℚ) (ha : a ≠ 0) (hz : a*q+b = z)
    {h t u y : Option ℝ} (hc : h = some (c:ℝ)) (ht : t = some (a:ℝ))
    (hu : u = some (b:ℝ)) (hy : y = some (q:ℝ)) {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) u)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0)
    (kind : FibreQuery) : kind.apply f y = atomFibre c a z kind.predicate := by
  subst h; subst t; subst u; subst y; subst z
  have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  let F (x : ℝ) := ((x-c)^2-(b:ℝ))/(a:ℝ)
  have hm : Measurable F := by dsimp [F]; fun_prop
  have roots := sourceRoots_cover (c:ℝ) a b q hn
  have masked (p : Option (ℝ → Option Bool)) :
      (maskedKernel p (some fun x => some (F x))).bind (fun k => k (q:ℝ)) = atomFibre c a ((a:ℝ)*q+b) p := by
    cases p with
    | none => rfl
    | some pred =>
      rw [maskedKernel_total pred F hm]
      change (maskedAtoms pred F (q:ℝ)).map presentation = _
      exact congrArg (Option.map presentation) (roots.masked pred _ (fun x _ _ => derivative c a b x))
  rw [funext (equation c a b hn equal), Rat.cast_add, Rat.cast_mul]
  cases kind with
  | full => exact (roots.true_kernel hm _ (fun x _ => derivative c a b x)).trans (masked _)
  | masked p => exact masked p

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
    have left : -(r:ℝ)+c = (c:ℝ)-r := by ring
    have right : (r:ℝ)+c = (c:ℝ)+r := add_comm _ _
    have d₁ : (c:ℝ)-r-c = -(r:ℝ) := by ring
    have d₂ : (c:ℝ)+r-c = (r:ℝ) := by ring
    simp only [atomFibre, sourceRoots, Option.some_bind, Rat.cast_mul, if_neg hs.not_lt, if_neg hs.ne',
      Real.sqrt_mul_self hp.le, left, right, d₁, d₂, inverse_slope (a:ℝ) r _ hn hp (abs_neg _ |>.trans (abs_of_pos hp)),
      inverse_slope (a:ℝ) r _ hn hp (abs_of_pos hp), Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_abs, Rat.cast_ofNat,
      List.mapM_cons, List.mapM_nil]
    cases Value.mask (pred ((c:ℝ)-r)) (some (|(a:ℝ)|/(2*r))) <;>
      cases Value.mask (pred ((c:ℝ)+r)) (some (|(a:ℝ)|/(2*r))) <;> rfl

end Coordinates.Quadratic
end QSym.Distribution.GraphFibre
