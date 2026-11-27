import QSym.DistributionMaskedGraph
import QSym.DistributionRootCover
import QSym.DistributionQuadraticFibre

noncomputable section
namespace QSym.Distribution.GraphFibre
open Set MeasureTheory

private theorem observe_mapM {α : Type} (xs : List α) (atom : α → Option (ℝ × ℝ)) (test : ℝ → Option ℝ) :
    (xs.mapM atom).bind (fun zs => observe zs test) =
      xs.foldr (fun x acc => Value.add ((atom x).bind (fun z => Value.mul (some z.2) (test z.1))) acc) (some 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldr_cons, ← ih, List.mapM_cons]
    cases h : atom x <;> cases t : xs.mapM atom <;> simp [observe, Value.add]

/-- A partial test still visits an excluded root with coefficient zero. Only
a root whose predicate is true needs a derivative certificate. -/
theorem RootCover.masked_pairing {f : ℝ → ℝ} {y : ℝ} {xs : List ℝ} (cover : RootCover univ f y xs)
    (p : ℝ → Option Bool) (hm : Measurable f) (slope : ℝ → ℝ)
    (hd : ∀ x ∈ xs, p x = some true → HasStrictDerivAt f (slope x) x) (test : ℝ → Option ℝ) :
    (((maskedKernel (some p) (some fun x => some (f x))).bind (fun k => k y)).bind (fun d => integrate d test)) =
    xs.foldr (fun x acc => Value.add (Value.mul (Value.mask (p x) (Value.inv (some |slope x|))) (test x)) acc) (some 0) := by
  rw [maskedKernel_total p f hm]
  change ((maskedAtoms p f y).map presentation).bind (fun d => integrate d test) = _
  rw [cover.masked p slope hd]
  have presented (rows : Option (List (ℝ × ℝ))) :
      (rows.map presentation).bind (fun d => integrate d test) = rows.bind (fun zs => observe zs test) := by
    cases rows with
    | none => rfl
    | some zs => exact integrate_presentation zs test
  have atRoot (x : ℝ) (w : Option ℝ) :
      (w.map (x, ·)).bind (fun z => Value.mul (some z.2) (test z.1)) = Value.mul w (test x) := by
    cases w <;> rfl
  rw [presented, observe_mapM]
  simp only [atRoot]

/-- The mass of a masked disintegration equals the pushforward density at this
target whenever its whole fibre is finite and the active derivatives exist. -/
theorem RootCover.masked_mass {f : ℝ → ℝ} {y : ℝ} {xs : List ℝ} (cover : RootCover univ f y xs)
    (p : ℝ → Option Bool) (hm : Measurable f) (slope : ℝ → ℝ)
    (hd : ∀ x ∈ xs, p x ≠ some false → HasStrictDerivAt f (slope x) x) :
    massValue ((maskedKernel (some p) (some fun x => some (f x))).bind (fun k => k y)) =
      densityAtValue (realPushforwardOnValue (some p) (some fun x => some (f x))) (some y) := by
  rw [massValue, cover.masked_pairing p hm slope (fun x hx e => hd x hx (by simp [e])),
    cover.density p hm slope hd]
  simp only [Value.mul_one_right]

namespace Coordinates.Quadratic

theorem masked_marginal (c a b : ℚ) (ha : a ≠ 0) {h t u : Option ℝ}
    (hc : h = some (c:ℝ)) (ht : t = some (a:ℝ)) (hu : u = some (b:ℝ)) {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) u)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0)
    (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    massValue ((maskedKernel p (some f)).bind (fun k => y.bind k)) = densityAtValue (realPushforwardOnValue p (some f)) y := by
  subst h; subst t; subst u
  have hn : (a:ℝ) ≠ 0 := by exact_mod_cast ha
  rw [funext (equation c a b hn equal)]
  cases p with
  | none => rfl
  | some pred =>
    cases y with
    | none => rfl
    | some y => exact (sourceRoots_cover c a b y hn).masked_mass pred (by fun_prop) _ (fun x _ _ => derivative c a b x)

end Coordinates.Quadratic
end QSym.Distribution.GraphFibre
