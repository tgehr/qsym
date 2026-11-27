import QSym.DistributionQuadraticChart
import QSym.DistributionSquareCover
import QSym.DistributionImageIntegral
import QSym.DistributionGraphBridge

noncomputable section
namespace QSym.Distribution.GraphFibre
open Set MeasureTheory

/-- Postcomposition by an injective target map preserves the entire sorted
root list, including critical roots. The source restriction is arbitrary. -/
theorem RootCover.postcomp {s : Set ℝ} {f g : ℝ → ℝ} {y : ℝ} {xs : List ℝ}
    (cover : RootCover s f y xs) (hg : Function.Injective g) :
    RootCover s (fun x => g (f x)) (g y) xs :=
  ⟨cover.sorted, fun x => (cover.complete x).trans (and_congr_right fun _ => hg.eq_iff.symm)⟩

namespace Coordinates.Quadratic

/-- The complete fibre in increasing source order. The vertex occurs once. -/
def sourceRoots (c t : ℝ) : List ℝ :=
  if t < 0 then [] else if t = 0 then [c] else [-√t+c, √t+c]

theorem sourceRoots_cover (c a b y : ℝ) (ha : a ≠ 0) :
    RootCover univ (fun x : ℝ => ((x-c)^2-b)/a) y (sourceRoots c (a*y+b)) := by
  let t := a*y+b
  have shift : GlobalInverseBranch (fun x : ℝ => x-c) (fun z => z+c) (fun _ => 1) :=
    ⟨fun _ _ h => by linarith, fun _ => by ring, fun x => (hasStrictDerivAt_id x).sub_const c⟩
  have back : Function.Injective (fun u : ℝ => (u-b)/a) := by
    intro u v h; field_simp [ha] at h; linarith
  have transport {xs : List ℝ} (h : RootCover univ (fun x : ℝ => (x-c)^2) t xs) :
      RootCover univ (fun x : ℝ => ((x-c)^2-b)/a) y xs := by
    have eq : (t-b)/a = y := by dsimp [t]; field_simp [ha]
    simpa only [eq] using h.postcomp back
  change RootCover _ _ _ (sourceRoots c t)
  rcases lt_trichotomy t 0 with hn | hz | hp
  · simpa only [sourceRoots, if_pos hn] using transport (squareCover_negative (fun x : ℝ => x-c) hn)
  · have root : RootCover univ (fun x : ℝ => (x-c)^2) t [0+c] := hz ▸ squareCover_zero shift
    simpa [sourceRoots, hz] using transport root
  · have hs := Real.sqrt_pos.mpr hp
    simpa only [sourceRoots, if_neg hp.not_lt, if_neg hp.ne'] using transport (squareCover_positive shift hp
      (l := -√t+c) (r := √t+c) (by linarith) (Or.inl ⟨rfl, rfl⟩))

private theorem derivative (c a b x : ℝ) :
    HasStrictDerivAt (fun u : ℝ => ((u-c)^2-b)/a) (2*(x-c)/a) x := by
  have h₁ : HasStrictDerivAt (fun u : ℝ => u-c) 1 x := (hasStrictDerivAt_id x).sub_const c
  have h₂ := (hasStrictDerivAt_pow 2 (x-c)).comp x h₁
  have h₃ : HasStrictDerivAt (fun z : ℝ => (z-b)/a) a⁻¹ ((x-c)^2) := by
    convert affine_derivative a⁻¹ (-b/a) ((x-c)^2) using 1
    ext z; ring
  simpa [Function.comp_def, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h₃.comp x h₂

/-- A source predicate is queried only at roots of this fibre. A false
predicate at the critical root suppresses its undefined inverse derivative. -/
theorem restricted_roots (c a b y : ℝ) (ha : a ≠ 0) (p : ℝ → Option Bool) :
    densityAtValue (realPushforwardOnValue (some p)
      (some fun x => some (((x-c)^2-b)/a))) (some y) =
      (sourceRoots c (a*y+b)).foldr (fun x acc =>
        Value.add (Value.mask (p x) (Value.inv (some |2*(x-c)/a|))) acc) (some 0) :=
  (sourceRoots_cover c a b y ha).density p (by fun_prop) _ (fun x _ _ => derivative c a b x)

/-- The pointwise density for an arbitrary nondegenerate quadratic in vertex
coordinates. The real square root is partial, and the reciprocal is singular
at the vertex even though that fibre integrates over the source as usual. -/
theorem density (c a b : ℝ) (ha : a ≠ 0) (query : Option ℝ) :
    densityAtValue (realPushforwardOnValue (some fun _ => some true)
      (some fun x => some (((x-c)^2-b)/a))) query =
    unrestrictedSquareDensity (some |a|) (query.map fun y => a*y+b) := by
  cases query with
  | none => rfl
  | some y =>
    rw [restricted_roots c a b y ha]
    let t := a*y+b
    change (sourceRoots c t).foldr _ _ = unrestrictedSquareDensity (some |a|) (some t)
    rcases lt_trichotomy t 0 with hn | hz | hp
    · simp [sourceRoots, hn, unrestrictedSquareDensity, Value.le, Value.mask, not_le.mpr hn]
    · simp [sourceRoots, hz, unrestrictedSquareDensity, Value.le, Value.mask, Value.add, Value.mul,
        Value.inv, Functions.sqrtR, Function1.apply]
    · have hs := Real.sqrt_pos.mpr hp
      have ha' : |a| ≠ 0 := abs_ne_zero.mpr ha
      simp [sourceRoots, hp.not_lt, hp.ne', unrestrictedSquareDensity, hp.le, Value.le, Value.mask, Value.add,
        Value.mul, Value.inv, Functions.sqrtR, Function1.apply, abs_div, abs_mul, abs_of_pos hs, hs.ne', ha]
      field_simp [ha', hs.ne']; ring

inductive Observation where
  | mass | density | integral | bind

def Observation.apply (kind : Observation) (f : ℝ → Option ℝ) (y : Option ℝ) : Option ℝ :=
  match kind with
  | .mass => marginal (some f) y
  | .density => densityAtValue (realPushforwardOnValue (some fun _ => some true) (some f)) y
  | .integral => densityAtValue (realIntegralValue (some fun x => diracValue (f x))) y
  | .bind => densityAtValue (realBindValue lebesgueValue (some fun x => diracValue (f x))) y

/-- Expose the same scalar law to direct marginal and density observations.
The gain and source identity have independent, kernel-checkable certificates. -/
theorem observation (c a b j : ℚ) (ha : a ≠ 0) (hj : j = |a|) {h t u gain : Option ℝ}
    (hc : h = some (c : ℝ)) (ht : t = some (a : ℝ)) (hu : u = some (b : ℝ))
    (hg : gain = some (j : ℝ)) {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) u)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0)
    (y : Option ℝ) (kind : Observation) :
    kind.apply f y =
    unrestrictedSquareDensity gain (Value.add (Value.mul t y) u) := by
  subst h; subst t; subst u; subst gain; subst j
  have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [funext (equation c a b hn equal), Rat.cast_abs]
  let F := fun x : ℝ => ((x-c)^2-(b:ℝ))/(a:ℝ)
  have hm : Measurable F := by dsimp [F]; fun_prop
  have target : Value.add (Value.mul (some (a:ℝ)) y) (some (b:ℝ)) = y.map (fun z => (a:ℝ)*z+b) := by
    cases y <;> rfl
  rw [target]
  have hd := density (c:ℝ) a b hn y
  have total (x : ℝ) : Value.Defined (some (F x)) := ⟨_, rfl⟩
  cases kind with
  | mass => exact (unrestricted_density_eq_marginal F hm y).symm.trans hd
  | density => exact hd
  | integral => exact (congrArg (densityAtValue · y) (integral_dirac_graph _ total)).trans hd
  | bind => exact (congrArg (densityAtValue · y) (bind_dirac_graph _ total)).trans hd

theorem literal_argument (a b q z : ℚ) {t u y : Option ℝ} (ht : t = some (a:ℝ))
    (hu : u = some (b:ℝ)) (hy : y = some (q:ℝ)) (hz : a*q+b = z) :
    Value.add (Value.mul t y) u = some (z:ℝ) := by
  subst t; subst u; subst y; subst z
  simp [Value.add, Value.mul]

theorem literal_outside (z : ℚ) (hn : z < 0) (gain : Option ℝ) :
    unrestrictedSquareDensity gain (some (z:ℝ)) = some 0 := by
  have h : (z:ℝ) < 0 := by exact_mod_cast hn
  simp [unrestrictedSquareDensity, Value.mask, Value.le, not_le.mpr h]

theorem literal_regular (j z s k : ℚ) {gain v : Option ℝ} (hg : gain = some (j:ℝ))
    (hv : v = some (k:ℝ)) (hs : 0 < s) (hz : s*s = z) (hk : j/s = k) :
    unrestrictedSquareDensity gain (some (z:ℝ)) = v := by
  subst gain; subst v; subst z; subst k
  have hp : (0:ℝ) < s := by exact_mod_cast hs
  have hn : (0:ℝ) ≤ (s:ℝ)*s := mul_nonneg hp.le hp.le
  simp [unrestrictedSquareDensity, Value.mask, Value.le, Value.mul, Value.inv, Function1.apply,
    Functions.sqrtR, hn, Real.sqrt_mul_self hp.le, hp.ne', div_eq_mul_inv, mul_comm]

end Coordinates.Quadratic
end QSym.Distribution.GraphFibre
