import QSym.Value
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Pointwise disintegration of the graph of a total real map with Lebesgue
source, at values having finitely many regular preimages. Sorting fixes a
presentation order. Completeness includes every preimage, even on null sets. -/
noncomputable section
namespace QSym.Distribution.GraphFibre
open Set

/-- The root predicate specifies the active preimage. Regularity is required
only at the roots it contains. -/
structure RegularRootList (f : ℝ → ℝ) (root : ℝ → Prop) (xs : List ℝ) : Prop where
  sorted : xs.Sorted (· < ·)
  complete : ∀ x, x ∈ xs ↔ root x
  regular : ∀ x ∈ xs, HasStrictDerivAt f (deriv f x) x ∧ deriv f x ≠ 0

theorem RegularRootList.unique {f root xs zs} (a : RegularRootList f root xs)
    (b : RegularRootList f root zs) : xs = zs :=
  a.sorted.eq_of_mem_iff b.sorted (fun x => (a.complete x).trans (b.complete x).symm)

structure RegularRoots (f : ℝ → ℝ) (y : ℝ) (xs : List ℝ) : Prop where
  sorted : xs.Sorted (· < ·)
  complete : ∀ x, x ∈ xs ↔ f x = y
  regular : ∀ x ∈ xs, HasStrictDerivAt f (deriv f x) x ∧ deriv f x ≠ 0

private theorem RegularRoots.toList {f y xs} (h : RegularRoots f y xs) :
    RegularRootList f (fun x => f x = y) xs := ⟨h.sorted, h.complete, h.regular⟩

theorem RegularRoots.unique {f y xs zs} (a : RegularRoots f y xs) (b : RegularRoots f y zs) :
    xs = zs := a.toList.unique b.toList

private def weightedRoots (f : ℝ → ℝ) (root : ℝ → Prop) : Option (List (ℝ × ℝ)) := by
  classical
  exact if h : ∃ xs, RegularRootList f root xs then
    some (h.choose.map (fun x => (x, |deriv f x|⁻¹))) else none

private theorem weightedRoots_of_regular {f root xs} (h : RegularRootList f root xs) :
    weightedRoots f root = some (xs.map (fun x => (x, |deriv f x|⁻¹))) := by
  classical
  have he : ∃ zs, RegularRootList f root zs := ⟨xs, h⟩
  simp [weightedRoots, he, he.choose_spec.unique h]

def fibre (f : ℝ → ℝ) (y : ℝ) := weightedRoots f (fun x => f x = y)

/-- Select the source before computing inverse-Jacobian weights. In particular,
a critical point outside the source cannot invalidate an empty fibre. -/
def fibreOn (s : Set ℝ) (f : ℝ → ℝ) (y : ℝ) :=
  weightedRoots f (fun x => x ∈ s ∧ f x = y)

theorem fibreOn_mem {s f y atoms} (h : fibreOn s f y = some atoms) {a : ℝ × ℝ}
    (ha : a ∈ atoms) : a.1 ∈ s := by
  classical
  unfold fibreOn weightedRoots at h
  split at h
  · rename_i roots
    cases h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact ((roots.choose_spec.complete x).mp hx).1
  · contradiction

@[simp] theorem fibreOn_univ (f : ℝ → ℝ) (y : ℝ) : fibreOn univ f y = fibre f y := by
  simp [fibreOn, fibre]

theorem fibreOn_of_regular {s f y xs} (h : RegularRootList f (fun x => x ∈ s ∧ f x = y) xs) :
    fibreOn s f y = some (xs.map (fun x => (x, |deriv f x|⁻¹))) :=
  weightedRoots_of_regular h

theorem fibre_of_regular {f y xs} (h : RegularRoots f y xs) :
    fibre f y = some (xs.map (fun x => (x, |deriv f x|⁻¹))) :=
  weightedRoots_of_regular h.toList

theorem fibreOn_of_critical {s : Set ℝ} {f : ℝ → ℝ} {x y : ℝ}
    (hx : x ∈ s) (hy : f x = y) (hz : deriv f x = 0) : fibreOn s f y = none := by
  have hn : ¬ ∃ xs, RegularRootList f (fun z => z ∈ s ∧ f z = y) xs := by
    rintro ⟨xs, h⟩
    exact (h.regular x ((h.complete x).mpr ⟨hx, hy⟩)).2 hz
  simp [fibreOn, weightedRoots, hn]

/-- Pair a finite weighted fibre with a partial test, retaining undefined
values at roots. This observation is independent of the frontend encoding. -/
def observe (atoms : List (ℝ × ℝ)) (test : ℝ → Option ℝ) : Option ℝ :=
  atoms.foldr (fun atom acc => Value.add (Value.mul (some atom.2) (test atom.1)) acc) (some 0)

theorem observe_congr {atoms : List (ℝ × ℝ)} {p q : ℝ → Option ℝ}
    (h : ∀ a ∈ atoms, p a.1 = q a.1) : observe atoms p = observe atoms q := by
  induction atoms with
  | nil => rfl
  | cons a as ih =>
    change Value.add (Value.mul _ (p a.1)) (observe as p) =
      Value.add (Value.mul _ (q a.1)) (observe as q)
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- Observe the image of a weighted real parameter. A zero coefficient
removes that parameter before testing regularity. A missing coefficient at
a regular root propagates through the strict finite sum. -/
def chartDensity (w v : ℝ → Option ℝ) (y : ℝ) : Option ℝ := by
  classical
  exact if (∀ x, Value.Defined (v x)) ∧ Measurable (fun x => (v x).getD 0) then
    (fibreOn {x | w x ≠ some 0} (fun x => (v x).getD 0) y).bind (fun atoms => observe atoms w)
  else none

def square (x : ℝ) := x ^ 2

theorem deriv_square (x : ℝ) : deriv square x = 2 * x := by
  apply HasDerivAt.deriv
  simpa [square] using hasDerivAt_pow 2 x

def jac (y : ℝ) : ℝ := (2 * √y)⁻¹

theorem square_positive {y : ℝ} (hy : 0 < y) :
    fibre square y = some [(-√y, jac y), (√y, jac y)] := by
  have hs := Real.sqrt_pos.2 hy
  have hs2 := Real.sq_sqrt hy.le
  have h : RegularRoots square y [-√y, √y] := by
    constructor
    · simp [List.Sorted, hs]
    · intro x
      simp only [List.mem_cons, List.not_mem_nil, or_false, square]
      constructor
      · rintro (rfl|rfl) <;> simpa using hs2
      · intro hx
        rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hx.trans hs2.symm) with hp|hn
        · exact Or.inr hp
        · exact Or.inl hn
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      constructor
      · rw [deriv_square]
        simpa [square] using hasStrictDerivAt_pow 2 x
      · rw [deriv_square]
        apply mul_ne_zero (by norm_num)
        rcases hx with rfl|rfl
        · exact neg_ne_zero.mpr hs.ne'
        · exact hs.ne'
  rw [fibre_of_regular h]
  simp [deriv_square, abs_mul, abs_of_pos hs, jac]

theorem square_negative {y : ℝ} (hy : y < 0) : fibre square y = some [] := by
  apply fibre_of_regular (xs := [])
  constructor
  · simp [List.Sorted]
  · intro x
    simp [square, ne_of_gt (lt_of_lt_of_le hy (sq_nonneg x))]
  · simp

theorem square_critical : fibre square 0 = none := by
  rw [← fibreOn_univ]
  exact fibreOn_of_critical (x := 0) (mem_univ _) (by simp [square]) (by simp [deriv_square])

/-- Evaluate a strict test of the retained coordinate at a positive target. -/
theorem square_observe {y : ℝ} (hy : 0 < y) (test : ℝ → Option ℝ) :
    (fibre square y).bind (fun atoms => observe atoms test) =
      Value.add (Value.mul (some (jac y)) (test (-√y))) (Value.mul (some (jac y)) (test (√y))) := by
  rw [square_positive hy]
  cases hm : test (-√y) <;> cases hp : test (√y) <;>
    simp [observe, Value.add, Value.mul, hm, hp]

/-- Interpret a graph with a partial frontend map and a partial query directly
as a finite weighted parameter space at each certified regular value. -/
def atomsValue (g : Option (ℝ → Option ℝ)) (y : Option ℝ) : Option (List (ℝ × ℝ)) := by
  classical
  exact do
    let f ← g
    let t ← y
    if (∀ x, Value.Defined (f x)) ∧ Measurable (fun x => (f x).getD 0) then
      fibre (fun x => (f x).getD 0) t
    else none

theorem atomsValue_total (f : ℝ → ℝ) (hf : Measurable f) (y : ℝ) :
    atomsValue (some (fun x => some (f x))) (some y) = fibre f y := by
  simp [atomsValue, Value.Defined, hf]

def marginal (g : Option (ℝ → Option ℝ)) (y : Option ℝ) : Option ℝ :=
  (atomsValue g y).bind (fun atoms => observe atoms (fun _ => some 1))

theorem square_marginal_positive {y : ℝ} (hy : 0 < y) :
    marginal (some (fun x => some (square x))) (some y) = some (√y)⁻¹ := by
  unfold marginal
  rw [atomsValue_total square (measurable_id.pow_const 2), square_observe hy]
  simp [jac, Value.mul, Value.add]
  <;> ring

theorem square_marginal_negative {y : ℝ} (hy : y < 0) :
    marginal (some (fun x => some (square x))) (some y) = some 0 := by
  unfold marginal
  rw [atomsValue_total square (measurable_id.pow_const 2), square_negative hy]
  rfl

theorem square_marginal_zero : marginal (some (fun x => some (square x))) (some 0) = none := by
  unfold marginal
  rw [atomsValue_total square (measurable_id.pow_const 2), square_critical]
  rfl

end QSym.Distribution.GraphFibre
