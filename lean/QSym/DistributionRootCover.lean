import QSym.DistributionInverseBranch

noncomputable section
namespace QSym.Distribution.GraphFibre
open Set

/-- A complete fibre in a source set, including its critical points. The order
is the source order used by the finite-atom interpretation. -/
structure RootCover (s : Set ℝ) (f : ℝ → ℝ) (y : ℝ) (xs : List ℝ) : Prop where
  sorted : xs.Sorted (· < ·)
  complete : ∀ x, x ∈ xs ↔ x ∈ s ∧ f x = y

namespace RootCover
variable {s : Set ℝ} {f g i d : ℝ → ℝ} {y : ℝ} {xs zs : List ℝ}

/-- Pull a restricted outer fibre back through a certified change of source
coordinates. The caller can order the new roots in either orientation. -/
theorem precomp (cover : RootCover s g y xs) (inner : GlobalInverseBranch f i d)
    (sorted : zs.Sorted (· < ·)) (roots : ∀ x, x ∈ zs ↔ x ∈ xs.map i) :
    RootCover (f ⁻¹' s) (fun x => g (f x)) y zs := by
  refine ⟨sorted, fun x => (roots x).trans ?_⟩
  constructor
  · rintro hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    simpa only [mem_preimage, inner.inverse t] using (cover.complete t).mp ht
  · intro h
    exact List.mem_map.mpr ⟨f x, (cover.complete _).mpr h, inner.injective (inner.inverse _)⟩

theorem restrict (cover : RootCover s f y xs) (r : Set ℝ) [DecidablePred (· ∈ r)] :
    RootCover (s ∩ r) f y (xs.filter fun x => decide (x ∈ r)) := by
  refine ⟨cover.sorted.filter _, fun x => ?_⟩
  simp only [List.mem_filter, decide_eq_true_eq, cover.complete, mem_inter_iff]
  tauto

private theorem fold_missing {xs : List ℝ} {v : ℝ → Option ℝ} {x : ℝ}
    (hx : x ∈ xs) (h : v x = none) :
    xs.foldr (fun t acc => Value.add (v t) acc) (some 0) = none := by
  induction xs with
  | nil => simp at hx
  | cons t ts ih =>
    rcases List.mem_cons.mp hx with rfl | ht
    · simp [h, Value.add]
    · simp only [List.foldr_cons, ih ht]
      cases v t <;> rfl

private theorem mapM_congrAt {α β : Type} {xs : List α} {f g : α → Option β}
    (h : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, h x List.mem_cons_self, ih (fun t ht => h t (List.mem_cons_of_mem x ht))]

/-- Every point contributes its masked inverse derivative, including an
excluded critical point with zero weight. -/
theorem masked (cover : RootCover univ f y xs) (p : ℝ → Option Bool)
    (slope : ℝ → ℝ) (hd : ∀ x ∈ xs, p x = some true → HasStrictDerivAt f (slope x) x) :
    maskedAtoms p f y = xs.mapM fun x =>
      (Value.mask (p x) (Value.inv (some |slope x|))).map (x, ·) := by
  rw [maskedAtoms_of_roots p cover.sorted (fun x => by simpa using cover.complete x)]
  apply mapM_congrAt
  intro x hx
  cases hp : p x with
  | none => simp [maskedAtom, hp, Value.mask]
  | some b =>
    cases b with
    | false => simp [maskedAtom, hp, Value.mask]
    | true =>
      have h := hd x hx hp
      by_cases hz : slope x = 0 <;> simp [maskedAtom, hp, h.hasDerivAt.deriv, h, hz, Value.mask, Value.inv]

theorem atoms (cover : RootCover univ f y xs) (slope : ℝ → ℝ)
    (hd : ∀ x ∈ xs, HasStrictDerivAt f (slope x) x) :
    fibre f y = xs.mapM fun x => (Value.inv (some |slope x|)).map (x, ·) := by
  classical
  by_cases reg : ∀ x ∈ xs, slope x ≠ 0
  · have roots : RegularRoots f y xs := ⟨cover.sorted, fun x => by simpa using cover.complete x,
        fun x hx => by rw [(hd x hx).hasDerivAt.deriv]; exact ⟨hd x hx, reg x hx⟩⟩
    rw [fibre_of_regular roots]
    have aux (ts : List ℝ) (sub : ∀ t ∈ ts, t ∈ xs) :
        some (ts.map fun x => (x, |deriv f x|⁻¹)) =
          ts.mapM fun x => (Value.inv (some |slope x|)).map (x, ·) := by
      induction ts with
      | nil => rfl
      | cons t ts ih =>
        have ht := sub t List.mem_cons_self
        rw [List.mapM_cons, ← ih (fun x hx => sub x (List.mem_cons_of_mem t hx))]
        simp [Value.inv, reg t ht, (hd t ht).hasDerivAt.deriv]
    exact aux xs (fun _ h => h)
  · push_neg at reg
    obtain ⟨x, hx, hz⟩ := reg
    rw [← fibreOn_univ, fibreOn_of_critical (mem_univ x) ((cover.complete x).mp hx).2 ((hd x hx).hasDerivAt.deriv.trans hz)]
    generalize ht : (fun t : ℝ => (Value.inv (some |slope t|)).map (t, ·)) = k
    have h : k x = none := by simp [← ht, hz, Value.inv]
    clear ht cover hd
    induction xs with
    | nil => simp at hx
    | cons t ts ih =>
      rcases List.mem_cons.mp hx with rfl | hm
      · simp [List.mapM_cons, h]
      · cases k t <;> simp [List.mapM_cons, ← ih hm]

private theorem observed_filter (xs : List ℝ) (w : ℝ → Option ℝ) (d : ℝ → ℝ)
    [DecidablePred (fun x => w x ≠ some 0)] (regular : ∀ x ∈ xs, w x ≠ some 0 → d x ≠ 0) :
    observe ((xs.filter fun x => decide (w x ≠ some 0)).map fun x => (x, |d x|⁻¹)) w =
      xs.foldr (fun x acc => Value.add
        (if w x = some 0 then some 0 else Value.mul (Value.inv (some |d x|)) (w x)) acc) (some 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have tail := ih (fun t ht => regular t (List.mem_cons_of_mem _ ht))
    by_cases h : w x = some 0
    · simpa [List.filter_cons, h, Value.add_zero_left] using tail
    · have hn := regular x List.mem_cons_self h
      simp [List.filter_cons, h, Value.inv, hn, observe] at tail ⊢
      rw [tail]

/-- A complete finite fibre determines a pointwise density, even for a
partial source coefficient. An excluded root contributes zero before the
inverse derivative is tested. -/
theorem observe_weighted (cover : RootCover univ f y xs) (w : ℝ → Option ℝ)
    (slope : ℝ → ℝ) (hd : ∀ x ∈ xs, w x ≠ some 0 → HasStrictDerivAt f (slope x) x) :
    (fibreOn {x | w x ≠ some 0} f y).bind (fun atoms => observe atoms w) =
      xs.foldr (fun x acc => Value.add
        (if w x = some 0 then some 0 else Value.mul (Value.inv (some |slope x|)) (w x)) acc) (some 0) := by
  classical
  let active := {x | w x ≠ some 0}
  have sel := cover.restrict active
  rw [univ_inter] at sel
  by_cases reg : ∀ x ∈ xs, w x ≠ some 0 → slope x ≠ 0
  · have roots : RegularRootList f (fun x => x ∈ active ∧ f x = y) _ := ⟨sel.sorted, sel.complete,
        fun x hx => by
          obtain ⟨hm, ha⟩ := List.mem_filter.mp hx
          have h := hd x hm (of_decide_eq_true ha)
          rw [h.hasDerivAt.deriv]
          exact ⟨h, reg x hm (of_decide_eq_true ha)⟩⟩
    rw [fibreOn_of_regular roots, Option.some_bind]
    have eq := List.map_congr_left (f := fun x => (x, |deriv f x|⁻¹))
      (g := fun x => (x, |slope x|⁻¹)) (l := xs.filter fun x => decide (x ∈ active))
      (fun x hx => by simp only [(hd x (List.mem_filter.mp hx).1 (of_decide_eq_true (List.mem_filter.mp hx).2)).hasDerivAt.deriv])
    rw [eq]
    exact observed_filter xs w slope reg
  · push_neg at reg
    obtain ⟨x, hx, ha, hz⟩ := reg
    rw [fibreOn_of_critical (s := active) ha ((cover.complete x).mp hx).2 ((hd x hx ha).hasDerivAt.deriv.trans hz)]
    exact (fold_missing hx (by simp [ha, hz, Value.inv, Value.mul])).symm

/-- Sum the masked inverse Jacobians of a finite fibre. Predicate values away
from this target can be partial. -/
theorem density (cover : RootCover univ f y xs) (p : ℝ → Option Bool) (hm : Measurable f)
    (slope : ℝ → ℝ)
    (hd : ∀ x ∈ xs, p x ≠ some false → HasStrictDerivAt f (slope x) x) :
    densityAtValue (realPushforwardOnValue (some p) (some fun x => some (f x))) (some y) =
      xs.foldr (fun x acc => Value.add (Value.mask (p x) (Value.inv (some |slope x|))) acc) (some 0) := by
  classical
  let w := fun x => Value.mask (p x) (some (1 : ℝ))
  change densityAt (inLebesgueCoordinates (.density w (fun x => some (f x)))) y = _
  rw [coordinates_density]
  by_cases identity : (fun x => some (f x)) = some
  · have eq : f = id := funext (fun x => Option.some.inj (congrFun identity x))
    subst f
    have roots : xs = [y] := cover.sorted.eq_of_mem_iff (by simp [List.Sorted])
      (fun x => by simp only [cover.complete, mem_univ, true_and, id_eq, List.mem_singleton])
    subst xs
    rw [identity, densityAt_density]
    by_cases inactive : p y = some false
    · simp [w, inactive, Value.mask, Value.add_zero_right]
    · have h := (hd y List.mem_cons_self inactive).hasDerivAt.deriv.symm.trans (hasDerivAt_id y).deriv
      simp [w, h, Value.inv, Value.add_zero_right]
  simp only [densityAt, realFibre, identity, if_false, RealDensityFibre.density, chartDensity,
    Option.getD_some, Value.Defined, Option.some.injEq, exists_eq', implies_true, hm, and_self, if_true]
  have active_deriv (x : ℝ) (hx : x ∈ xs) (h : w x ≠ some 0) :=
    hd x hx (fun inactive => h (by simp [w, inactive, Value.mask]))
  rw [cover.observe_weighted w slope active_deriv]
  have eq (x : ℝ) : (if w x = some 0 then some 0 else Value.mul (Value.inv (some |slope x|)) (w x)) =
      Value.mask (p x) (Value.inv (some |slope x|)) := by
    cases h : p x with
    | none => cases Value.inv (some |slope x|) <;> simp [w, h, Value.mask, Value.mul]
    | some b => cases b <;> simp [w, h, Value.mask, Value.mul_one_right]
  simp only [eq]

end RootCover
end QSym.Distribution.GraphFibre
