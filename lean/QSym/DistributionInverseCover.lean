import QSym.DistributionRadius
import QSym.DistributionRootCover
import QSym.DistributionStepSource
import QSym.Tensor

noncomputable section
namespace QSym.Distribution.GraphFibre
open Classical MeasureTheory Set

/-- Inverse coordinates describe one source line. Repeating a coordinate at a
branch boundary still describes just one source point. If a source has zero or
several distinct target values its forward output is undefined. -/
def inverseCoverOutput {ι : Type} (g : ι → ℝ → Option ℝ) (x : ℝ) : Option ℝ :=
  if h : ∃! y, ∃ i, g i y = some x then some h.choose else none

def inverseCoverValue {ι : Type} (gs : Option (ι → ℝ → Option ℝ)) : Option (D ℝ) := do
  let g ← gs
  realPushforwardOnValue (some fun _ => some true) (some (inverseCoverOutput g))

theorem inverseCoverOutput_eq {ι : Type} {g : ι → ℝ → Option ℝ} {f : ℝ → Option ℝ}
    (cover : ∀ x y, (∃ i, g i y = some x) ↔ f x = some y) :
    inverseCoverOutput g = f := by
  funext x
  unfold inverseCoverOutput
  cases hx : f x with
  | none => simp [cover, hx]
  | some z =>
    have unique : ∃! y, ∃ i, g i y = some x :=
      ⟨z, (cover x z).2 hx, fun y hy => Option.some.inj (((cover x y).1 hy).symm.trans hx)⟩
    rw [dif_pos unique, ← hx]
    exact ((cover x _).1 unique.choose_spec.1).symm

theorem inverseCover_eq {ι : Type} {g : ι → ℝ → Option ℝ} {f : ℝ → Option ℝ}
    (cover : ∀ x y, (∃ i, g i y = some x) ↔ f x = some y) :
    inverseCoverValue (some g) = realPushforwardOnValue (some fun _ => some true) (some f) := by
  simp [inverseCoverValue, inverseCoverOutput_eq cover]

/-- A global affine inverse contributes the absolute slope of the inverse,
including when it reverses orientation. -/
theorem affine_inverse_coordinate (a b j : ℚ) (ha : a ≠ 0) (hj : j = |a|)
    {g : ℝ → Option ℝ} (hg : StepSource.Affine g a b) {v : Option ℝ} (hv : v = some (j : ℝ))
    (unit : Bool) (hu : if unit then j = 1 else True) :
    inverseCoverValue (Tensor.consValue (some g) Tensor.nilValue) =
      if unit then lebesgueValue else weightValue (some fun _ => v) lebesgueValue := by
  let maps : Fin 1 → ℝ → Option ℝ := Fin.cases g Fin.elim0
  let m : ℝ := (a : ℝ)⁻¹
  let k : ℝ := -(b : ℝ) / a
  have nz : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have inv (x y : ℝ) : (∃ i, maps i y = some x) ↔ some (m*x+k) = some y := by
    constructor
    · rintro ⟨i,h⟩
      fin_cases i
      change g y = some x at h
      rw [hg.equation] at h
      rw [← Option.some.inj h]
      congr 1; dsimp [m,k]; field_simp
    · intro h
      refine ⟨0, ?_⟩
      change g y = some x
      rw [hg.equation, ← Option.some.inj h]
      congr 1; dsimp [m,k]; field_simp
  change inverseCoverValue (some maps) = _
  rw [inverseCover_eq inv]
  have e := affine_lebesgue Set.univ m k (inv_ne_zero nz)
  simp only [Set.mem_univ, decide_true, sourceWeight, if_true, one_mul, m, abs_inv, inv_inv] at e
  rw [e, hv, hj, Rat.cast_abs]
  cases unit
  · simp [weightValue, weight, densityValue, lebesgueValue, Value.mul]
  · have one : |(a : ℝ)| = 1 := by exact_mod_cast (hj ▸ hu : |a| = 1)
    simp [one, lebesgueValue]

/-- Omitting a source coordinate from an unrestricted chart is observable
even with the constant zero test. A source part therefore keeps its complete
cover, including the continuation on points with weight zero. -/
theorem inverseCover_missing_zero_test {ι : Type} {g : ι → ℝ → Option ℝ} {x : ℝ}
    (missing : ∀ i y, g i y ≠ some x) :
    (inverseCoverValue (some g)).bind (fun d => integrate d (fun _ => some 0)) = none := by
  have noTarget : inverseCoverOutput g x = none := by
    apply dif_neg
    rintro ⟨y,⟨i,hi⟩,_⟩
    exact missing i y hi
  change integrate (inLebesgueCoordinates (.density (fun _ => some 1) (inverseCoverOutput g))) _ = _
  rw [coordinates_test _ (fun _ => 0)]
  change partialIntegral volume _ = none
  unfold partialIntegral
  apply if_neg
  intro h
  simpa [noTarget, Value.Defined, Value.mul] using h.1 x

/-- Source charts with null overlap add when paired with any partial signed test. The
test must exist on their entire union, including a shared null boundary. -/
theorem inverseCover_pairing_add {ι : Type} {g : ι → ℝ → Option ℝ} {f : ℝ → ℝ}
    (cover : ∀ x y, (∃ i, g i y = some x) ↔ f x = y)
    {s t : Set ℝ} (whole : s ∪ t = univ) (dis : AEDisjoint volume s t)
    (mt : NullMeasurableSet t volume) {z : ℝ}
    (critical : densityAt (.density (fun _ => some 1) (fun x => some (f x))) z = none)
    (test : ℝ → Option ℝ) :
    (inverseCoverValue (some g)).bind (fun d => integrate d test) =
      Value.add (branchIntegral s (fun x => test (f x))) (branchIntegral t (fun x => test (f x))) := by
  rw [inverseCover_eq (f := fun x => some (f x)) (fun x y => by simpa using cover x y)]
  change integrate (inLebesgueCoordinates (.density (fun _ => some 1) (fun x => some (f x)))) _ = _
  rw [coordinates_of_missing_density critical]
  change partialIntegral volume (fun x => Value.mul (some 1) (test (f x))) = _
  simp only [Value.mul_one_left]
  rw [← branchIntegral_univ, ← whole, branchIntegral_union dis mt]

/-- The two summands retain the same forward map. Their source predicates
are complements, so a regular root belongs to exactly one summand. -/
def sourcePart (p : ℝ → Bool) (f : ℝ → ℝ) : Option (D ℝ) :=
  pushforwardOnValue (some fun x => some (p x)) (some fun x => some (f x))

private theorem part_density (p : ℝ → Bool) (f : ℝ → ℝ) (y : ℝ) :
    densityAtValue (sourcePart p f) (some y) =
      densityAtValue (realPushforwardOnValue (some fun x => some (p x)) (some fun x => some (f x))) (some y) :=
  (congrFun (coordinates_density _) y).symm

theorem inverseCover_density_add {ι : Type} {g : ι → ℝ → Option ℝ} {f : ℝ → ℝ}
    (inverse : ∀ x y, (∃ i, g i y = some x) ↔ f x = y) (hf : Measurable f)
    {y : ℝ} {xs : List ℝ} (roots : RootCover univ f y xs)
    (d : ℝ → ℝ) (hd : ∀ x ∈ xs, HasStrictDerivAt f (d x) x) (p : ℝ → Bool) :
    densityAtValue (inverseCoverValue (some g)) (some y) =
      densityAtValue (addValue (sourcePart p f) (sourcePart (fun x => !(p x)) f)) (some y) := by
  have sum : densityAtValue (addValue (sourcePart p f) (sourcePart (fun x => !(p x)) f)) (some y) =
      Value.add (densityAtValue (sourcePart p f) (some y)) (densityAtValue (sourcePart (fun x => !(p x)) f) (some y)) := by
    simp [sourcePart, addValue, pushforwardOnValue, densityAtValue, densityAt, realFibre,
      RealDensityFibre.add, RealDensityFibre.density]
  rw [inverseCover_eq (f := fun x => some (f x)) (fun x y => by simpa using inverse x y), sum,
    part_density, part_density, roots.density _ hf d (fun x hx _ => hd x hx),
    roots.density _ hf d (fun x hx _ => hd x hx), roots.density _ hf d (fun x hx _ => hd x hx)]
  let j := fun x => Value.inv (some |d x|)
  let fold := fun (q : ℝ → Bool) (l : List ℝ) => l.foldr
    (fun x acc => Value.add (Value.mask (some (q x)) (j x)) acc) (some 0)
  change fold (fun _ => true) xs = Value.add (fold p xs) (fold (fun x => !(p x)) xs)
  clear roots hd
  induction xs with
  | nil => simp [fold, Value.add]
  | cons x xs ih =>
    simp only [fold, List.foldr_cons] at ih ⊢
    rw [ih]
    generalize (List.foldr _ _ xs : Option ℝ) = left
    generalize (List.foldr _ _ xs : Option ℝ) = right
    cases px : p x <;> cases j x <;> cases left <;> cases right <;>
      simp [Value.add, Value.mask, add_left_comm, add_assoc]

private theorem part_test {s : Set ℝ} [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (f : ℝ → ℝ) (t : ℝ → Option ℝ) (defined : ∀ x, Value.Defined (t (f x))) :
    pushforwardTest s f t = branchIntegral s (fun x => t (f x)) := by
  let k := fun x => Value.mul (some (sourceWeight s x)) (t (f x))
  have off (x : ℝ) (hx : x ∉ s) : k x = some 0 := by
    obtain ⟨v,hv⟩ := defined x
    simp [k, sourceWeight, hx, hv, Value.mul]
  rw [pushforwardTest, ← branchIntegral_eq_full hs k off]
  exact branchIntegral_congr hs (fun x hx => by simp [k, sourceWeight, hx, Value.mul_one_left])

theorem inverseCover_integral_add {ι : Type} {g : ι → ℝ → Option ℝ} {f : ℝ → ℝ}
    (inverse : ∀ x y, (∃ i, g i y = some x) ↔ f x = y) (s : Set ℝ) (hs : MeasurableSet s)
    {z : ℝ} (critical : densityAt (.density (fun _ => some 1) (fun x => some (f x))) z = none)
    (t : ℝ → Option ℝ) :
    (inverseCoverValue (some g)).bind (fun d => integrate d t) =
      (addValue (sourcePart (fun x => decide (x ∈ s)) f)
        (sourcePart (fun x => decide (x ∈ sᶜ)) f)).bind (fun d => integrate d t) := by
  rw [inverseCover_pairing_add inverse (union_compl_self s) disjoint_compl_right.aedisjoint
    hs.compl.nullMeasurableSet critical]
  change _ = Value.add
    ((pushforwardOnValue (some fun x => some (decide (x ∈ s))) (some fun x => some (f x))).bind (fun d => integrate d t))
    ((pushforwardOnValue (some fun x => some (decide (x ∈ sᶜ))) (some fun x => some (f x))).bind (fun d => integrate d t))
  rw [pushforwardOn_test, pushforwardOn_test]
  by_cases h : ∀ x, Value.Defined (t (f x))
  · rw [part_test hs f t h, part_test hs.compl f t h]
  · have missing (u : Set ℝ) : pushforwardTest u f t = none := by
      unfold pushforwardTest partialIntegral
      apply if_neg
      intro valid
      apply h
      intro x
      have hx := valid.1 x
      cases he : t (f x) <;> simp_all [Value.Defined, Value.mul]
    rw [missing, missing, ← branchIntegral_union disjoint_compl_right.aedisjoint hs.compl.nullMeasurableSet,
      union_compl_self, branchIntegral_univ]
    unfold partialIntegral
    rw [if_neg (fun valid => h valid.1)]
    rfl

/-- A source predicate can select an individual sheet while keeping a complete
inverse chart for the output map. Both arguments may themselves be partial. -/
def inverseSourcePartValue {ι : Type} (p : Option (ℝ → Option Bool)) (gs : Option (ι → ℝ → Option ℝ)) :
    Option (D ℝ) := pushforwardOnValue p (gs.map inverseCoverOutput)

/-- Inverse coordinates restricted to a set of source points. The forward
map is recovered from the coordinates and is shared by both pieces. -/
def inversePartValue {ι : Type} (g : ι → ℝ → Option ℝ) (p : ℝ → Bool) : Option (D ℝ) :=
  inverseSourcePartValue (some fun x => some (p x)) (some g)

/-- The observation interface here is for real atom-free charts. Each field
is pointwise, including the domain of every partial signed test. -/
structure ChartObservations where
  atPoint : ℝ → Option ℝ
  pairing : (ℝ → Option ℝ) → Option ℝ

def chartObservations (d : Option (D ℝ)) : ChartObservations :=
  ⟨fun y => densityAtValue d (some y), fun t => d.bind (fun a => integrate a t)⟩

theorem inverseCover_sum {ι : Type} {g : ι → ℝ → Option ℝ} {f : ℝ → ℝ}
    (inverse : ∀ x y, (∃ i, g i y = some x) ↔ f x = y) (hf : Measurable f)
    (cover : ∀ y, ∃ xs, RootCover univ f y xs) (d : ℝ → ℝ) (hd : ∀ x, HasStrictDerivAt f (d x) x)
    (s : Set ℝ) (hs : MeasurableSet s) {z : ℝ}
    (critical : densityAt (.density (fun _ => some 1) (fun x => some (f x))) z = none) :
    chartObservations (inverseCoverValue (some g)) = chartObservations
      (addValue (inversePartValue g (fun x => decide (x ∈ s))) (inversePartValue g (fun x => decide (x ∈ sᶜ)))) := by
  have eq : inverseCoverOutput g = fun x => some (f x) :=
    inverseCoverOutput_eq (fun x y => by simpa using inverse x y)
  have part (p : ℝ → Bool) : inversePartValue g p = sourcePart p f := by
    exact congrArg (fun v => pushforwardOnValue (some fun x => some (p x)) (some v)) eq
  simp only [part]
  apply congrArg₂ ChartObservations.mk
  · funext y
    obtain ⟨xs,roots⟩ := cover y
    simpa only [Set.mem_compl_iff, decide_not] using
      inverseCover_density_add inverse hf roots d (fun x _ => hd x) (fun x => decide (x ∈ s))
  · funext t
    exact inverseCover_integral_add inverse s hs critical t

/-- The current frontend can inspect a distribution as a higher-order value.
Even a sum agreeing on both observations has a distinct constructor here. -/
theorem affineSquare_not_presentation_add (a b : ℝ) (ha : a ≠ 0) (l r : Option (D ℝ)) :
    some (inLebesgueCoordinates (affineSquareSource a b)) ≠ addValue l r := by
  have critical := affine_square_critical_density a b ha
  rw [coordinates_density] at critical
  rw [coordinates_of_missing_density critical]
  cases l <;> cases r <;> simp [addValue, affineSquareSource]

private abbrev pair (l u : ℝ → Option ℝ) :=
  Tensor.consValue (some l) (Tensor.consValue (some u) Tensor.nilValue)

private theorem symmetric_cover (c : ℝ) (r : ℝ → Option ℝ)
    (positive : ∀ y v, r y = some v → 0 ≤ v) :
    inverseCoverValue (pair (fun y => (r y).map (fun v => c-v)) (fun y => (r y).map (fun v => c+v))) =
      radiusImageValue (some c) (some r) := by
  let g : Fin 2 → ℝ → Option ℝ := Fin.cases (fun y => (r y).map (fun v => c-v))
    (Fin.cases (fun y => (r y).map (fun v => c+v)) Fin.elim0)
  have rel (x y : ℝ) : (∃ i, g i y = some x) ↔ r y = some |x-c| := by
    have two : (∃ i, g i y = some x) ↔ g 0 y = some x ∨ g 1 y = some x := by
      constructor
      · rintro ⟨i,hi⟩; fin_cases i <;> tauto
      · exact fun h => h.elim (fun h => ⟨0,h⟩) (fun h => ⟨1,h⟩)
    rw [two]
    cases hv : r y with
    | none =>
      change ((r y).map (fun v => c-v) = some x ∨ (r y).map (fun v => c+v) = some x) ↔ none = some |x-c|
      simp [hv]
    | some v =>
      have hn := positive y v hv
      change ((r y).map (fun v => c-v) = some x ∨ (r y).map (fun v => c+v) = some x) ↔ some v = some |x-c|
      simp [hv]
      rw [abs_eq_max_neg]
      rcases le_total c x with h | h
      · rw [max_eq_left (by linarith)]
        exact ⟨fun h' => by rcases h' with h' | h' <;> linarith,
          fun h' => Or.inr (by linarith)⟩
      · rw [max_eq_right (by linarith)]
        exact ⟨fun h' => by rcases h' with h' | h' <;> linarith,
          fun h' => Or.inl (by linarith)⟩
  have eq : inverseCoverOutput g = radiusOutput c r := by
    funext x
    let chooseTarget (p : ℝ → Prop) : Option ℝ := if h : ∃! y, p y then some h.choose else none
    change chooseTarget (fun y => ∃ i, g i y = some x) = chooseTarget (fun y => r y = some |x-c|)
    exact congrArg chooseTarget (funext (fun y => propext (rel x y)))
  have hg : pair (fun y => (r y).map (fun v => c-v)) (fun y => (r y).map (fun v => c+v)) = some g := rfl
  rw [hg]
  exact congrArg (fun f => realPushforwardOnValue (some fun _ => some true) (some f)) eq

private theorem sqrtRadius_nonnegative {j : ℚ} (hj : 0 < j) {v : Option ℝ}
    (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ} (hr : r = sqrtRadius v) :
    ∀ y z, r y = some z → 0 ≤ z := by
  subst r; subst v
  intro y z h
  by_cases hy : 0 ≤ y <;> simp [sqrtRadius, Functions.sqrtR, Function1.apply, Value.mul, hy] at h
  exact h ▸ mul_nonneg (by exact_mod_cast hj.le) (Real.sqrt_nonneg y)

private def ordered (swap : Bool) (op : Option ℝ → Option ℝ → Option ℝ) (x y : Option ℝ) :=
  if swap then op y x else op x y

private theorem ordered_mul (s : Bool) (x y : Option ℝ) : ordered s Value.mul x y = Value.mul x y := by
  cases s <;> cases x <;> cases y <;> simp [ordered, Value.mul, mul_comm]

private def shift (centred swap : Bool) (z v : Option ℝ) :=
  if centred then ordered swap Value.add z v else v

private theorem shift_eq (b s : Bool) (x y : Option ℝ) : shift b s x y = if b then Value.add x y else y := by
  cases b <;> cases s <;> cases x <;> cases y <;> simp [shift, ordered, Value.add, add_comm]

/-- The coefficient of the decreasing branch can already have been folded
into a signed literal by the scalar elaborator. -/
theorem sqrt_cover (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ} (hr : r = sqrtRadius v)
    (centred : Bool) (hc : if centred then True else c = 0) (nested : Bool) {k : Option ℝ}
    (hk : k = some (((if nested then -1 else -j) : ℚ) : ℝ)) (lowerSwap upperSwap factorSwap : Bool) :
    inverseCoverValue (pair (fun y => shift centred lowerSwap z (ordered factorSwap Value.mul k (if nested then r y else Functions.sqrtR.apply (some y))))
      (fun y => shift centred upperSwap z (r y))) = radiusImageValue z (some r) := by
  simp only [shift_eq, ordered_mul]
  subst z; subst k
  rw [← symmetric_cover (c : ℝ) r (sqrtRadius_nonnegative hj hv hr)]
  subst r; subst v
  cases centred <;> simp only [Bool.false_eq_true, if_false, if_true] at hc
  · subst c
    cases nested <;> congr 2 <;> funext y <;> cases h : Functions.sqrtR.apply (some y) <;>
      simp [shift, sqrtRadius, h, Value.mul]
  · cases nested <;> congr 2 <;> funext y <;> cases h : Functions.sqrtR.apply (some y) <;>
      simp [shift, sqrtRadius, h, Value.mul, Value.add, sub_eq_add_neg]

end QSym.Distribution.GraphFibre
