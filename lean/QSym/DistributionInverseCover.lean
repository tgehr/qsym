import QSym.DistributionCoordinateVariation
import QSym.DistributionAffineSquare
import QSym.DistributionInverseSheets
import QSym.DistributionInverseBranch
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

/-- Pair the joint graph recovered from inverse coordinates with an arbitrary
partial signed test. A source guard is evaluated before the test. The chosen
regular sheets need not be exhaustive: the residual stays in source coordinates. -/
theorem inverseCover_joint_split {ι : Type} {g : ι → ℝ → Option ℝ} {f : ℝ → ℝ}
    (cover : ∀ x y, (∃ i, g i y = some x) ↔ f x = y)
    (s : Set ℝ) (hs : MeasurableSet s) (bs : List (InverseSheet f)) (h : ℝ → ℝ → Option ℝ) :
    branchIntegral s (fun x => (inverseCoverOutput g x).bind (h x)) = InverseSheet.sum s h bs := by
  rw [inverseCoverOutput_eq (f := fun x => some (f x)) (fun x y => by simpa using cover x y)]
  exact InverseSheet.reconstruct bs s hs h

/-- Several inverse coordinates may describe the same regular global branch.
Only their joint relation matters, so a repeated coordinate adds no mass. -/
theorem inverseCover_regular {ι : Type} {g : ι → ℝ → Option ℝ} {f inv slope : ℝ → ℝ}
    (cover : ∀ x y, (∃ i, g i y = some x) ↔ f x = y)
    (branch : GlobalInverseBranch f inv slope) (regular : ∀ x, slope x ≠ 0) :
    inverseCoverValue (some g) =
      weightValue (some fun y => some |slope (inv y)|⁻¹) lebesgueValue := by
  rw [inverseCover_eq (f := fun x => some (f x)) (fun x y => by simpa using cover x y),
    branch.lebesgueChart (fun _ => some true) (fun _ => ⟨_,rfl⟩)
      (fun x h => False.elim (regular x h))]
  simp [Value.mask, Value.inv, regular, weightValue, lebesgueValue, densityValue, weight,
    Value.mul_one_left]

private theorem singleton_regular {g w : ℝ → Option ℝ} {f inv slope : ℝ → ℝ}
    (branch : GlobalInverseBranch f inv slope) (regular : ∀ x, slope x ≠ 0)
    (hg : ∀ y, g y = some (inv y)) (hw : ∀ y, w y = some |slope (inv y)|⁻¹) :
    inverseCoverValue (Tensor.consValue (some g) Tensor.nilValue) =
      weightValue (some w) lebesgueValue := by
  rw [funext hw]
  apply inverseCover_regular (f := f) _ branch regular
  intro x y
  constructor
  · rintro ⟨i,h⟩
    fin_cases i
    change g y = some x at h
    rw [hg] at h
    exact (Option.some.inj h) ▸ branch.inverse y
  · intro h
    refine ⟨0, ?_⟩
    change g y = some x
    rw [hg, ← h, branch.injective (branch.inverse (f x))]

theorem sinh_inverse_coordinate :
    inverseCoverValue (Tensor.consValue (some fun y => Functions.sinhR.apply (some y)) Tensor.nilValue) =
      weightValue (some fun y => Functions.coshR.apply (some y)) lebesgueValue := by
  let branch : GlobalInverseBranch Real.arsinh Real.sinh (fun x => (√(1+x^2))⁻¹) :=
    ⟨Real.arsinh_injective, Real.arsinh_sinh, Real.hasStrictDerivAt_arsinh⟩
  apply singleton_regular branch (fun x => by positivity) (fun y => by simp [Functions.sinhR, Function1.apply])
  intro y
  simp [Functions.coshR, Function1.apply, abs_of_nonneg (Real.sqrt_nonneg _), ← Real.cosh_sq',
    Real.sqrt_sq_eq_abs, abs_inv, abs_of_pos (Real.cosh_pos _)]

theorem asinh_inverse_coordinate :
    inverseCoverValue (Tensor.consValue (some fun y => Functions.asinhR.apply (some y)) Tensor.nilValue) =
      weightValue (some fun y => Value.inv (Functions.sqrtR.apply
        (Value.add (some ((1 : ℤ) : ℝ)) ((some y).map (· ^ 2))))) lebesgueValue := by
  let branch : GlobalInverseBranch Real.sinh Real.arsinh Real.cosh :=
    ⟨Real.sinh_injective, Real.sinh_arsinh, Real.hasStrictDerivAt_sinh⟩
  apply singleton_regular branch (fun x => (Real.cosh_pos x).ne') (fun y => by simp [Functions.asinhR, Function1.apply])
  intro y
  have pos : 0 < 1+y^2 := by positivity
  simp [Functions.sqrtR, Function1.apply, Value.add, Value.inv, pos.le,
    (Real.sqrt_pos.mpr pos).ne', abs_of_pos (Real.cosh_pos _), Real.cosh_arsinh, abs_of_nonneg (Real.sqrt_nonneg _)]

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

/-- The source-restricted inverse notation uses a strict weight, so even
a zero weight checks the test at its output. An undefined predicate stays
undefined. The target-domain guards of the sheets, in contrast, short-circuit. -/
theorem inversePart_pairing_split {ι : Type} {g : ι → ℝ → Option ℝ} {f : ℝ → ℝ}
    (cover : ∀ x y, (∃ i, g i y = some x) ↔ f x = y)
    (p : Option (ℝ → Option Bool)) (bs : List (InverseSheet f)) (t : ℝ → Option ℝ) :
    ((inverseSourcePartValue p (some g)).bind (fun d => integrate d t)) =
      p.bind (fun pred => InverseSheet.sum univ
        (fun x y => Value.mul (Value.mask (pred x) (some 1)) (t y)) bs) := by
  change ((pushforwardOnValue p (some (inverseCoverOutput g))).bind _) = _
  cases p with
  | none => rfl
  | some pred =>
    rw [inverseCoverOutput_eq (f := fun x => some (f x)) (fun x y => by simpa using cover x y)]
    exact (branchIntegral_univ _).symm.trans (InverseSheet.reconstruct bs univ MeasurableSet.univ
      (fun x y => Value.mul (Value.mask (pred x) (some 1)) (t y)))

/-- Pointwise counterpart to the pairing rule. Each distinct source root
appears exactly once. A false guard suppresses its reciprocal, including
when the forward derivative vanishes. -/
theorem inversePart_density_roots {ι : Type} {g : ι → ℝ → Option ℝ} {f : ℝ → ℝ}
    (cover : ∀ x y, (∃ i, g i y = some x) ↔ f x = y) {y : ℝ} {xs : List ℝ}
    (roots : RootCover univ f y xs) (p : ℝ → Option Bool) (hf : Measurable f)
    (d : ℝ → ℝ) (hd : ∀ x ∈ xs, p x ≠ some false → HasStrictDerivAt f (d x) x) :
    densityAtValue (inverseSourcePartValue (some p) (some g)) (some y) =
      xs.foldr (fun x acc => Value.add (Value.mask (p x) (Value.inv (some |d x|))) acc) (some 0) := by
  change densityAt (.density _ (inverseCoverOutput g)) y = _
  rw [inverseCoverOutput_eq (f := fun x => some (f x)) (fun x y => by simpa using cover x y)]
  exact (congrFun (coordinates_density _) y).symm.trans (roots.density p hf d hd)

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

def ordered (swap : Bool) (op : Option ℝ → Option ℝ → Option ℝ) (x y : Option ℝ) :=
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


namespace Coordinates

/-- The displayed relation is the graph of one total continuously differentiable
coordinate. The criterion is invariant under repetitions and reindexing of sheets. -/
def Describes {ι : Type} (gs : ι → ℝ → Option ℝ) (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ ∀ x z, (∃ i, gs i x = some z) ↔ g x = z

def Displays {ι : Type} (gs : ι → ℝ → Option ℝ) (c : VariationChart) : Prop :=
  ∀ x z, (∃ i, gs i x = some z) ↔ c.coord x = z

private def interpret {ι : Type} (gs : ι → ℝ → Option ℝ)
    (p : Option (ℝ → Option Bool)) (fallback : Option (D ℝ)) : Option (D ℝ) :=
  if h : ∃ c, Displays gs c then h.choose.present p else fallback

private theorem interpret_pieces {ι : Type} {gs : ι → ℝ → Option ℝ} {c : VariationChart}
    (hc : Displays gs c) (p fallback) : interpret gs p fallback = c.present p := by
  have ex : ∃ b, Displays gs b := ⟨c, hc⟩
  have eq : ex.choose = c := VariationChart.ext_coord (funext fun x =>
    (ex.choose_spec x _).mp ((hc x _).mpr rfl))
  simp [interpret, ex, eq]

/-- Total finite-piece coordinates carry length on regular pieces and the
absolute length of each jump at its breakpoint. Other relations use the
inverse cover, including partial and multivalued inverse sheets. -/
def value {ι : Type} (coords : Option (ι → ℝ → Option ℝ)) : Option (D ℝ) :=
  coords.bind fun gs => interpret gs none (inverseCoverValue (some gs))

def restricted {ι : Type} (p : Option (ℝ → Option Bool)) (coords : Option (ι → ℝ → Option ℝ)) :
    Option (D ℝ) :=
  p.bind fun pred => coords.bind fun gs => interpret gs (some pred) (inverseSourcePartValue (some pred) (some gs))

theorem pieces_eq {ι : Type} {gs : ι → ℝ → Option ℝ} {c : VariationChart} (h : Displays gs c) :
    value (some gs) = c.present none := interpret_pieces h _ _

theorem restricted_pieces_eq {ι : Type} {gs : ι → ℝ → Option ℝ} {c : VariationChart}
    (h : Displays gs c) (p : ℝ → Option Bool) :
    restricted (some p) (some gs) = c.present (some p) := interpret_pieces h _ _

theorem length_eq {ι : Type} {gs : ι → ℝ → Option ℝ} {g : ℝ → ℝ} (hg : Describes gs g) :
    value (some gs) = weightValue (some fun x => some |deriv g x|) lebesgueValue :=
  pieces_eq (c := .smooth g hg.1) hg.2

theorem restricted_length_eq {ι : Type} {gs : ι → ℝ → Option ℝ} {g : ℝ → ℝ} (hg : Describes gs g)
    (p : ℝ → Option Bool) : restricted (some p) (some gs) =
      weightValue (some fun x => Value.mask (p (g x)) (some |deriv g x|)) lebesgueValue :=
  restricted_pieces_eq (c := .smooth g hg.1) hg.2 p

theorem singleton_displays {coord : ℝ → Option ℝ} (c : VariationChart)
    (hc : ∀ x, coord x = some (c.coord x)) :
    Displays (Fin.cases coord (Fin.elim0 : Fin 0 → ℝ → Option ℝ)) c := by
  intro x z
  constructor
  · rintro ⟨i,h⟩
    fin_cases i
    exact Option.some.inj ((hc x).symm.trans h)
  · intro h
    exact ⟨0, (hc x).trans (congrArg some h)⟩

theorem singleton_pieces {coord : ℝ → Option ℝ} (c : VariationChart)
    (hc : ∀ x, coord x = some (c.coord x)) :
    value (Tensor.consValue (some coord) Tensor.nilValue) = c.present none :=
  pieces_eq (singleton_displays c hc)

/-- On each injective piece this pointwise density gives ordinary Lebesgue
integration on the image, including the domain of every partial signed test. -/
theorem branch_image {ι : Type} {gs : ι → ℝ → Option ℝ} {g : ℝ → ℝ} (hg : Describes gs g)
    {s : Set ℝ} (hs : MeasurableSet s) (hinj : InjOn g s) (t : ℝ → Option ℝ) :
    branchIntegral (g '' s) t = branchIntegral s (fun x =>
      Value.mul (densityAtValue (value (some gs)) (some x)) (t (g x))) := by
  have hd (x : ℝ) (_ : x ∈ s) : HasDerivWithinAt g (deriv g x) s x :=
    ((hg.1.differentiable le_rfl x).hasDerivAt).hasDerivWithinAt
  rw [branchIntegral_image hs hinj hd t, length_eq hg]
  apply branchIntegral_congr hs
  intro x _
  simp only [density_weight_lebesgueValue, Option.some_bind]
  cases t (g x) <;> rfl

theorem singleton_length {coord w : ℝ → Option ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : ∀ x, coord x = some (g x)) (hw : ∀ x, w x = some |deriv g x|) :
    value (Tensor.consValue (some coord) Tensor.nilValue) = weightValue (some w) lebesgueValue := by
  rw [funext hw]
  exact singleton_pieces (.smooth g hg) hc

theorem square (product : Bool) :
    value (Tensor.consValue (some fun x => squareInput product (some x)) Tensor.nilValue) =
      weightValue (some fun x => Value.mul (some ((2 : ℤ) : ℝ)) (Value.abs (some x))) lebesgueValue := by
  apply singleton_length (g := fun x => x ^ 2) (by fun_prop)
  · intro x; cases product <;> simp [squareInput, Value.mul, pow_two]
  · intro x
    simp [Value.mul, Value.abs, deriv_square, GraphFibre.square, abs_mul]

theorem sinh :
    value (Tensor.consValue (some fun x => Functions.sinhR.apply (some x)) Tensor.nilValue) =
      weightValue (some fun x => Functions.coshR.apply (some x)) lebesgueValue := by
  apply singleton_length (coord := fun x => Functions.sinhR.apply (some x)) Real.contDiff_sinh
    (fun x => by simp [Functions.sinhR, Function1.apply])
  intro x; simp [Function1.apply, Functions.coshR, Real.deriv_sinh, abs_of_pos (Real.cosh_pos x)]

theorem asinh :
    value (Tensor.consValue (some fun x => Functions.asinhR.apply (some x)) Tensor.nilValue) =
      weightValue (some fun x => Value.inv (Functions.sqrtR.apply
        (Value.add (some ((1 : ℤ) : ℝ)) ((some x).map (· ^ 2))))) lebesgueValue := by
  apply singleton_length (coord := fun x => Functions.asinhR.apply (some x)) Real.contDiff_arsinh
    (fun x => by simp [Functions.asinhR, Function1.apply])
  intro x
  have h : 0 < 1+x^2 := by positivity
  simp [(Real.hasDerivAt_arsinh x).deriv, Value.add, Value.inv, Functions.sqrtR, Function1.apply, h.le,
    (Real.sqrt_pos.mpr h).ne', abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem affine (a b j : ℚ) (hj : j = |a|) {g : ℝ → Option ℝ} (hg : StepSource.Affine g a b)
    {v : Option ℝ} (hv : v = some (j : ℝ)) (unit : Bool) (hu : if unit then j = 1 else True) :
    value (Tensor.consValue (some g) Tensor.nilValue) =
      if unit then lebesgueValue else weightValue (some fun _ => v) lebesgueValue := by
  have h := singleton_length (w := fun _ => v) (by fun_prop) hg.equation (fun x => by
    rw [(affine_derivative (a : ℝ) (b : ℝ) x).hasDerivAt.deriv, hv, hj, Rat.cast_abs])
  cases unit
  · exact h
  · rw [h, hv, show j = 1 from hu]
    simp [weightValue, weight, lebesgueValue, densityValue, Value.mul]

/-- A gap in the displayed axis rules out a total coordinate. -/
private theorem interpret_gap {ι : Type} {gs : ι → ℝ → Option ℝ} {x : ℝ} (gap : ∀ i, gs i x = none)
    (p fallback) : interpret gs p fallback = fallback := by
  apply dif_neg
  rintro ⟨g,h⟩
  obtain ⟨i,hi⟩ := (h x _).mpr rfl
  simp [gap] at hi

theorem of_gap {ι : Type} {gs : ι → ℝ → Option ℝ} {x : ℝ} (gap : ∀ i, gs i x = none) :
    value (some gs) = inverseCoverValue (some gs) := by
  simp only [value, Option.some_bind, interpret_gap gap]

theorem restricted_of_gap {ι : Type} {gs : ι → ℝ → Option ℝ} {x : ℝ} (gap : ∀ i, gs i x = none)
    (p : Option (ℝ → Option Bool)) : restricted p (some gs) = inverseSourcePartValue p (some gs) := by
  cases p with
  | none => rfl
  | some pred =>
    simp only [restricted, Option.some_bind, interpret_gap gap]

private theorem pair_gap {l u : ℝ → Option ℝ} {x : ℝ} (hl : l x = none) (hu : u x = none) :
    value (pair l u) = inverseCoverValue (pair l u) := by
  apply of_gap (x := x)
  intro i; fin_cases i
  · exact hl
  · exact hu

theorem sqrtCover (c j : ℚ) (hj : 0 < j) {z v : Option ℝ}
    (hz : z = some (c : ℝ)) (hv : v = some (j : ℝ)) {r : ℝ → Option ℝ} (hr : r = sqrtRadius v)
    (centred : Bool) (hc : if centred then True else c = 0) (nested : Bool) {k : Option ℝ}
    (hk : k = some (((if nested then -1 else -j) : ℚ) : ℝ)) (lowerSwap upperSwap factorSwap : Bool) :
    value (pair (fun y => shift centred lowerSwap z (ordered factorSwap Value.mul k (if nested then r y else Functions.sqrtR.apply (some y))))
      (fun y => shift centred upperSwap z (r y))) = radiusImageValue z (some r) := by
  have root : Functions.sqrtR.apply (some (-1)) = none := by norm_num [Functions.sqrtR, Function1.apply]
  have rad : r (-1) = none := by simp [hr, sqrtRadius, root, Value.mul]
  refine Eq.trans (pair_gap (x := -1) ?_ ?_)
    (sqrt_cover c j hj hz hv hr centred hc nested hk lowerSwap upperSwap factorSwap)
  · simp only [shift_eq, ordered_mul, rad, root, ite_self]
    cases k <;> cases z <;> cases centred <;> rfl
  · simp only [shift_eq, rad]
    cases z <;> cases centred <;> rfl

end Coordinates

end QSym.Distribution.GraphFibre
