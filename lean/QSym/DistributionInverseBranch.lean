import QSym.DistributionMaskedGraph

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set

/-- A single inverse branch with a certified root at every target. Its
derivative may vanish. Regularity is tested at the requested inverse point. -/
structure GlobalInverseBranch (f root slope : ℝ → ℝ) : Prop where
  injective : Function.Injective f
  inverse : Function.RightInverse root f
  derivative : ∀ x, HasStrictDerivAt f (slope x) x

namespace GlobalInverseBranch
variable {f root slope : ℝ → ℝ} (c : GlobalInverseBranch f root slope)
include c

theorem fibreOn_eq (s : Set ℝ) [DecidablePred (· ∈ s)] (y : ℝ) :
    fibreOn s f y = if root y ∈ s then
      if slope (root y) = 0 then none else some [(root y, |slope (root y)|⁻¹)]
      else some [] := by
  by_cases hm : root y ∈ s
  · rw [if_pos hm]
    by_cases hz : slope (root y) = 0
    · rw [if_pos hz]
      exact fibreOn_of_critical hm (c.inverse y) ((c.derivative _).hasDerivAt.deriv.trans hz)
    · rw [if_neg hz]
      simpa only [c.inverse y] using fibreOn_of_injOn c.injective.injOn hm (c.derivative _) hz
  · rw [if_neg hm]
    apply fibreOn_of_notMem_image
    rintro ⟨x, hx, eq⟩
    exact hm (c.injective (eq.trans (c.inverse y).symm) ▸ hx)

theorem maskedAtoms_eq (p : ℝ → Option Bool) (y : ℝ) :
    maskedAtoms p f y = (Value.mask (p (root y)) (Value.inv (some |slope (root y)|))).map
      (fun w => [(root y, w)]) := by
  have roots (x : ℝ) : x ∈ [root y] ↔ f x = y := by
    rw [List.mem_singleton, ← c.injective.eq_iff, c.inverse]
  rw [maskedAtoms_of_roots p (by simp [List.Sorted]) roots]
  cases hp : p (root y) with
  | none => simp [List.mapM_cons, maskedAtom, hp, Value.mask]
  | some b =>
    cases b <;> by_cases hz : slope (root y) = 0 <;>
      simp [List.mapM_cons, maskedAtom, hp, (c.derivative _).hasDerivAt.deriv,
        c.derivative, Value.mask, Value.inv, hz]


/-- A pointwise pushforward density needs the predicate only at the inverse
point. An excluded root contributes zero even at a critical value. -/
theorem density_eq (p : ℝ → Option Bool) (y : ℝ) :
    densityAtValue (realPushforwardOnValue (some p) (some fun x => some (f x))) (some y) =
      Value.mask (p (root y)) (Value.inv (some |slope (root y)|)) := by
  classical
  let w := fun x => Value.mask (p x) (some (1 : ℝ))
  change densityAt (inLebesgueCoordinates (.density w (fun x => some (f x)))) y = _
  rw [coordinates_density]
  by_cases hi : (fun x => some (f x)) = some
  · have hf : f = id := funext (fun x => Option.some.inj (congrFun hi x))
    subst f
    have hr : root y = y := c.inverse y
    have hs : slope y = 1 := (c.derivative y).hasDerivAt.deriv.symm.trans (hasDerivAt_id y).deriv
    rw [hi, densityAt_density, hr, hs]
    simp [w, Value.inv]
  · have hm : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (c.derivative x).continuousAt)).measurable
    simp only [densityAt, realFibre, hi, if_false, RealDensityFibre.density, chartDensity,
      Option.getD_some, Value.Defined, Option.some.injEq, exists_eq', implies_true, hm, and_self, if_true]
    rw [c.fibreOn_eq]
    cases hp : p (root y) with
    | none => by_cases hz : slope (root y) = 0 <;> simp [w, hp, hz, observe, Value.add, Value.mul, Value.mask]
    | some b => cases b <;> by_cases hz : slope (root y) = 0 <;>
        simp [w, hp, hz, observe, Value.add, Value.mul, Value.mask, Value.inv]

/-- Definedness is pointwise. A partial predicate away from this fibre has
no bearing on the density at this target. -/
theorem density_defined_iff (p : ℝ → Option Bool) (y : ℝ) :
    Value.Defined (densityAtValue (realPushforwardOnValue (some p) (some fun x => some (f x))) (some y)) ↔
      Value.Defined (p (root y)) ∧ (slope (root y) = 0 → p (root y) = some false) := by
  rw [c.density_eq]
  cases h : p (root y) with
  | none => simp [Value.mask, Value.Defined]
  | some b => cases b <;> by_cases hz : slope (root y) = 0 <;> simp [Value.mask, Value.Defined, Value.inv, hz]

/-- Change coordinates for the whole distribution when the predicate is
total and excludes each critical source point. -/
theorem lebesgueChart (p : ℝ → Option Bool) (hp : ∀ x, Value.Defined (p x))
    (hc : ∀ x, slope x = 0 → p x = some false) :
    realPushforwardOnValue (some p) (some fun x => some (f x)) =
      densityValue (some fun y => Value.mask (p (root y)) (Value.inv (some |slope (root y)|))) := by
  classical
  let w := fun y => Value.mask (p (root y)) (Value.inv (some |slope (root y)|))
  let source := Presentation.density (fun x => Value.mask (p x) (some (1 : ℝ))) (fun x => some (f x))
  have inv (x : ℝ) : root (f x) = x := c.injective (c.inverse (f x))
  change some (inLebesgueCoordinates source) = some (.density w some)
  apply congrArg some
  apply inLebesgueCoordinates_of_chart
  constructor
  · funext y
    have h := c.density_eq p y
    change densityAt (inLebesgueCoordinates source) y = w y at h
    rwa [coordinates_density] at h
  · intro y
    by_cases hz : slope (root y) = 0
    · simp [w, hc _ hz, Value.mask, Value.Defined]
    · obtain ⟨b, hb⟩ := hp (root y)
      cases b <;> simp [w, Value.mask, Value.inv, hb, hz, Value.Defined]
  · intro t
    let g := fun y => Value.mul (w y) (some (t y))
    change partialIntegral volume (fun x => Value.mul (Value.mask (p x) (some 1)) (some (t (f x)))) =
      partialIntegral volume g
    have hd := fun x (_ : x ∈ (univ : Set ℝ)) => (c.derivative x).hasDerivAt.hasDerivWithinAt (s := univ)
    have eq := branchIntegral_image MeasurableSet.univ c.injective.injOn hd g
    rw [image_univ, c.inverse.surjective.range_eq, branchIntegral_univ, branchIntegral_univ] at eq
    rw [eq]
    apply congrArg (partialIntegral volume)
    funext x
    change _ = (g (f x)).map (|slope x| • ·)
    simp only [g, w, inv]
    by_cases hz : slope x = 0
    · simp [hc _ hz, Value.mask, Value.mul, smul_eq_mul]
    · obtain ⟨b, hb⟩ := hp x
      cases b <;> simp [hb, Value.mask, Value.inv, Value.mul, hz, smul_eq_mul, ← mul_assoc]

/-- The two chart premises are necessary as well as sufficient for the
pointwise density on the target to be everywhere defined. -/
theorem density_total_iff (p : ℝ → Option Bool) :
    (∀ y, Value.Defined (densityAtValue (realPushforwardOnValue (some p) (some fun x => some (f x))) (some y))) ↔
      (∀ x, Value.Defined (p x)) ∧ (∀ x, slope x = 0 → p x = some false) := by
  simp_rw [c.density_defined_iff]
  constructor
  · intro h
    have source (x : ℝ) := h (f x)
    have inv (x : ℝ) : root (f x) = x := c.injective (c.inverse (f x))
    simp only [inv] at source
    exact ⟨fun x => (source x).1, fun x => (source x).2⟩
  · rintro ⟨hp, hc⟩ y
    exact ⟨hp _, hc _⟩

end GlobalInverseBranch
end QSym.Distribution.GraphFibre
