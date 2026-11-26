import QSym.DistributionCoordinateInterval
import QSym.Limit

/-! Total variation of a directed coordinate on an unbounded interval. -/
noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid.Directed
open Set Filter Topology MeasureTheory StepSource
open scoped Classical

private abbrev endFilter (below : Bool) : Filter ℝ := if below then atBot else atTop
private abbrev raySet (below : Bool) (a : ℝ) := if below then Iic a else Ioi a

private theorem left_integrable {g j : ℝ → ℝ} {v : ℝ} (a : ℝ)
    (hd : ∀ x, HasDerivAt g (j x) x) (hp : ∀ x, 0 ≤ j x) (h : Tendsto g atBot (𝓝 v)) :
    IntegrableOn j (Iic a) volume := by
  have d (x : ℝ) : HasDerivAt (fun y => -g (-y)) (j (-x)) x := by
    simpa [Function.comp_def] using ((hd (-x)).comp x (hasDerivAt_neg' x)).neg
  have t : Tendsto (fun x => -g (-x)) atTop (𝓝 (-v)) := (h.comp tendsto_neg_atTop_atBot).neg
  have i : IntegrableOn (fun x => j (-x)) (Ioi (-a)) volume :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => d x) (fun x _ => hp (-x)) t
  have k : (fun x : ℝ => -x) ⁻¹' Iic a = Ici (-a) := by ext x; simp [neg_le]
  apply (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg volume)
    (Homeomorph.neg ℝ).measurableEmbedding).1
  simpa [k, Function.comp_def] using integrableOn_Ici_iff_integrableOn_Ioi.mpr i

private theorem ray_primitive {g j : ℝ → ℝ} {v : ℝ} (below : Bool) (a : ℝ)
    (hd : ∀ x, HasDerivAt g (j x) x) (hp : ∀ x, 0 ≤ j x) (h : Tendsto g (endFilter below) (𝓝 v)) :
    IntegrableOn j (raySet below a) volume ∧
      (∫ x in raySet below a, j x) = if below then g a - v else v - g a := by
  cases below with
  | false =>
    have i := integrableOn_Ioi_deriv_of_nonneg' (a := a) (fun x _ => hd x) (fun x _ => hp x) h
    exact ⟨i, integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) i h⟩
  | true =>
    have i := left_integrable a hd hp h
    exact ⟨i, integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hd x) i h⟩

private theorem coordinate_ray {g : ℝ → ℝ} {v : ℝ} (down below : Bool) (a : ℝ)
    (sm : ContDiff ℝ 1 g) (mon : if down then Antitone g else Monotone g)
    (h : Tendsto g (endFilter below) (𝓝 v)) :
    IntegrableOn (fun x => |deriv g x|) (raySet below a) volume ∧
      (∫ x in raySet below a, |deriv g x|) = if below != down then g a - v else v - g a := by
  let G (x : ℝ) := if down then -g x else g x
  have d := sm.differentiable le_rfl
  have dg (x : ℝ) : HasDerivAt G |deriv g x| x := by
    cases down
    · simpa [G, abs_of_nonneg (nonneg_deriv_of_monotone mon (d x))] using (d x).hasDerivAt
    · simpa [G, abs_of_nonpos (nonpos_deriv_of_antitone mon (d x))] using (d x).hasDerivAt.neg
  have vg : Tendsto G (endFilter below) (𝓝 (if down then -v else v)) := by
    cases down
    · exact h
    · exact h.neg
  obtain ⟨hi, hv⟩ := ray_primitive below a dg (fun _ => abs_nonneg _) vg
  refine ⟨hi, hv.trans ?_⟩
  cases below <;> cases down <;> simp [G] <;> ring

private theorem ray_limit {g : ℝ → ℝ} (below : Bool) (a : ℝ) (sm : ContDiff ℝ 1 g)
    (hint : IntegrableOn (fun x => |deriv g x|) (raySet below a) volume) :
    Tendsto g (endFilter below) (𝓝 (limUnder (endFilter below) g)) := by
  have i : IntegrableOn (deriv g) (raySet below a) volume :=
    (integrable_norm_iff (sm.continuous_deriv le_rfl).aestronglyMeasurable).mp
      (by simpa only [Real.norm_eq_abs] using hint)
  cases below
  · exact tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (fun x _ => (sm.differentiable le_rfl x).hasDerivAt) i
  · exact tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic (fun x _ => (sm.differentiable le_rfl x).hasDerivAt) i

private def rayGuard (below strict : Bool) (bound : Option ℝ) (x : ℝ) :=
  if below then compare strict (some x) bound else compare strict bound (some x)

private theorem masked_ray (below strict : Bool) (a : ℝ) (j : ℝ → ℝ) :
    partialIntegral volume (fun x => Value.mask (rayGuard below strict (some a) x) (some (j x))) =
      if IntegrableOn j (raySet below a) volume then some (∫ x in raySet below a, j x) else none := by
  classical
  cases below with
  | false =>
    have obs := above_observation_value (g := j) (v := fun x => some (j x)) strict a (fun _ _ => rfl)
    by_cases hi : IntegrableOn j (Ioi a) volume
    · simpa [rayGuard, raySet, hi] using obs.1 hi
    · simpa [rayGuard, raySet, hi] using obs.2 hi
  | true =>
    have obs := below_observation_value (g := j) (v := fun x => some (j x)) strict a (fun _ _ => rfl)
    by_cases hi : IntegrableOn j (Iic a) volume
    · have e := obs.1 (integrableOn_Iic_iff_integrableOn_Iio.mp hi)
      simpa [rayGuard, raySet, hi, Measure.restrict_congr_set (Iio_ae_eq_Iic (μ := volume) (a := a))] using e
    · simpa [rayGuard, raySet, hi] using obs.2 (fun ht => hi (integrableOn_Iic_iff_integrableOn_Iio.mpr ht))

/-- The ray mass of a smooth monotone coordinate is its endpoint difference.
An absent endpoint or an infinite amount of variation gives an absent real mass. -/
theorem ray {f w : Scalar} (down below strict : Bool) (b m : Option ℝ)
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (h : Directed down f)
    (hw : ∀ x, w x = Value.mask (if below then compare strict (some x) b else compare strict b (some x)) (some (1 : ℝ))) :
    massValue (weightValue (some w) (value (Tensor.consValue (some f) Tensor.nilValue))) =
      (let v := Limit.value (if below then atBot else atTop) (some f)
       if below != down then Value.add (b.bind f) (Value.mul m v)
       else Value.add v (Value.mul m (b.bind f))) := by
  classical
  obtain ⟨g, sm, mon, src⟩ := h
  rw [singleton_length sm src (w := fun x => some |deriv g x|) (fun _ => rfl), weight_weight_lebesgue,
    weighted_lebesgue_mass_bridge, Model.densityMassValue_eq]
  have weight : (fun x => Value.mul (some |deriv g x|) (w x)) =
      fun x => Value.mask (rayGuard below strict b x) (some |deriv g x|) := by
    funext x
    rw [hw]
    change Value.mul _ (Value.mask (rayGuard below strict b x) _) = _
    rcases rayGuard below strict b x with _ | _ | _ <;> simp [Value.mul, Value.mask]
  change partialIntegral volume (fun x => Value.mul (some |deriv g x|) (w x)) = _
  rw [weight, hm]
  cases b with
  | none =>
    have empty : partialIntegral volume (fun x => Value.mask (rayGuard below strict none x) (some |deriv g x|)) = none := by
      apply if_neg
      intro h
      obtain ⟨v, hv⟩ := h.1 0
      cases below <;> cases strict <;> cases hv
    rw [empty]
    have miss (v : Option ℝ) (positive : Bool) : none = (if positive then Value.add (none.bind f)
        (Value.mul (some (Numeric.denote (s := .real) (-1 : ℚ))) v) else
        Value.add v (Value.mul (some (Numeric.denote (s := .real) (-1 : ℚ))) (none.bind f))) := by
      cases positive <;> cases v <;> rfl
    exact miss _ _
  | some a =>
    rw [masked_ray]
    let l := endFilter below
    haveI : l.NeBot := by
      change (endFilter below).NeBot
      cases below
      · exact (inferInstance : (atTop : Filter ℝ).NeBot)
      · exact (inferInstance : (atBot : Filter ℝ).NeBot)
    change (if IntegrableOn _ (raySet below a) volume then _ else _) =
      if below != down then Value.add (f a) (Value.mul _ (Limit.along l f))
      else Value.add (Limit.along l f) (Value.mul _ (f a))
    rw [src a]
    by_cases hi : IntegrableOn (fun x => |deriv g x|) (raySet below a) volume
    · have ht := ray_limit below a sm hi
      have lim : Limit.along l f = some (limUnder l g) := Limit.along_eq_some (Eventually.of_forall src) ht
      have val := (coordinate_ray down below a sm mon ht).2
      rw [if_pos hi, lim, val]
      cases below <;> cases down <;> simp [l, Numeric.denote, Value.mul, Value.add, sub_eq_add_neg, add_comm]
    · have lim : Limit.along l f = none := by
        cases he : Limit.along l f with
        | none => rfl
        | some v =>
          have ht := (Limit.along_eq_some_iff.mp he).2
          have tg : Tendsto g l (𝓝 v) := ht.congr fun x => by simp [src x]
          exact False.elim (hi (coordinate_ray down below a sm mon tg).1)
      rw [if_neg hi, lim]
      cases below <;> cases down <;> rfl

/-- On the whole line the two actual finite limits determine the length.
If either end has unbounded variation there is no real total mass. -/
theorem whole {f : Scalar} (down : Bool) (m : Option ℝ)
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (h : Directed down f) :
    massValue (value (Tensor.consValue (some f) Tensor.nilValue)) =
      (let lo := Limit.value atBot (some f)
       let hi := Limit.value atTop (some f)
       if down then Value.add lo (Value.mul m hi) else Value.add hi (Value.mul m lo)) := by
  classical
  obtain ⟨g, sm, mon, src⟩ := h
  let j := fun x => |deriv g x|
  rw [singleton_length sm src (w := fun x => some (j x)) (fun _ => rfl),
    weighted_lebesgue_mass_bridge, Model.densityMassValue_eq]
  change partialIntegral volume (fun x => some (j x)) = (if down then
    Value.add (Limit.along atBot f) (Value.mul m (Limit.along atTop f))
    else Value.add (Limit.along atTop f) (Value.mul m (Limit.along atBot f)))
  rw [hm]
  by_cases hi : Integrable j volume
  · have hb : Tendsto g atBot (𝓝 (limUnder atBot g)) := ray_limit true 0 sm hi.integrableOn
    have ht : Tendsto g atTop (𝓝 (limUnder atTop g)) := ray_limit false 0 sm hi.integrableOn
    rw [Limit.along_eq_some (Eventually.of_forall src) hb, Limit.along_eq_some (Eventually.of_forall src) ht,
      partialIntegral_valid volume (fun x => some (j x)) (fun x => ⟨_, rfl⟩) hi]
    change some (∫ x, j x) = _
    have total : (∫ x, j x) = (∫ x in Iic 0, j x) + (∫ x in Ioi 0, j x) := by
      rw [← setIntegral_univ, ← Iic_union_Ioi (a := 0),
        setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hi.integrableOn hi.integrableOn]
    have left : (∫ x in Iic 0, j x) = if true != down then g 0 - limUnder atBot g else limUnder atBot g - g 0 :=
      (coordinate_ray down true 0 sm mon hb).2
    have right : (∫ x in Ioi 0, j x) = if false != down then g 0 - limUnder atTop g else limUnder atTop g - g 0 :=
      (coordinate_ray down false 0 sm mon ht).2
    rw [total, left, right]
    cases down <;> simp [Value.add, Value.mul, Numeric.denote, endFilter] <;> ring
  · rw [partialIntegral_invalid volume (fun x => some (j x)) hi]
    cases hb : Limit.along atBot f with
    | none => cases down <;> cases Limit.along atTop f <;> rfl
    | some lb =>
      cases ht : Limit.along atTop f with
      | none => cases down <;> rfl
      | some rt =>
        have lb' : Tendsto g atBot (𝓝 lb) :=
          (Limit.along_eq_some_iff.mp hb).2.congr fun x => by simp [src x]
        have rt' : Tendsto g atTop (𝓝 rt) :=
          (Limit.along_eq_some_iff.mp ht).2.congr fun x => by simp [src x]
        have l := (coordinate_ray down true 0 sm mon lb').1
        have r := (coordinate_ray down false 0 sm mon rt').1
        exact False.elim (hi (by simpa [raySet, j] using l.union r))

end QSym.Distribution.GraphFibre.Coordinates.Grid.Directed

namespace QSym.Distribution.GraphFibre.Coordinates.Grid.VariationChange
open Filter Topology StepSource

private theorem endpoint_limit {l : Filter ℝ} [l.NeBot] {h k op prim} {f : Scalar} {g : ℝ → ℝ} {e : Option ℝ}
    (c : VariationChange h k op prim) (src : ∀ x, f x = some (g x)) (he : Limit.Exact l f e) :
    Limit.value l (some fun x => prim (f x)) = prim e := by
  cases e with
  | none =>
    obtain ⟨x, hx⟩ := (show ∀ᶠ x in l, f x = none from he).exists
    exact False.elim (Option.noConfusion ((src x).symm.trans hx))
  | some a =>
    obtain ⟨u, eu, hu⟩ := he
    rw [c.endpoint a]
    exact Limit.along_eq_some (eu.mono fun x hx => (congrArg prim hx).trans (c.endpoint _))
      ((c.smoothPrimitive.continuous.tendsto a).comp hu)

/-- The variation primitive at a certified finite asymptote also computes the length
on a ray crossing a critical point of the outer coordinate. -/
theorem ray {h k op prim} {f w : Scalar} (c : VariationChange h k op prim)
    (down below strict : Bool) (b m : Option ℝ) (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (v : Directed down f) (e : Option ℝ) (he : Limit.Exact (if below then atBot else atTop) f e)
    (hw : ∀ x, w x = Value.mask (if below then compare strict (some x) b else compare strict b (some x)) (some (1 : ℝ))) :
    massValue (weightValue (some w) (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue))) =
      (let atBound := b.bind fun x => prim (f x)
       if below != down then Value.add atBound (Value.mul m (prim e))
       else Value.add (prim e) (Value.mul m atBound)) := by
  have directed := c.directed v
  obtain ⟨g, sg, _, src⟩ := v
  haveI : (if below then (atBot : Filter ℝ) else atTop).NeBot := by
    cases below
    · exact (inferInstance : (atTop : Filter ℝ).NeBot)
    · exact (inferInstance : (atBot : Filter ℝ).NeBot)
  have p := Directed.ray down below strict b m hm directed hw
  rw [endpoint_limit c src he] at p
  exact (congrArg (fun d => massValue (weightValue (some w) d)) (c.length sg src)).trans p

/-- A turning coordinate can have finite total length even when its two limits coincide. -/
theorem whole {h k op prim} {f : Scalar} (c : VariationChange h k op prim) (down : Bool)
    (m : Option ℝ) (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ))) (v : Directed down f)
    (lo : Option ℝ) (hl : Limit.Exact atBot f lo) (hi : Option ℝ) (hr : Limit.Exact atTop f hi) :
    massValue (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) =
      (if down then Value.add (prim lo) (Value.mul m (prim hi))
       else Value.add (prim hi) (Value.mul m (prim lo))) := by
  have directed := c.directed v
  obtain ⟨g, sg, _, src⟩ := v
  have p := Directed.whole down m hm directed
  rw [endpoint_limit c src hl, endpoint_limit c src hr] at p
  exact (congrArg massValue (c.length sg src)).trans p

end QSym.Distribution.GraphFibre.Coordinates.Grid.VariationChange
