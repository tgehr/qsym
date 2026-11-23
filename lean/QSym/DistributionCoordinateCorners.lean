import QSym.DistributionCoordinatePiecewise

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates
open Classical Set Filter Topology

private def ramp (left : Bool) (x : ℝ) := if (if left then x < 0 else 0 < x) then x else 0

private theorem ramp_value (left closed : Bool) (x : ℝ) :
    Value.mask (rayGuard left closed x) (some x) = some (ramp left x) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> cases left <;> cases closed <;>
    simp_all [ramp, rayGuard, Value.mask, Value.lt, Value.le, not_le_of_gt, not_lt_of_gt, le_of_lt]

private theorem ramp_germ (left : Bool) {x : ℝ} (hn : x ≠ 0) :
    ramp left =ᶠ[𝓝 x] (if (if left then x < 0 else 0 < x) then id else fun _ => 0) := by
  rcases lt_or_gt_of_ne hn with hx | hx
  · filter_upwards [gt_mem_nhds hx] with y hy
    cases left <;> simp [ramp, hx, hy, not_lt_of_gt hx, not_lt_of_gt hy]
  · filter_upwards [lt_mem_nhds hx] with y hy
    cases left <;> simp [ramp, hx, hy, not_lt_of_gt hx, not_lt_of_gt hy]

private theorem ramp_corner (left : Bool) : ¬ DifferentiableAt ℝ (ramp left) 0 := by
  intro h
  have d := h.hasDerivAt
  have l : HasDerivWithinAt (ramp left) (if left then 1 else 0) (Iic 0) 0 := by
    cases left
    · apply (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr_of_mem _ right_mem_Iic
      exact fun x hx => if_neg (not_lt_of_ge (show x ≤ 0 from hx))
    · apply (hasDerivAt_id (0:ℝ)).hasDerivWithinAt.congr_of_mem _ right_mem_Iic
      intro x hx
      rcases lt_or_eq_of_le (show x ≤ 0 from hx) with h | rfl <;> simp [ramp, *]
  have r : HasDerivWithinAt (ramp left) (if left then 0 else 1) (Ici 0) 0 := by
    cases left
    · apply (hasDerivAt_id (0:ℝ)).hasDerivWithinAt.congr_of_mem _ left_mem_Ici
      intro x hx
      rcases lt_or_eq_of_le (show 0 ≤ x from hx) with h | rfl <;> simp [ramp, *]
    · apply (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr_of_mem _ left_mem_Ici
      exact fun x hx => if_neg (not_lt_of_ge (show 0 ≤ x from hx))
  have ul := uniqueDiffOn_Iic (0:ℝ) 0 right_mem_Iic
  have ur := uniqueDiffOn_Ici (0:ℝ) 0 left_mem_Ici
  have e := (l.derivWithin ul).symm.trans ((d.hasDerivWithinAt.derivWithin ul).trans
    ((d.hasDerivWithinAt.derivWithin ur).symm.trans (r.derivWithin ur)))
  cases left <;> norm_num at e

private theorem ramp_regular (left : Bool) {x : ℝ} (hx : x ≠ 0) : ContDiffAt ℝ 1 (ramp left) x := by
  apply ContDiffAt.congr_of_eventuallyEq _ (ramp_germ left hx)
  by_cases h : (if left then x < 0 else 0 < x) <;> simp [h] <;> fun_prop

private theorem ramp_continuous (left : Bool) : Continuous (ramp left) := by
  cases left
  · have eq : ramp false = fun x => max x 0 := by
      funext x; by_cases h : 0 < x <;> simp [ramp, h, max_eq_left, max_eq_right, *] <;> linarith
    rw [eq]; exact continuous_id.max continuous_const
  · have eq : ramp true = fun x => min x 0 := by
      funext x; by_cases h : x < 0 <;> simp [ramp, h, min_eq_left, min_eq_right, *] <;> linarith
    rw [eq]; exact continuous_id.min continuous_const

private def rampChart (left : Bool) : VariationChart where
  coord := ramp left
  cuts := [0]
  sorted := by simp
  exceptional x := by
    by_cases hx : x = 0
    · simp [hx, ramp_corner]
    · simp [hx, (ramp_regular left hx).differentiableAt le_rfl]
  regular x hx := ramp_regular left (by simpa using hx)
  limits x _ := ⟨_, _, (ramp_continuous left).continuousAt.continuousWithinAt,
    (ramp_continuous left).continuousAt.continuousWithinAt, Or.inl rfl⟩

/-- A continuous corner contributes no mass and keeps a missing pointwise
density. The graph of the singleton critical parameter already expresses
this in qsym's integral syntax. Both endpoint spellings give the same term. -/
theorem rayLinear (left closed : Bool) :
    value (Tensor.consValue (some fun x => Value.mask (rayGuard left closed x) (some x)) Tensor.nilValue) =
    addValue (realPushforwardOnValue (some fun s => Value.not (Value.nonzero (some s)))
      (some fun s : ℝ => (some s).map (· ^ 2)))
      (weightValue (some fun x => Value.mask (rayGuard left false x) (some ((1:ℤ):ℝ))) lebesgueValue) := by
  rw [singleton_pieces (rampChart left) (ramp_value left closed)]
  change addValue (VariationChart.atCut (ramp left) 0 none) _ = _
  apply congrArg₂ addValue
  · have h := (ramp_continuous left).continuousAt (x := 0)
    rw [VariationChart.atCut_of_limits h.continuousWithinAt h.continuousWithinAt]
    simp only [if_true, Option.elim, VariationChart.corner, add_zero]
    congr 2
    funext s
    by_cases h : s = 0 <;> simp [Value.not, Value.nonzero, h]
  · apply congrArg (fun w : ℝ → Option ℝ => weightValue (some w) lebesgueValue)
    funext x
    change some |deriv (ramp left) x| = _
    by_cases hx : x = 0
    · simp [hx, deriv_zero_of_not_differentiableAt (ramp_corner left), rayGuard, Value.mask, Value.lt]
    · have eq := (ramp_germ left hx).deriv_eq
      rw [eq]
      cases left <;> simp only [Bool.false_eq_true, ↓reduceIte, rayGuard, Int.cast_zero, Int.cast_one]
      all_goals split <;> rename_i h <;> simp [Value.lt, Value.mask, h]

/-- Combining tests on a parameterized real density preserves strict
multiplication, including at a missing output or an undefined test. -/
theorem weight_weight_chart (g f : ℝ → Option ℝ) (p : Option (ℝ → Option Bool)) (v : Option (ℝ → Option ℝ)) :
    weightValue (some f) (weightValue (some g) (realPushforwardOnValue p v)) =
      weightValue (some fun x => Value.mul (g x) (f x)) (realPushforwardOnValue p v) := by
  have h (w : ℝ → Option ℝ) (k : ℝ → Option ℝ) :
      weightValue (some f) (weightValue (some g) (some (.density w k))) =
        weightValue (some fun x => Value.mul (g x) (f x)) (some (.density w k)) := by
    change some (Presentation.density _ k) = some (Presentation.density _ k)
    congr 2
    funext x
    cases hk : k x with
    | none => simp [hk, Value.mul]
    | some y =>
      simp only [hk, Option.some_bind]
      cases w x <;> cases g y <;> cases f y <;> simp [Value.mul, mul_assoc]
  cases p with
  | none => rfl
  | some p =>
    cases v with
    | none => rfl
    | some v =>
      let d := Presentation.density (fun x => Value.mask (p x) (some 1)) v
      change weightValue _ (weightValue _ (some (inLebesgueCoordinates d))) =
        weightValue _ (some (inLebesgueCoordinates d))
      unfold inLebesgueCoordinates
      split <;> apply h

private def cornerSource (a : ℝ) : D ℝ :=
  .density (fun x => some (if x = 0 then 1 else 0)) (fun x => some (x^2+a))

private theorem corner_source_density (a y : ℝ) :
    densityAt (cornerSource a) y = if y = a then none else some 0 := by
  have ne : (fun x : ℝ => some (x^2+a)) ≠ some := by
    intro h
    have h0 := Option.some.inj (congrFun h 0)
    have h2 := Option.some.inj (congrFun h 2)
    norm_num at h0 h2
    linarith
  have hm : Measurable (fun x : ℝ => x^2+a) := by fun_prop
  simp only [cornerSource, densityAt, realFibre, ne, if_false, RealDensityFibre.density,
    chartDensity, Value.Defined, Option.some.injEq, exists_eq', implies_true, Option.getD_some, hm,
    and_self, if_true]
  by_cases hy : y = a
  · subst y
    rw [fibreOn_of_critical (x := 0) (by simp) (by simp)
      (by simpa using ((hasDerivAt_pow 2 (0:ℝ)).add_const a).deriv)]
    simp
  · rw [fibreOn_of_notMem_image (by
      rintro ⟨x,hx,he⟩
      have hx0 : x = 0 := by
        by_contra hn
        simpa [hn] using hx
      exact hy (by simpa [hx0] using he.symm))]
    simp [hy, observe]

private theorem corner_source (a : ℝ) : VariationChart.corner a (some true) = some (cornerSource a) := by
  have w (x : ℝ) : Value.mask (if x = 0 then some true else some false) (some (1:ℝ)) =
      some (if x = 0 then 1 else 0) := by split <;> rfl
  change some (inLebesgueCoordinates (.density _ _)) = _
  rw [funext w]
  exact congrArg some (coordinates_of_missing_density (by simpa using corner_source_density a a))

theorem corner_density (a y : ℝ) :
    densityAtValue (VariationChart.corner a (some true)) (some y) = if y = a then none else some 0 := by
  rw [corner_source]
  exact corner_source_density a y

/-- The critical singleton has zero charge even at the point where its
regular density is missing. This also determines its contribution to signed sums. -/
theorem corner_components (a : ℝ) : ∃ d, VariationChart.corner a (some true) = some d ∧
    ∀ y, (realFibre d y).charge = 0 ∧ (realFibre d y).regular = if y = a then none else some 0 := by
  refine ⟨cornerSource a, corner_source a, fun y => ⟨rfl, ?_⟩⟩
  have hz : (realFibre (cornerSource a) y).charge = 0 := rfl
  simpa only [densityAt, RealDensityFibre.density, hz, if_true] using corner_source_density a y

theorem corner_integral (a : ℝ) (t : ℝ → Option ℝ) (ht : ∀ y, Value.Defined (t y)) :
    massValue (weightValue (some t) (VariationChart.corner a (some true))) = some 0 := by
  rw [corner_source]
  choose v hv using ht
  rw [funext hv]
  change partialIntegral MeasureTheory.volume
    (fun x : ℝ => some (((if x = 0 then 1 else 0) * v (x^2+a)) * 1)) = _
  rw [partialIntegral_congr_away _ (fun _ => some (0:ℝ)) [0] (fun _ => ⟨_,rfl⟩) (fun _ => ⟨_,rfl⟩)
    (fun x hx => by simp [hx 0 (by simp)])]
  simp [partialIntegral, Value.Defined]

/-- An ordinary Lebesgue summand has zero singleton charge. Its pointwise
weight can therefore be added after querying the other summand. -/
theorem density_add_weight (d : Option (D ℝ)) (w : ℝ → Option ℝ) (y : Option ℝ) :
    densityAtValue (addValue d (weightValue (some w) lebesgueValue)) y =
      Value.add (densityAtValue d y) (y.bind w) := by
  cases d with
  | none => cases y <;> rfl
  | some d =>
    cases y with
    | none => rfl
    | some x =>
      by_cases h : (realFibre d x).charge = 0 <;>
        simp [densityAtValue, addValue, weightValue, weight, lebesgueValue, densityValue,
          densityAt, realFibre, RealDensityFibre.add, RealDensityFibre.density, h, Value.mul_one_left, Value.add]

/-- The surviving source singleton has Lebesgue mass zero. Totality of the
test preserves the domain of the strict source integral. -/
theorem corner_pairing (t : ℝ → Option ℝ) (ht : ∀ y, Value.Defined (t y)) :
    massValue (weightValue (some t) (realPushforwardOnValue
      (some fun s : ℝ => Value.not (Value.nonzero (some s))) (some fun s : ℝ => (some s).map (· ^ 2)))) =
      some ((0:ℤ):ℝ) := by
  have h := corner_integral 0 t ht
  have test (x : ℝ) : (if x = 0 then some true else some false) = Value.not (Value.nonzero (some x)) := by
    by_cases hx : x = 0 <;> simp [hx, Value.not, Value.nonzero]
  simpa only [VariationChart.corner, funext test, add_zero, Int.cast_zero] using h

end QSym.Distribution.GraphFibre.Coordinates
