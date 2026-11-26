import QSym.DistributionCoordinateGridChange

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid
open Set Filter Topology VariationChart

/-- A cut in the source grid names the position of the new event.
Its weight is determined in the image coordinate. -/
def ImageEvent (g : ℝ → ℝ) (p : Option (ℝ → Option Bool)) (e : Event) (d : Option (D ℝ)) :=
  atCut g e.1 p = d

theorem imageCorner {s h op jac g a d} (c : ScalarChange s h op jac) (v : ℚ)
    (ends : Tendsto g (𝓝[<] a) (𝓝 (v:ℝ)) ∧ Tendsto g (𝓝[>] a) (𝓝 (v:ℝ)))
    (hv : (v:ℝ) ∈ s) (event : VariationChart.corner a (some true) = d) :
    atCut (h ∘ g) a none = d := by
  rw [c.change.atCut ends.1 ends.2 hv hv]
  simpa using event

theorem imageJump {s h op jac g a} (c : ScalarChange s h op jac) (l r u v : ℚ)
    (ends : Tendsto g (𝓝[<] a) (𝓝 (l:ℝ)) ∧ Tendsto g (𝓝[>] a) (𝓝 (r:ℝ)))
    (hl : (l:ℝ) ∈ s) (hr : (r:ℝ) ∈ s) (hne : l ≠ r)
    (hu : h (l:ℝ) = (u:ℝ)) (hv : h (r:ℝ) = (v:ℝ)) :
    atCut (h ∘ g) a none = atom a (some ((|v - u| : ℚ):ℝ)) := by
  rw [c.change.atCut ends.1 ends.2 hl hr, if_neg (Rat.cast_injective.ne hne)]
  simp [hu, hv]

theorem imageTraces {s h op jac} {g : ℝ → ℝ} {a : ℝ} (c : ScalarChange s h op jac) (l r u v : ℚ)
    (ends : Tendsto g (𝓝[<] a) (𝓝 (l:ℝ)) ∧ Tendsto g (𝓝[>] a) (𝓝 (r:ℝ)))
    (hl : (l:ℝ) ∈ s) (hr : (r:ℝ) ∈ s) (hu : h (l:ℝ) = (u:ℝ)) (hv : h (r:ℝ) = (v:ℝ)) :
    Tendsto (h ∘ g) (𝓝[<] a) (𝓝 (u:ℝ)) ∧ Tendsto (h ∘ g) (𝓝[>] a) (𝓝 (v:ℝ)) := by
  rw [← hu, ← hv]
  exact ⟨((c.change.smooth _ hl).continuousAt.tendsto).comp ends.1,
    ((c.change.smooth _ hr).continuousAt.tendsto).comp ends.2⟩

theorem imageRestrictedCorner {s h op jac f a} (c : ScalarChange s h op jac)
    (pred : ℝ → Option Bool) (v : ℚ)
    (ends : Tendsto (coord f) (𝓝[<] a) (𝓝 (v:ℝ)) ∧ Tendsto (coord f) (𝓝[>] a) (𝓝 (v:ℝ)))
    (hf : f a = some (v:ℝ)) (hv : (v:ℝ) ∈ s) :
    atCut (h ∘ coord f) a (some pred) = VariationChart.corner a ((op (some (v:ℝ))).bind pred) := by
  rw [c.change.atCut ends.1 ends.2 hv hv, if_pos rfl]
  simp [coord, hf, c.value _ hv]

theorem imageTest {s h op jac} (c : ScalarChange s h op jac) (pred : ℝ → Option Bool)
    (v u : ℚ) (hv : (v:ℝ) ∈ s) (hu : h (v:ℝ) = (u:ℝ)) {b : Bool}
    (hp : pred u = some b) : (op (some (v:ℝ))).bind pred = some b := by
  rw [c.value _ hv, hu]
  exact hp

theorem reciprocalTrace (q k : ℚ) (hk : k = q⁻¹) : (q:ℝ)⁻¹ = (k:ℝ) := by
  simp [hk]

theorem sqrtTrace (q k : ℚ) (hn : 0 ≤ k) (hs : k^2 = q) : Real.sqrt (q:ℝ) = (k:ℝ) := by
  rw [← hs, Rat.cast_pow, Real.sqrt_sq (Rat.cast_nonneg.mpr hn)]

private theorem sqrt_gap_one {l r : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r) :
    Real.sqrt r - Real.sqrt l = 1 ↔ 0 ≤ r - l - 1 ∧ (r - l - 1)^2 = 4*l := by
  have sl := Real.sq_sqrt hl
  have sr := Real.sq_sqrt hr
  have nn := Real.sqrt_nonneg l
  constructor
  · intro h
    have e : Real.sqrt r = Real.sqrt l + 1 := by linarith
    rw [e] at sr
    have d : r - l - 1 = 2 * Real.sqrt l := by nlinarith only [sr, sl]
    rw [d]
    exact ⟨by positivity, by nlinarith only [sl]⟩
  · rintro ⟨hn, hs⟩
    have d := (sq_eq_sq₀ hn (show 0 ≤ 2 * Real.sqrt l by positivity)).mp
      (show (r - l - 1)^2 = (2 * Real.sqrt l)^2 by rw [hs]; nlinarith only [sl])
    have e := (sq_eq_sq₀ (Real.sqrt_nonneg r) (show 0 ≤ Real.sqrt l + 1 by positivity)).mp
      (show (Real.sqrt r)^2 = (Real.sqrt l + 1)^2 by nlinarith only [sl, sr, d])
    linarith only [e]

/-- Rational arithmetic decides whether a square-root jump is exactly one,
even when the endpoint values cannot be written as rationals. -/
def sqrtUnitGap (l r : ℚ) : Bool :=
  let d := max l r - min l r - 1
  decide (0 ≤ d ∧ d^2 = 4 * min l r)

theorem sqrtImageJump {g : ℝ → ℝ} {a : ℝ} (l r : ℚ)
    (ends : Tendsto g (𝓝[<] a) (𝓝 (l:ℝ)) ∧ Tendsto g (𝓝[>] a) (𝓝 (r:ℝ)))
    (hl : (l:ℝ) ∈ Ioi (0:ℝ)) (hr : (r:ℝ) ∈ Ioi (0:ℝ)) (hne : l ≠ r)
    {av lo hi minus : Option ℝ} (ha : av = some a) (hlo : lo = some ((min l r : ℚ):ℝ))
    (hhi : hi = some ((max l r : ℚ):ℝ)) (hm : minus = some ((-1:ℚ):ℝ)) :
    atCut (Real.sqrt ∘ g) a none =
      if sqrtUnitGap l r then diracValue av else scaleValue
        (Value.add (Functions.sqrtR.apply hi) (Value.mul minus (Functions.sqrtR.apply lo))) (diracValue av) := by
  subst av; subst lo; subst hi; subst minus
  change 0 < (l:ℝ) at hl
  change 0 < (r:ℝ) at hr
  have lo0 : 0 ≤ ((min l r : ℚ):ℝ) := by rw [Rat.cast_min]; exact le_min hl.le hr.le
  have hi0 : 0 ≤ ((max l r : ℚ):ℝ) := by rw [Rat.cast_max]; exact hl.le.trans (le_max_left _ _)
  have dist : |Real.sqrt (r:ℝ) - Real.sqrt (l:ℝ)| =
      Real.sqrt ((max l r : ℚ):ℝ) - Real.sqrt ((min l r : ℚ):ℝ) := by
    rcases le_total l r with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt (Rat.cast_le.mpr h)))]
    · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (sub_nonpos.mpr (Real.sqrt_le_sqrt (Rat.cast_le.mpr h))), neg_sub]
  have unit : (Real.sqrt ((max l r : ℚ):ℝ) - Real.sqrt ((min l r : ℚ):ℝ) = 1) ↔ sqrtUnitGap l r = true := by
    rw [sqrt_gap_one lo0 hi0]
    simp only [sqrtUnitGap, decide_eq_true_eq]
    norm_cast
  rw [ChangeOn.sqrt.atCut ends.1 ends.2 hl hr, if_neg (Rat.cast_injective.ne hne)]
  change atom a (some |Real.sqrt (r:ℝ) - Real.sqrt (l:ℝ)|) = _
  rw [dist, atom]
  have lp : 0 < ((min l r : ℚ):ℝ) := by rw [Rat.cast_min]; exact lt_min hl hr
  have hp : 0 < ((max l r : ℚ):ℝ) := by rw [Rat.cast_max]; exact hl.trans_le (le_max_left _ _)
  rw [ScalarChange.sqrt.value _ hp, ScalarChange.sqrt.value _ lp]
  simp only [Option.some.injEq, unit]
  simp only [Rat.cast_neg, Rat.cast_one, Value.add, Value.mul, neg_one_mul, sub_eq_add_neg]

/-- The equality is of distributions, so the regular term is retained even
when its Jacobian vanishes on every cell. -/
theorem finishImage {s h op jac f w es ds} (c : ScalarChange s h op jac)
    (grid : Checked f w none es) (range : RangeIn grid.chart s)
    (events : List.Forall₂ (ImageEvent (h ∘ coord f) none) es ds) :
    value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue) =
      ds.foldr addValue (weightValue (some fun x => Value.mul (jac (f x)) (w x)) lebesgueValue) :=
  (singleton_pieces _ (grid.changeValues c range)).trans ((grid.presentChange c range none).trans
    (foldCuts (eval := fun a => atCut (h ∘ coord f) a none) events _))

theorem finishImageRestricted {s h op jac f w es ds} (c : ScalarChange s h op jac)
    (pred : ℝ → Option Bool) (grid : Checked f w none es) (range : RangeIn grid.chart s)
    (events : List.Forall₂ (ImageEvent (h ∘ coord f) (some pred)) es ds) :
    restricted (some pred) (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue) =
      ds.foldr addValue (weightValue (some fun x => Value.mask ((op (f x)).bind pred)
        (Value.mul (jac (f x)) (w x))) lebesgueValue) :=
  (restricted_pieces_eq (singleton_displays _ (grid.changeValues c range)) pred).trans
    ((grid.presentChange c range (some pred)).trans
      (foldCuts (eval := fun a => atCut (h ∘ coord f) a (some pred)) events _))

end QSym.Distribution.GraphFibre.Coordinates.Grid
