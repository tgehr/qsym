import QSym.DistributionCoordinateGridChange

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid
open Set Filter Topology VariationChart

/-- A cut in the source grid names the position of the new event.
Its weight is determined in the image coordinate. -/
def ImageEvent (g : ℝ → ℝ) (e : Event) (d : Option (D ℝ)) :=
  atCut g e.1 none = d

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

theorem reciprocalTrace (q k : ℚ) (hk : k = q⁻¹) : (q:ℝ)⁻¹ = (k:ℝ) := by
  simp [hk]

theorem sqrtTrace (q k : ℚ) (hn : 0 ≤ k) (hs : k^2 = q) : Real.sqrt (q:ℝ) = (k:ℝ) := by
  rw [← hs, Rat.cast_pow, Real.sqrt_sq (Rat.cast_nonneg.mpr hn)]

/-- The equality is of distributions, so the regular term is retained even
when its Jacobian vanishes on every cell. -/
theorem finishImage {s h op jac f w es ds} (c : ScalarChange s h op jac)
    (grid : Checked f w none es) (range : RangeIn grid.chart s)
    (events : List.Forall₂ (ImageEvent (h ∘ coord f)) es ds) :
    value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue) =
      ds.foldr addValue (weightValue (some fun x => Value.mul (jac (f x)) (w x)) lebesgueValue) := by
  let chart := grid.chart.postcompose c.change range
  have values (x : ℝ) : coord f x ∈ s := range.value x
  have hv x : op (f x) = some (chart.coord x) :=
    (congrArg op (grid.values x).1).trans (c.value _ (values x))
  have weight x : Value.mul (jac (f x)) (w x) =
      some (|deriv h (coord f x)| * |deriv (coord f) x|) := by
    rw [(grid.values x).1, (grid.values x).2, c.weight _ (values x)]
    rfl
  rw [singleton_pieces chart hv, present_postcompose]
  change (es.map Prod.fst).foldr _ (weightValue (some fun x =>
    some (|deriv h (coord f x)| * |deriv (coord f) x|)) _) = _
  rw [← funext weight]
  exact foldCuts (eval := fun a => atCut (h ∘ coord f) a none) events _

end QSym.Distribution.GraphFibre.Coordinates.Grid
