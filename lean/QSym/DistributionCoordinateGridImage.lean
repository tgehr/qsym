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

theorem reciprocalTrace (q k : ℚ) (hk : k = q⁻¹) : (q:ℝ)⁻¹ = (k:ℝ) := by
  simp [hk]

theorem sqrtTrace (q k : ℚ) (hn : 0 ≤ k) (hs : k^2 = q) : Real.sqrt (q:ℝ) = (k:ℝ) := by
  rw [← hs, Rat.cast_pow, Real.sqrt_sq (Rat.cast_nonneg.mpr hn)]

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
