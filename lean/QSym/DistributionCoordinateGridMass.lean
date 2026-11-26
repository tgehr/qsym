import QSym.DistributionCoordinateGridProbe
import QSym.DistributionCoordinateMass

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid
open Set Filter Topology VariationChart

/-- A closed scalar term for the sum of all jump lengths in the output coordinate. -/
def JumpSum (g : ℝ → ℝ) (es : List Event) (z : Option ℝ) :=
  z = some (es.map (fun e => jumpLength g e.1)).sum

theorem JumpSum.nil {g z} (hz : z = some ((0:ℚ):ℝ)) : JumpSum g [] z := by
  simpa [JumpSum] using hz

theorem JumpSum.cons {s h op jac g a d es z} (c : ScalarChange s h op jac) (l r : ℚ)
    (ends : Tendsto g (𝓝[<] a) (𝓝 (l:ℝ)) ∧ Tendsto g (𝓝[>] a) (𝓝 (r:ℝ)))
    (hl : (l:ℝ) ∈ s) (hr : (r:ℝ) ∈ s) {lv rv minus : Option ℝ}
    (left : lv = some (l:ℝ)) (right : rv = some (r:ℝ)) (hm : minus = some ((-1:ℚ):ℝ))
    (t : JumpSum (h ∘ g) es z) :
    JumpSum (h ∘ g) ((a,d) :: es)
      (Value.add (Value.abs (Value.add (op rv) (Value.mul minus (op lv)))) z) := by
  obtain ⟨tl, tr⟩ := ends
  have el := leftLim_eq_of_tendsto (NeBot.ne inferInstance) (((c.change.smooth _ hl).continuousAt.tendsto).comp tl)
  have er := rightLim_eq_of_tendsto (NeBot.ne inferInstance) (((c.change.smooth _ hr).continuousAt.tendsto).comp tr)
  unfold JumpSum at t ⊢
  rw [left, right, hm, t, c.value _ hl, c.value _ hr]
  simp [Value.abs, Value.add, Value.mul, jumpLength, el, er, sub_eq_add_neg]

theorem massFlatChange {s h op jac f es} (c : ScalarChange s h op jac)
    {zero : Option ℝ} (hz : zero = some ((0:ℚ):ℝ)) (grid : Checked f (fun _ => zero) none es)
    (range : RangeIn grid.chart s) {z : Option ℝ} (total : JumpSum (h ∘ coord f) es z) :
    massValue (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) = z := by
  have hz' : zero = some 0 := by simpa only [Rat.cast_zero] using hz
  let chart := grid.chart.postcompose c.change range
  have values (x : ℝ) : coord f x ∈ s := range.value x
  have hv x : op (f x) = some (chart.coord x) := (congrArg op (grid.values x).1).trans (c.value _ (values x))
  have flat x : deriv chart.coord x = 0 := by
    have inner : deriv (coord f) x = 0 := abs_eq_zero.mp (Option.some.inj ((grid.values x).2.symm.trans hz'))
    change deriv (h ∘ coord f) x = _
    rw [c.change.deriv_comp values, inner, mul_zero]
  rw [singleton_pieces chart hv, mass_flat chart flat]
  simpa only [JumpSum, List.map_map, Function.comp_def, chart, postcompose, Checked.chart] using total.symm

end QSym.Distribution.GraphFibre.Coordinates.Grid
