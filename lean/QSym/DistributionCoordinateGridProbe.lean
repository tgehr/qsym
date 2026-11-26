import QSym.DistributionCoordinateProbe
import QSym.DistributionCoordinateGridChange

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid
open Set VariationChart

/-- Membership of the query in the intrinsic cuts is computed over rationals.
The event positions in the semantic grid are real. -/
def Probe (q : ℚ) (es : List Event) (hit : Bool) := ((q:ℝ) ∈ es.map Prod.fst ↔ hit = true)

theorem Probe.nil (q : ℚ) : Probe q [] false := by simp [Probe]

theorem Probe.cons (q a : ℚ) (d : Option (D ℝ)) {es hit} (t : Probe q es hit) :
    Probe q (((a:ℝ), d) :: es) (decide (q = a) || hit) := by
  have tail : ((q:ℝ) ∈ es.map Prod.fst) ↔ hit = true := t
  simp [Probe, tail]

private theorem checkedDensity {q es f w hit} (grid : Checked f w none es) (probe : Probe q es hit) :
    densityAtValue (value (Tensor.consValue (some f) Tensor.nilValue)) (some (q:ℝ)) =
      if hit then none else w q := by
  rw [singleton_pieces grid.chart (fun x => (grid.values x).1), density_present]
  change (if (q:ℝ) ∈ es.map Prod.fst then none else some |deriv (coord f) q|) = _
  have test : ((q:ℝ) ∈ es.map Prod.fst) ↔ hit = true := probe
  simp only [test, (grid.values (q:ℝ)).2]

theorem probeCut {es f w} (q : ℚ) {z : Option ℝ} (hz : z = some (q:ℝ))
    (grid : Checked f w none es) (probe : Probe q es true) :
    densityAtValue (value (Tensor.consValue (some f) Tensor.nilValue)) z = none := by
  subst z; exact checkedDensity grid probe

theorem probeRegular {es f w} (q : ℚ) {z v : Option ℝ} (hz : z = some (q:ℝ))
    (grid : Checked f w none es) (probe : Probe q es false) (hw : w q = v) :
    densityAtValue (value (Tensor.consValue (some f) Tensor.nilValue)) z = v := by
  subst z; exact (checkedDensity grid probe).trans hw

private theorem changedDensityOn {s h op jac f w es q hit} (c : ScalarChange s h op jac)
    (grid : Checked f w none es) (range : RangeIn grid.chart s) (probe : Probe q es hit) :
    densityAtValue (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) (some (q:ℝ)) =
      if hit then none else Value.mul (jac (f q)) (w q) := by
  have values (x : ℝ) : coord f x ∈ s := range.value x
  let t := grid.chart.postcompose c.change range
  have hv x : op (f x) = some (t.coord x) := (congrArg op (grid.values x).1).trans (c.value _ (values x))
  rw [singleton_pieces t hv, density_present]
  change (if (q:ℝ) ∈ es.map Prod.fst then none else some |deriv (h ∘ coord f) q|) = _
  have test : ((q:ℝ) ∈ es.map Prod.fst) ↔ hit = true := probe
  simp only [test, c.change.deriv_comp values, abs_mul, (grid.values (q:ℝ)).1,
    (grid.values (q:ℝ)).2, c.weight _ (values _)]
  rfl

/-- Membership of both one-sided traces in the domain of the outer operation. -/
def CutRange (s : Set ℝ) (f : Scalar) (es : List Event) :=
  ∀ e ∈ es, Function.leftLim (coord f) e.1 ∈ s ∧ Function.rightLim (coord f) e.1 ∈ s

theorem CutRange.nil (s : Set ℝ) (f : Scalar) : CutRange s f [] := by simp [CutRange]

theorem CutRange.cons {s f es a d} {l r : ℝ}
    (ends : Function.leftLim (coord f) a = l ∧ Function.rightLim (coord f) a = r)
    (hl : l ∈ s) (hr : r ∈ s) (t : CutRange s f es) : CutRange s f ((a,d) :: es) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨ends.1.symm ▸ hl, ends.2.symm ▸ hr⟩
  · exact t e he

theorem CutRange.positive (q : ℚ) (hq : decide (0 < q) = true) : (q:ℝ) ∈ Ioi (0:ℝ) := by
  change (0:ℝ) < (q:ℝ)
  exact_mod_cast of_decide_eq_true hq

theorem CutRange.nonzero (q : ℚ) (hq : decide (q ≠ 0) = true) : (q:ℝ) ∈ {u : ℝ | u ≠ 0} :=
  Rat.cast_ne_zero.mpr (of_decide_eq_true hq)

theorem Checked.rangeIn {s f w es} (grid : Checked f w none es) (src : SourceIn s f)
    (traces : CutRange s f es) : RangeIn grid.chart s := by
  refine ⟨fun x => src x _ (grid.values x).1, fun a ha => ?_⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  exact traces e he

theorem probeRangeCut {s h op jac f w es} (c : ScalarChange s h op jac) (q : ℚ)
    {z : Option ℝ} (hz : z = some (q:ℝ)) (grid : Checked f w none es)
    (range : RangeIn grid.chart s) (probe : Probe q es true) :
    densityAtValue (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) z = none := by
  subst z; exact changedDensityOn c grid range probe

theorem probeRangeRegular {s h op jac f w es} (c : ScalarChange s h op jac) (q : ℚ)
    {z u k : Option ℝ} (hz : z = some (q:ℝ)) (grid : Checked f w none es)
    (range : RangeIn grid.chart s) (probe : Probe q es false) (hv : f q = u) (hw : w q = k) :
    densityAtValue (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) z = Value.mul (jac u) k := by
  subst z; subst u; subst k; exact changedDensityOn c grid range probe

private theorem changedDensity {s h op jac f w es q hit} (c : ScalarChange s h op jac)
    (src : SourceIn s f) (grid : Checked f w none es) (cuts : ContinuousCuts f es) (probe : Probe q es hit) :
    densityAtValue (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) (some (q:ℝ)) =
      if hit then none else Value.mul (jac (f q)) (w q) := by
  have range : RangeIn grid.chart s := .of_continuousAt (fun x => src x _ (grid.values x).1) (fun a ha => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact cuts e he)
  exact changedDensityOn c grid range probe

theorem probeChangeCut {s h op jac f w es} (c : ScalarChange s h op jac) (src : SourceIn s f)
    (q : ℚ) {z : Option ℝ} (hz : z = some (q:ℝ)) (grid : Checked f w none es)
    (cuts : ContinuousCuts f es) (probe : Probe q es true) :
    densityAtValue (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) z = none := by
  subst z; exact changedDensity c src grid cuts probe

theorem probeChangeRegular {s h op jac f w es} (c : ScalarChange s h op jac) (src : SourceIn s f)
    (q : ℚ) {z u k : Option ℝ} (hz : z = some (q:ℝ)) (grid : Checked f w none es)
    (cuts : ContinuousCuts f es) (probe : Probe q es false) (hv : f q = u) (hw : w q = k) :
    densityAtValue (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) z = Value.mul (jac u) k := by
  subst z; subst u; subst k; exact changedDensity c src grid cuts probe

end QSym.Distribution.GraphFibre.Coordinates.Grid
