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

private theorem changedDensity {s h op jac f w es q hit} (c : ScalarChange s h op jac)
    (src : SourceIn s f) (grid : Checked f w none es) (cuts : ContinuousCuts f es) (probe : Probe q es hit) :
    densityAtValue (value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) (some (q:ℝ)) =
      if hit then none else Value.mul (jac (f q)) (w q) := by
  have values (x : ℝ) := src x _ (grid.values x).1
  have range : RangeIn grid.chart s := .of_continuousAt values (fun a ha => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact cuts e he)
  let t := grid.chart.postcompose c.change range
  have hv x : op (f x) = some (t.coord x) := (congrArg op (grid.values x).1).trans (c.value _ (values x))
  rw [singleton_pieces t hv, density_present]
  change (if (q:ℝ) ∈ es.map Prod.fst then none else some |deriv (h ∘ coord f) q|) = _
  have test : ((q:ℝ) ∈ es.map Prod.fst) ↔ hit = true := probe
  simp only [test, c.change.deriv_comp values, abs_mul, (grid.values (q:ℝ)).1,
    (grid.values (q:ℝ)).2, c.weight _ (values _)]
  rfl

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
