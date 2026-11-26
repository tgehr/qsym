import QSym.DistributionCoordinateGridImage
import QSym.DistributionCoordinateProbe

/-! Point observations of restricted coordinates. Every traversed jump must have a
defined weight, including jumps away from the query. A retained corner only removes
the regular density at its own position. -/
noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid
open VariationChart

/-- Summarize the fibre contributed by a list of cuts, leaving the weight of
the ordinary Lebesgue term arbitrary. All decisions in the indices are rational. -/
def PointCuts (event : ℝ → Option (D ℝ)) (q : ℚ) (as : List ℝ) (charge : ℚ) (regular : Bool) :=
  ∀ w : Scalar, ∃ d, as.foldr (fun a rest => addValue (event a) rest)
    (weightValue (some w) lebesgueValue) = some d ∧
    realFibre d q = ⟨(charge:ℝ), if regular then w q else none⟩

namespace PointCuts

theorem nil (event : ℝ → Option (D ℝ)) (q : ℚ) : PointCuts event q [] 0 true := by
  intro w
  exact ⟨.density w some, by simp [weightValue, weight, lebesgueValue, densityValue, Value.mul_one_left],
    by simp [realFibre]⟩

private theorem cons {event as charge regular} {q a : ℚ} (k : ℚ) (b : Bool)
    (h : ∃ d, event a = some d ∧ realFibre d q = ⟨(k:ℝ), if b then some 0 else none⟩)
    (rest : PointCuts event q as charge regular) :
    PointCuts event q ((a:ℝ) :: as) (k + charge) (b && regular) := by
  intro w
  obtain ⟨d, hd, fd⟩ := h
  obtain ⟨r, hr, fr⟩ := rest w
  refine ⟨.add d r, by rw [List.foldr_cons, hd, hr]; rfl, ?_⟩
  change (realFibre d q).add (realFibre r q) = _
  rw [fd, fr]
  cases b <;> cases regular <;> cases hw : w (q:ℝ) <;> simp [RealDensityFibre.add, Value.add, hw]

theorem atom {event as charge regular} (q a k : ℚ)
    (h : event a = VariationChart.atom a (some (k:ℝ))) (rest : PointCuts event q as charge regular) :
    PointCuts event q ((a:ℝ) :: as) ((if q = a then k else 0) + charge) regular := by
  apply cons _ true _ rest
  obtain ⟨d, hd, fd⟩ := atom_fibre (a:ℝ) (k:ℝ) (q:ℝ)
  exact ⟨d, h.trans hd, by rw [fd]; by_cases eq : q = a <;> simp [eq]⟩

theorem corner {event as charge regular} (q a : ℚ) (active : Bool)
    (h : event a = VariationChart.corner a (some active)) (rest : PointCuts event q as charge regular) :
    PointCuts event q ((a:ℝ) :: as) charge ((!active || decide (q ≠ a)) && regular) := by
  have point : ∃ d, event a = some d ∧ realFibre d q =
      ⟨((0:ℚ):ℝ), if !active || decide (q ≠ a) then some 0 else none⟩ := by
    cases active with
    | false =>
      refine ⟨.density (fun _ => some 0) some, h.trans ((cornerInactive a rfl).trans ?_), ?_⟩
      · simp [weightValue, weight, lebesgueValue, densityValue, Value.mul]
      · simp [realFibre]
    | true =>
      obtain ⟨d, hd, fd⟩ := corner_components (a:ℝ)
      obtain ⟨hc, hr⟩ := fd (q:ℝ)
      refine ⟨d, h.trans hd, ?_⟩
      cases e : realFibre d q with
      | mk c r =>
        rw [e] at hc hr
        by_cases eq : q = a <;> simp_all
  simpa only [_root_.zero_add] using cons 0 _ point rest

end PointCuts

theorem probeImageAt {s h op jac f w es charge regular out} (c : ScalarChange s h op jac)
    (pred : ℝ → Option Bool) (q : ℚ) {x : Option ℝ} (hx : x = some (q:ℝ))
    (grid : Checked f w none es) (range : RangeIn grid.chart s)
    (cuts : PointCuts (fun a => atCut (h ∘ coord f) a (some pred)) q (es.map Prod.fst) charge regular)
    (answer : (if decide (charge = 0) && regular then
      Value.mask ((op (f q)).bind pred) (Value.mul (jac (f q)) (w q)) else none) = out) :
    densityAtValue (restricted (some pred) (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue)) x = out := by
  subst x
  let weight := fun y => Value.mask ((op (f y)).bind pred) (Value.mul (jac (f y)) (w y))
  obtain ⟨d, hd, fd⟩ := cuts weight
  have shape : restricted (some pred) (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue) = some d :=
    (restricted_pieces_eq (singleton_displays _ (grid.changeValues c range)) pred).trans
      ((grid.presentChange c range (some pred)).trans hd)
  rw [shape]
  change (realFibre d q).density = _
  rw [fd, ← answer]
  by_cases hz : charge = 0 <;> cases regular <;> simp [RealDensityFibre.density, hz, weight]

theorem sampleImage {s h op jac} (_c : ScalarChange s h op jac) (pred : ℝ → Option Bool)
    {v w u k : Option ℝ} (hv : v = u) (hw : w = k) :
    Value.mask ((op v).bind pred) (Value.mul (jac v) w) =
      Value.mask ((op u).bind pred) (Value.mul (jac u) k) := hv ▸ hw ▸ rfl

end QSym.Distribution.GraphFibre.Coordinates.Grid
