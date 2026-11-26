import QSym.DistributionCoordinateChange
import QSym.DistributionCoordinateDomain

/-! A checked polynomial grid can be reused underneath a smooth outer operation.
At a continuous join its exceptional contribution only depends on the actual
coordinate value, so the source restriction can be pulled back at that point. -/
noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid
open Set Filter Topology VariationChart

structure ScalarChange (s : Set ℝ) (h : ℝ → ℝ) (op jac : Option ℝ → Option ℝ) where
  change : ChangeOn s h
  value : ∀ u ∈ s, op (some u) = some (h u)
  weight : ∀ u ∈ s, jac (some u) = some |deriv h u|

namespace ScalarChange

def exp : ScalarChange univ Real.exp Functions.expR.apply Functions.expR.apply :=
  ⟨.exp, fun u _ => by simp [Function1.apply, Functions.expR],
    fun u _ => by simp [Function1.apply, Functions.expR, (Real.hasDerivAt_exp u).deriv, abs_of_pos (Real.exp_pos u)]⟩

def sinh : ScalarChange univ Real.sinh Functions.sinhR.apply Functions.coshR.apply :=
  ⟨.sinh, fun u _ => by simp [Function1.apply, Functions.sinhR],
    fun u _ => by simp [Function1.apply, Functions.coshR, (Real.hasDerivAt_sinh u).deriv, abs_of_pos (Real.cosh_pos u)]⟩

def arsinh : ScalarChange univ Real.arsinh Functions.asinhR.apply (fun u =>
    Value.inv (Functions.sqrtR.apply (Value.add (some ((1:ℤ):ℝ)) (u.map (·^2))))) := by
  refine ⟨.arsinh, fun _ _ => by simp [Function1.apply, Functions.asinhR], fun u _ => ?_⟩
  have hp : 0 < 1 + u^2 := by positivity
  simp [Function1.apply, Functions.sqrtR, Value.inv, Value.add, hp.le, (Real.sqrt_pos.2 hp).ne',
    (Real.hasDerivAt_arsinh u).deriv, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hp))]

def log : ScalarChange (Ioi 0) Real.log Functions.logR.apply Value.inv :=
  ⟨.log, fun u hu => by simp [Function1.apply, Functions.logR, (show 0 < u from hu)],
    fun u hu => by
      change 0 < u at hu
      simp [Value.inv, hu.ne', (Real.hasDerivAt_log hu.ne').deriv, abs_of_pos (inv_pos.2 hu)]⟩

def sqrt : ScalarChange (Ioi 0) Real.sqrt Functions.sqrtR.apply (fun u =>
    Value.inv (Value.mul (some ((2:ℤ):ℝ)) (Functions.sqrtR.apply u))) := by
  refine ⟨.sqrt, fun u hu => by simp [Function1.apply, Functions.sqrtR, (show 0 < u from hu).le], fun u hu => ?_⟩
  change 0 < u at hu
  have hp := Real.sqrt_pos.2 hu
  simp [Function1.apply, Functions.sqrtR, le_of_lt hu, Value.inv, Value.mul, hp.ne',
    (Real.hasDerivAt_sqrt (ne_of_gt hu)).deriv, one_div, abs_mul, abs_of_pos (inv_pos.2 hp), abs_of_pos (by norm_num : 0 < (2:ℝ)⁻¹)]

def reciprocal : ScalarChange {u : ℝ | u ≠ 0} (fun u => u⁻¹) Value.inv
    (fun u => Value.inv (u.map (·^2))) := by
  refine ⟨.reciprocal, fun u hu => by simp [Value.inv, (show u ≠ 0 from hu)], fun u hu => ?_⟩
  have hp := sq_pos_of_ne_zero (show u ≠ 0 from hu)
  simp [Value.inv, hp.ne', deriv_inv, abs_of_pos (inv_pos.2 hp)]

end ScalarChange

def SourceIn (s : Set ℝ) (f : Scalar) := ∀ x v, f x = some v → v ∈ s

theorem SourceIn.univ (f : Scalar) : SourceIn univ f := fun _ _ _ => trivial

def ContinuousCuts (f : Scalar) (es : List Event) := ∀ e ∈ es, ContinuousAt (coord f) e.1

theorem ContinuousCuts.nil (f : Scalar) : ContinuousCuts f [] := by simp [ContinuousCuts]

theorem ContinuousCuts.cons {f es a} {d : Option (D ℝ)} (ha : ContinuousAt (coord f) a)
    (t : ContinuousCuts f es) : ContinuousCuts f ((a,d) :: es) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact ha
  · exact t e he

private theorem foldCuts {as : List Event} {ds : List (Option (D ℝ))}
    {eval : ℝ → Option (D ℝ)} (eqs : List.Forall₂ (fun e d => eval e.1 = d) as ds)
    (z : Option (D ℝ)) : (as.map Prod.fst).foldr (fun a d => addValue (eval a) d) z = ds.foldr addValue z := by
  induction eqs with
  | nil => rfl
  | cons h _ ih => exact congrArg₂ addValue h ih

private theorem foldCutCongr (as : List ℝ) {l r : ℝ → Option (D ℝ)} {z v : Option (D ℝ)}
    (cuts : ∀ a ∈ as, l a = r a) (base : z = v) :
    as.foldr (fun a d => addValue (l a) d) z = as.foldr (fun a d => addValue (r a) d) v := by
  induction as with
  | nil => exact base
  | cons a as ih =>
    exact congrArg₂ addValue (cuts _ List.mem_cons_self) (ih (fun _ hm => cuts _ (List.mem_cons_of_mem _ hm)))

private theorem finishChangeAt {s h op jac f w es} (c : ScalarChange s h op jac)
    (src : SourceIn s f) (grid : Checked f w none es) (cuts : ContinuousCuts f es)
    (p : Option (ℝ → Option Bool)) :
    ∃ t : VariationChart, (∀ x, op (f x) = some (t.coord x)) ∧
      t.present p = (es.map Prod.fst).foldr (fun a d => addValue
        (VariationChart.atCut (coord f) a (p.map fun pred u => (op (some u)).bind pred)) d)
        (weightValue (some fun x =>
          let weight := Value.mul (jac (f x)) (w x)
          p.elim weight (fun pred => Value.mask ((op (f x)).bind pred) weight)) lebesgueValue) := by
  have values (x : ℝ) := src x _ (grid.values x).1
  have atCuts (a : ℝ) (ha : a ∈ grid.chart.cuts) : ContinuousAt (coord f) a := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact cuts e he
  have range : RangeIn grid.chart s := .of_continuousAt values atCuts
  refine ⟨grid.chart.postcompose c.change range, fun x => (congrArg op (grid.values x).1).trans (c.value _ (values x)), ?_⟩
  rw [present_postcompose]
  have regular (x : ℝ) := grid.values x
  have weight x : Value.mul (jac (f x)) (w x) = some (|deriv h (coord f x)| * |deriv (coord f) x|) := by
    rw [(regular x).1, (regular x).2, c.weight _ (values x)]
    rfl
  apply foldCutCongr
  · intro a ha
    change VariationChart.atCut (h ∘ coord f) a p = _
    have ha' := atCuts a ha
    rw [atCut_of_continuousAt ((c.change.smooth _ (values a)).continuousAt.comp ha'), atCut_of_continuousAt ha']
    cases p <;> simp [Function.comp_apply, c.value _ (values a), Checked.chart]
  · apply congrArg (fun u : Scalar => weightValue (some u) lebesgueValue)
    funext x
    cases p with
    | none => exact (weight x).symm
    | some pred =>
      apply congrArg₂ Value.mask _ (weight x).symm
      rw [(regular x).1, c.value _ (values x)]
      rfl

theorem finishChange {s h op jac f w es} (c : ScalarChange s h op jac) (src : SourceIn s f)
    (grid : Checked f w none es) (cuts : ContinuousCuts f es) :
    value (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue) =
      es.foldr (fun e d => addValue e.2 d) (weightValue (some fun x => Value.mul (jac (f x)) (w x)) lebesgueValue) := by
  obtain ⟨t, ht, he⟩ := finishChangeAt c src grid cuts none
  exact (singleton_pieces t ht).trans (he.trans (grid.fold_events _))

theorem finishChangeRestricted {s h op jac f w es ds} (c : ScalarChange s h op jac) (src : SourceIn s f)
    (pred : ℝ → Option Bool) (grid : Checked f w none es) (cuts : ContinuousCuts f es)
    (events : List.Forall₂ (RestrictedEvent f (fun u => (op (some u)).bind pred)) es ds) :
    restricted (some pred) (Tensor.consValue (some fun x => op (f x)) Tensor.nilValue) =
      ds.foldr addValue (weightValue (some fun x => Value.mask ((op (f x)).bind pred) (Value.mul (jac (f x)) (w x))) lebesgueValue) := by
  obtain ⟨t, ht, he⟩ := finishChangeAt c src grid cuts (some pred)
  exact (restricted_pieces_eq (singleton_displays t ht) pred).trans (he.trans
    (foldCuts (eval := fun a => VariationChart.atCut (coord f) a (some fun u => (op (some u)).bind pred)) events _))

end QSym.Distribution.GraphFibre.Coordinates.Grid
