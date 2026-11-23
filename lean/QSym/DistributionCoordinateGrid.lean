import QSym.DistributionCoordinateCorners
import QSym.DistributionInterval
import QSym.DistributionFibreCertificate

/-! Source certificates for singleton coordinates on a rational polynomial grid.
Only genuine corners and jumps enter the variation chart. All tests at a cut
use the value of the original term there, in addition to its two polynomial germs. -/
noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid
open Set Filter Topology StepSource
abbrev Scalar := ℝ → Option ℝ
private def coord (f : Scalar) (x : ℝ) := (f x).getD 0

private theorem smoothPoly (p : List ℚ) : ContDiff ℝ 1 (polyEval p) := by
  induction p with
  | nil => exact contDiff_const
  | cons c p ih => exact contDiff_const.add (contDiff_id.mul ih)

private theorem samePoly {p q : List ℚ} (h : polyZero (polyAdd p (polyScale (-1) q)) = true)
    (x : ℝ) : polyEval p x = polyEval q x := by
  have hz := polyEval_zero h x
  rw [polyEval_add, polyEval_scale] at hz
  push_cast at hz
  linarith

/-- The exporter supplies a signed polynomial for the generated weight on
each cell. Its sign need not be constant within the cell. -/
def Magnitude (s : ℝ → Prop) (w : Scalar) (p : List ℚ) :=
  ∀ x, s x → w x = some |polyEval p x|

theorem magnitude_abs {s w p} (h : PolynomialOn s w p) :
    Magnitude s (fun x => Value.abs (w x)) p := by
  intro x hx
  change Value.abs (w x) = _
  rw [h.equation x hx]; rfl

theorem magnitude_mask {r : Region} {c : ℝ → Option Bool} {w p} (s : ℚ)
    (hs : s = r.sample) (hu : Uniform r c) (hc : c (s : ℝ) = some true)
    (hw : Magnitude r.contains w p) : Magnitude r.contains (fun x => Value.mask (c x) (w x)) p := by
  subst s
  intro x hx
  change Value.mask (c x) (w x) = _
  rw [hu x hx, hc, hw x hx]; rfl

theorem magnitude_zero {s w} (h : PolynomialOn s w []) : Magnitude s w [] := by
  intro x hx; simpa [polyEval] using h.equation x hx

theorem magnitude_add_left {s w v p} (hw : Magnitude s w p) (hv : PolynomialOn s v []) :
    Magnitude s (fun x => Value.add (w x) (v x)) p := by
  intro x hx; simp [hw x hx, hv.equation x hx, polyEval, Value.add]

theorem magnitude_add_right {s w v p} (hw : PolynomialOn s w []) (hv : Magnitude s v p) :
    Magnitude s (fun x => Value.add (w x) (v x)) p := by
  intro x hx; simp [hw.equation x hx, hv x hx, polyEval, Value.add]

theorem zero_on {s w p} (h : PolynomialOn s w p) (z : polyZero p = true) : PolynomialOn s w [] :=
  ⟨fun x hx => (h.equation x hx).trans (congrArg some (polyEval_zero z x))⟩

theorem zero_add {s w v} (hw : PolynomialOn s w []) (hv : PolynomialOn s v []) :
    PolynomialOn s (fun x => Value.add (w x) (v x)) [] :=
  ⟨fun x hx => by simp [hw.equation x hx, hv.equation x hx, polyEval, Value.add]⟩

structure Cell (s : ℝ → Prop) (f w : Scalar) (p : List ℚ) : Prop where
  source : PolynomialOn s f p
  weight : Magnitude s w (polyDerivative p)

theorem cell {s f w p q} (hf : PolynomialOn s f p) (hw : Magnitude s w q)
    (he : polyZero (polyAdd q (polyScale (-1) (polyDerivative p))) = true) : Cell s f w p :=
  ⟨hf, fun x hx => (hw x hx).trans (congrArg (fun z : ℝ => some |z|) (samePoly he x))⟩

theorem polynomial {f w p} (h : Cell (fun _ => True) f w p) :
    value (Tensor.consValue (some f) Tensor.nilValue) = weightValue (some w) lebesgueValue :=
  singleton_length (smoothPoly p) (fun x => h.source.equation x trivial)
    (fun x => ((polyEval_hasDerivAt p x).deriv.symm ▸ h.weight x trivial))

private structure Regular (f w : Scalar) (x : ℝ) : Prop where
  total : f x = some (coord f x)
  weight : w x = some |deriv (coord f) x|
  smooth : ContDiffAt ℝ 1 (coord f) x

private theorem cellRegular {s f w p} (h : Cell s f w p) {x : ℝ}
    (hs : ∀ᶠ y in 𝓝 x, s y) : Regular f w x := by
  have germ : coord f =ᶠ[𝓝 x] polyEval p :=
    hs.mono fun y hy => by simp [coord, h.source.equation y hy]
  refine ⟨(h.source.equation x hs.self_of_nhds).trans (congrArg some germ.self_of_nhds.symm), ?_,
    (smoothPoly p).contDiffAt.congr_of_eventuallyEq germ⟩
  rw [germ.deriv_eq, (polyEval_hasDerivAt p x).deriv]
  exact h.weight x hs.self_of_nhds

private def Above (lo : Option ℚ) (x : ℝ) := lo.elim True (fun a => (a : ℝ) < x)
def leftCell (lo : Option ℚ) (a : ℚ) : Region := lo.elim (.before a) (fun b => .between b a)
def rightCell (a : ℚ) (hi : Option ℚ) : Region := hi.elim (.after a) (fun b => .between a b)
def ordered (lo : Option ℚ) (a : ℚ) := lo.elim true (fun b => decide (b < a))
def orderedRight (a : ℚ) (hi : Option ℚ) := hi.elim true (fun b => decide (a < b))

private theorem above_ordered {lo a} (h : ordered lo a = true) : Above lo a := by
  cases lo <;> simp_all [ordered, Above]
private theorem above_trans {lo x y} (h : Above lo x) (hxy : x < y) : Above lo y := by
  cases lo with
  | none => trivial
  | some a => exact lt_trans h hxy

private theorem leftMem {lo} {a : ℚ} {x} (hl : Above lo x) (hr : x < (a : ℝ)) :
    ∀ᶠ y in 𝓝 x, (leftCell lo a).contains y := by
  cases lo with
  | none => exact gt_mem_nhds hr
  | some b => exact inter_mem (lt_mem_nhds (show (b:ℝ) < x from hl)) (gt_mem_nhds hr)

private def Germ (f : Scalar) (a : ℚ) (p q : List ℚ) :=
  coord f =ᶠ[𝓝[<] (a:ℝ)] polyEval p ∧ coord f =ᶠ[𝓝[>] (a:ℝ)] polyEval q

theorem germs {lo hi a f p q} (hl : ordered lo a = true) (hr : orderedRight a hi = true)
    (l : PolynomialOn (leftCell lo a).contains f p) (r : PolynomialOn (rightCell a hi).contains f q) :
    Germ f a p q := by
  have left : ∀ᶠ y in 𝓝[<] (a:ℝ), (leftCell lo a).contains y := by
    cases lo with
    | none => exact self_mem_nhdsWithin
    | some b => exact inter_mem (mem_nhdsWithin_of_mem_nhds (lt_mem_nhds (show (b:ℝ) < a from above_ordered hl))) self_mem_nhdsWithin
  have right : ∀ᶠ y in 𝓝[>] (a:ℝ), (rightCell a hi).contains y := by
    cases hi with
    | none => exact self_mem_nhdsWithin
    | some b =>
      have hab : a < b := of_decide_eq_true hr
      exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (Rat.cast_lt.mpr hab : (a:ℝ) < b)))
  exact ⟨left.mono fun y hy => by simp [coord, l.equation y hy],
         right.mono fun y hy => by simp [coord, r.equation y hy]⟩

private theorem rightClosed {f g : ℝ → ℝ} {a : ℝ}
    (h : f =ᶠ[𝓝[>] a] g) (v : f a = g a) : f =ᶠ[𝓝[≥] a] g := by
  rw [← Ioi_insert, nhdsWithin_insert]
  exact Filter.mem_sup.mpr ⟨v, h⟩

private theorem leftClosed {f g : ℝ → ℝ} {a : ℝ}
    (h : f =ᶠ[𝓝[<] a] g) (v : f a = g a) : f =ᶠ[𝓝[≤] a] g := by
  rw [← Iio_insert, nhdsWithin_insert]
  exact Filter.mem_sup.mpr ⟨v, h⟩

private structure Break (f w : Scalar) (x : ℝ) (d : Option (D ℝ)) : Prop where
  total : f x = some (coord f x)
  weight : w x = some |deriv (coord f) x|
  nonsmooth : ¬ DifferentiableAt ℝ (coord f) x
  traces : ∃ l r, Tendsto (coord f) (𝓝[<] x) (𝓝 l) ∧ Tendsto (coord f) (𝓝[>] x) (𝓝 r) ∧
    (coord f x = l ∨ coord f x = r)
  event : VariationChart.atCut (coord f) x none = d

private theorem traceL {f a p q} (g : Germ f a p q) :
    Tendsto (coord f) (𝓝[<] (a:ℝ)) (𝓝 (polyEval p a)) :=
  ((polyEval_continuous p).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' g.1.symm
private theorem traceR {f a p q} (g : Germ f a p q) :
    Tendsto (coord f) (𝓝[>] (a:ℝ)) (𝓝 (polyEval q a)) :=
  ((polyEval_continuous q).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' g.2.symm

private theorem value_eq {v : ℚ} {p : List ℚ} {a : ℚ} (h : v = polyEvalQ p a) :
    (v : ℝ) = polyEval p a := h ▸ polyEvalQ_cast p a

theorem smooth {f w a p q} {v slope : ℚ} (g : Germ f a p q) (hf : f a = some (v:ℝ))
    (hv : v = polyEvalQ p a) (hr : v = polyEvalQ q a)
    (hd : slope = polyEvalQ (polyDerivative p) a) (he : slope = polyEvalQ (polyDerivative q) a)
    (hw : w a = some ((|slope| : ℚ):ℝ)) : Regular f w a := by
  have hval : coord f a = (v:ℝ) := by simp [coord, hf]
  have eq := (value_eq hv).symm.trans (value_eq hr)
  have de := (value_eq hd).symm.trans (value_eq he)
  let j := fun x : ℝ => if x < (a:ℝ) then polyEval p x else polyEval q x
  have germ : coord f =ᶠ[𝓝 (a:ℝ)] j := by
    rw [← nhdsLT_sup_nhdsGE (a:ℝ)]
    apply Filter.mem_sup.mpr
    constructor
    · filter_upwards [g.1, self_mem_nhdsWithin] with x hx hlt
      exact hx.trans (if_pos (show x < (a:ℝ) from hlt)).symm
    · filter_upwards [rightClosed g.2 (hval.trans (value_eq hr)), self_mem_nhdsWithin] with x hx hge
      exact hx.trans (if_neg (not_lt_of_ge (show (a:ℝ) ≤ x from hge))).symm
  have dj := hasDerivAt_join (polyEval_hasDerivAt p) (polyEval_hasDerivAt q) eq de (a:ℝ)
  have cj := contDiff_join (smoothPoly p) (smoothPoly q) eq (by simpa only [(polyEval_hasDerivAt _ _).deriv] using de)
  refine ⟨hf.trans (congrArg some hval.symm), ?_, cj.contDiffAt.congr_of_eventuallyEq germ⟩
  rw [germ.deriv_eq, show deriv j (a:ℝ) = polyEval (polyDerivative q) a by simpa [j] using dj.deriv, ← value_eq he, ← Rat.cast_abs]
  exact hw

theorem corner {f w a p q} {v : ℚ} (g : Germ f a p q) (hf : f a = some (v:ℝ))
    (hl : v = polyEvalQ p a) (hr : v = polyEvalQ q a)
    (hd : polyEvalQ (polyDerivative p) a ≠ polyEvalQ (polyDerivative q) a)
    (hw : w a = some ((0:ℚ):ℝ)) : Break f w a (VariationChart.corner a (some true)) := by
  have hval : coord f a = (v:ℝ) := by simp [coord, hf]
  have nondiff : ¬ DifferentiableAt ℝ (coord f) (a:ℝ) := by
    intro h
    have l := (polyEval_hasDerivAt p (a:ℝ)).hasDerivWithinAt.congr_of_eventuallyEq
      (leftClosed g.1 (hval.trans (value_eq hl))) (hval.trans (value_eq hl))
    have r := (polyEval_hasDerivAt q (a:ℝ)).hasDerivWithinAt.congr_of_eventuallyEq
      (rightClosed g.2 (hval.trans (value_eq hr))) (hval.trans (value_eq hr))
    have ul := uniqueDiffOn_Iic (a:ℝ) a right_mem_Iic
    have ur := uniqueDiffOn_Ici (a:ℝ) a left_mem_Ici
    apply hd
    apply Rat.cast_injective (α := ℝ)
    rw [polyEvalQ_cast, polyEvalQ_cast, ← l.derivWithin ul, h.hasDerivAt.hasDerivWithinAt.derivWithin ul,
      ← r.derivWithin ur, h.hasDerivAt.hasDerivWithinAt.derivWithin ur]
  exact ⟨hf.trans (congrArg some hval.symm), by simpa [deriv_zero_of_not_differentiableAt nondiff] using hw,
    nondiff, ⟨_, _, traceL g, traceR g, Or.inl (hval.trans (value_eq hl))⟩,
    by simp [VariationChart.atCut_of_limits (traceL g) (traceR g), (value_eq hl).symm.trans (value_eq hr)]⟩

theorem jump {f w a p q} {v l r : ℚ} (g : Germ f a p q) (hf : f a = some (v:ℝ))
    (hl : l = polyEvalQ p a) (hr : r = polyEvalQ q a) (hne : l ≠ r) (endpoint : v = l ∨ v = r)
    (hw : w a = some ((0:ℚ):ℝ)) : Break f w a (VariationChart.atom a (some ((|r-l| : ℚ):ℝ))) := by
  have hval : coord f a = (v:ℝ) := by simp [coord, hf]
  have tl := traceL g; rw [← value_eq hl] at tl
  have tr := traceR g; rw [← value_eq hr] at tr
  have ne : (l:ℝ) ≠ r := by exact_mod_cast hne
  have nondiff : ¬ DifferentiableAt ℝ (coord f) (a:ℝ) := by
    intro h
    have t := h.continuousAt.tendsto
    exact ne ((tendsto_nhds_unique tl (t.mono_left nhdsWithin_le_nhds)).trans
      (tendsto_nhds_unique (t.mono_left nhdsWithin_le_nhds) tr))
  refine ⟨hf.trans (congrArg some hval.symm), by simpa [deriv_zero_of_not_differentiableAt nondiff] using hw,
    nondiff, ⟨_, _, tl, tr, ?_⟩, ?_⟩
  · rcases endpoint with h | h <;> simp [hval, h]
  · simp [VariationChart.atCut_of_limits tl tr, ne]

abbrev Event := ℝ × Option (D ℝ)
structure Checked (f w : Scalar) (lo : Option ℚ) (es : List Event) : Prop where
  sorted : (es.map Prod.fst).Sorted (· < ·)
  inside : ∀ e ∈ es, Above lo e.1
  breaks : ∀ e ∈ es, Break f w e.1 e.2
  regular : ∀ x, Above lo x → x ∉ es.map Prod.fst → Regular f w x

theorem last {a f w p} (h : Cell (Region.after a).contains f w p) : Checked f w (some a) [] :=
  ⟨.nil, by simp, by simp, fun _ hx _ => cellRegular h (lt_mem_nhds hx)⟩

theorem pass {lo a f w es p} (ha : ordered lo a = true)
    (c : Cell (leftCell lo a).contains f w p) (v : Regular f w a) (t : Checked f w (some a) es) :
    Checked f w lo es := by
  refine ⟨t.sorted, fun e h => above_trans (above_ordered ha) (t.inside e h), t.breaks, ?_⟩
  intro x hx hm
  rcases lt_trichotomy x (a:ℝ) with h | rfl | h
  · exact cellRegular c (leftMem hx h)
  · exact v
  · exact t.regular x h hm

theorem cut {lo a f w es p d} (ha : ordered lo a = true)
    (c : Cell (leftCell lo a).contains f w p) (v : Break f w a d) (t : Checked f w (some a) es) :
    Checked f w lo (((a:ℝ), d) :: es) := by
  refine ⟨List.pairwise_cons.mpr ⟨?_, t.sorted⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨e, hm, rfl⟩ := List.mem_map.mp hy
    exact t.inside e hm
  · intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact above_ordered ha
    · exact above_trans (above_ordered ha) (t.inside e h)
  · intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact v
    · exact t.breaks e h
  · intro x hx hn
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rcases lt_or_gt_of_ne hn.1 with h | h
    · exact cellRegular c (leftMem hx h)
    · exact t.regular x h hn.2

private theorem foldEvents {f w : Scalar} (es : List Event)
    (hb : ∀ e ∈ es, Break f w e.1 e.2) (base : Option (D ℝ)) :
    (es.map Prod.fst).foldr (fun a d => addValue (VariationChart.atCut (coord f) a none) d) base =
      es.foldr (fun e d => addValue e.2 d) base := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [(hb e List.mem_cons_self).event, ih (fun _ h => hb _ (List.mem_cons_of_mem _ h))]

theorem finish {f w es} (h : Checked f w none es) :
    value (Tensor.consValue (some f) Tensor.nilValue) =
      es.foldr (fun e d => addValue e.2 d) (weightValue (some w) lebesgueValue) := by
  have exceptional x : x ∈ es.map Prod.fst ↔ ¬ DifferentiableAt ℝ (coord f) x := by
    constructor
    · intro hx; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact (h.breaks e he).nonsmooth
    · contrapose!
      exact fun hx => (h.regular _ trivial hx).smooth.differentiableAt le_rfl
  let chart : VariationChart := ⟨coord f, es.map Prod.fst, h.sorted, exceptional,
    fun _ hx => (h.regular _ trivial hx).smooth, fun _ hx => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx; exact (h.breaks e he).traces⟩
  have eqs x : f x = some (coord f x) ∧ w x = some |deriv (coord f) x| := by
    by_cases hx : x ∈ es.map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact ⟨(h.breaks e he).total, (h.breaks e he).weight⟩
    · exact ⟨(h.regular _ trivial hx).total, (h.regular _ trivial hx).weight⟩
  rw [singleton_pieces chart (fun x => (eqs x).1)]
  change (es.map Prod.fst).foldr _ (weightValue (some fun x => some |deriv (coord f) x|) _) = _
  rw [← funext (fun x => (eqs x).2)]
  exact foldEvents es h.breaks _

private theorem zero_test (x : ℝ) :
    (if x = 0 then some true else some false) = Value.not (Value.nonzero (some x)) := by
  by_cases hx : x = 0 <;> simp [hx, Value.not, Value.nonzero]

theorem cornerTerm (a : ℚ) {v : Option ℝ} (hv : v = some (a:ℝ)) :
    VariationChart.corner a (some true) = realPushforwardOnValue
      (some fun x => Value.not (Value.nonzero (some x)))
      (some fun x : ℝ => Value.add ((some x).map (· ^ 2)) v) := by
  subst v; simp only [VariationChart.corner, funext zero_test]; rfl

theorem cornerBare : VariationChart.corner (0:ℚ) (some true) = realPushforwardOnValue
    (some fun x => Value.not (Value.nonzero (some x))) (some fun x : ℝ => (some x).map (· ^ 2)) := by
  simp [VariationChart.corner, funext zero_test]

theorem cornerSwapped (a : ℚ) {v : Option ℝ} (hv : v = some (a:ℝ)) :
    VariationChart.corner a (some true) = realPushforwardOnValue
      (some fun x => Value.not (Value.nonzero (some x)))
      (some fun x : ℝ => Value.add v ((some x).map (· ^ 2))) := by
  subst v
  simpa [Value.add, add_comm] using (cornerTerm a rfl)

theorem atomTerm (a k : ℚ) {v u : Option ℝ} (hv : v = some (a:ℝ)) (hu : u = some (k:ℝ)) :
    VariationChart.atom a (some (k:ℝ)) =
      if k = 1 then diracValue v else scaleValue u (diracValue v) := by
  subst v; subst u
  have eq : ((k:ℝ) = 1) ↔ k = 1 := by norm_cast
  simp [VariationChart.atom, eq]

theorem moveBreak {f w a d e} (h : Break f w a d) (he : d = e) : Break f w a e := he ▸ h

theorem shifted_pairing (a : ℚ) (swap : Bool) {v : Option ℝ} (hv : v = some (a:ℝ))
    (t : Scalar) (ht : ∀ y, Value.Defined (t y)) :
    massValue (weightValue (some t) (realPushforwardOnValue
      (some fun x => Value.not (Value.nonzero (some x)))
      (some fun x : ℝ => GraphFibre.ordered swap Value.add ((some x).map (· ^ 2)) v))) =
        some ((0:ℤ):ℝ) := by
  subst v
  have e := corner_integral (a:ℝ) t ht
  rw [cornerTerm a rfl] at e
  cases swap <;> simpa [GraphFibre.ordered, Value.add, add_comm] using e

end QSym.Distribution.GraphFibre.Coordinates.Grid

namespace QSym.Distribution.FibreCertificate
open GraphFibre.Coordinates
theorem corner (a : ℚ) {v : Option ℝ} {d : Option (D ℝ)} (hv : v = some (a:ℝ))
    (hd : VariationChart.corner a (some true) = d) (x : Option ℝ) :
    FibreCertificate d x (x.bind (fun _ => some ((0:ℤ):ℝ)))
      (Binding.guardValue (Value.nonzero (Value.add x (Value.mul (some ((-1:ℤ):ℝ)) v))) (some ((0:ℤ):ℝ))) := by
  obtain ⟨c, hc, fibre⟩ := corner_components (a:ℝ)
  rw [← hd, hc, hv]
  cases x with
  | none => rfl
  | some y =>
    obtain ⟨hz, hw⟩ := fibre y
    by_cases h : y = (a:ℝ)
    · subst y; simp [FibreCertificate, hz, hw, Value.nonzero, Value.add, Value.mul, Binding.guardValue]
    · simp [FibreCertificate, hz, hw, Value.nonzero, Value.add, Value.mul, Binding.guardValue,
        ← sub_eq_add_neg, sub_eq_zero, h]
end QSym.Distribution.FibreCertificate
