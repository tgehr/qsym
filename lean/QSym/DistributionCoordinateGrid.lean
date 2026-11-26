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
def coord (f : Scalar) (x : ℝ) := (f x).getD 0

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

theorem polynomialRestricted {f w p} (pred : ℝ → Option Bool) (h : Cell (fun _ => True) f w p) :
    restricted (some pred) (Tensor.consValue (some f) Tensor.nilValue) =
      weightValue (some fun x => Value.mask ((f x).bind pred) (w x)) lebesgueValue := by
  let c := VariationChart.smooth (polyEval p) (smoothPoly p)
  refine (restricted_pieces_eq (singleton_displays c (fun x => h.source.equation x trivial)) pred).trans ?_
  change weightValue (some fun x => Value.mask (pred (polyEval p x)) (some |deriv (polyEval p) x|)) _ = _
  congr 2
  funext x
  rw [h.source.equation x trivial, h.weight x trivial, (polyEval_hasDerivAt p x).deriv]
  rfl

/-- A total smooth coordinate and its signed derivative, both described by
source terms. The derivative stays signed until the outer coordinate rule. -/
def Slope (f d : Scalar) : Prop :=
  ∃ g dg : ℝ → ℝ, ContDiff ℝ 1 g ∧ (∀ x, HasDerivAt g (dg x) x) ∧
    (∀ x, f x = some (g x)) ∧ (∀ x, d x = some (dg x))

namespace Slope

theorem polynomial {f d p q} (hf : PolynomialOn (fun _ => True) f p)
    (hd : PolynomialOn (fun _ => True) d q)
    (he : polyZero (polyAdd q (polyScale (-1) (polyDerivative p))) = true) : Slope f d :=
  ⟨polyEval p, polyEval (polyDerivative p), smoothPoly p, polyEval_hasDerivAt p,
    fun x => hf.equation x trivial,
    fun x => (hd.equation x trivial).trans (congrArg some (samePoly he x))⟩

theorem add {f d g e} (h : Slope f d) (k : Slope g e) :
    Slope (fun x => Value.add (f x) (g x)) (fun x => Value.add (d x) (e x)) := by
  obtain ⟨u, du, cu, hu, fu, fd⟩ := h
  obtain ⟨v, dv, cv, hv, gv, gd⟩ := k
  exact ⟨_, _, cu.add cv, fun x => (hu x).add (hv x),
    fun x => by simp [fu, gv, Value.add], fun x => by simp [fd, gd, Value.add]⟩

theorem mul {f d g e} (h : Slope f d) (k : Slope g e) :
    Slope (fun x => Value.mul (f x) (g x))
      (fun x => Value.add (Value.mul (d x) (g x)) (Value.mul (f x) (e x))) := by
  obtain ⟨u, du, cu, hu, fu, fd⟩ := h
  obtain ⟨v, dv, cv, hv, gv, gd⟩ := k
  exact ⟨_, _, cu.mul cv, fun x => (hu x).mul (hv x),
    fun x => by simp [fu, gv, Value.mul], fun x => by simp [fu, gv, fd, gd, Value.add, Value.mul]⟩

theorem pow {f d} (n : ℕ) (h : Slope f d) :
    Slope (fun x => (f x).map (fun y => y ^ n))
      (fun x => Value.mul (Value.mul (some ((n : ℤ) : ℝ)) ((f x).map (fun y => y ^ (n-1)))) (d x)) := by
  obtain ⟨u, du, cu, hu, fu, fd⟩ := h
  exact ⟨_, _, cu.pow n, fun x => (hu x).pow n, fun x => by simp [fu],
    fun x => by simp [fu, fd, Value.mul]⟩

private theorem chain {f d} (h : Slope f d) (op jac : Option ℝ → Option ℝ)
    (u du : ℝ → ℝ) (cu : ContDiff ℝ 1 u) (hu : ∀ x, HasDerivAt u (du x) x)
    (ev : ∀ z, op (some z) = some (u z)) (ej : ∀ z, jac (some z) = some (du z)) :
    Slope (fun x => op (f x)) (fun x => Value.mul (jac (f x)) (d x)) := by
  obtain ⟨g, dg, cg, hg, eqf, eqd⟩ := h
  exact ⟨u ∘ g, fun x => du (g x) * dg x, cu.comp cg, fun x => (hu _).comp x (hg x),
    fun x => by simp [eqf, ev, Function.comp_def], fun x => by simp [eqf, ej, eqd, Value.mul]⟩

theorem exp {f d} (h : Slope f d) :
    Slope (fun x => Functions.expR.apply (f x)) (fun x => Value.mul (Functions.expR.apply (f x)) (d x)) :=
  chain h Functions.expR.apply Functions.expR.apply Real.exp Real.exp Real.contDiff_exp Real.hasDerivAt_exp
    (fun _ => by simp [Function1.apply, Functions.expR]) (fun _ => by simp [Function1.apply, Functions.expR])

theorem sin {f d} (h : Slope f d) :
    Slope (fun x => Functions.sinR.apply (f x)) (fun x => Value.mul (Functions.cosR.apply (f x)) (d x)) :=
  chain h Functions.sinR.apply Functions.cosR.apply Real.sin Real.cos Real.contDiff_sin Real.hasDerivAt_sin
    (fun _ => by simp [Function1.apply, Functions.sinR]) (fun _ => by simp [Function1.apply, Functions.cosR])

theorem cos {f d} (h : Slope f d) :
    Slope (fun x => Functions.cosR.apply (f x))
      (fun x => Value.mul (Value.mul (some ((-1 : ℤ) : ℝ)) (Functions.sinR.apply (f x))) (d x)) :=
  chain h Functions.cosR.apply (fun v => Value.mul (some ((-1 : ℤ) : ℝ)) (Functions.sinR.apply v))
    Real.cos (fun z => -Real.sin z) Real.contDiff_cos Real.hasDerivAt_cos
    (fun _ => by simp [Function1.apply, Functions.cosR]) (fun z => by simp [Function1.apply, Functions.sinR, Value.mul])

theorem sinh {f d} (h : Slope f d) :
    Slope (fun x => Functions.sinhR.apply (f x)) (fun x => Value.mul (Functions.coshR.apply (f x)) (d x)) :=
  chain h Functions.sinhR.apply Functions.coshR.apply Real.sinh Real.cosh Real.contDiff_sinh Real.hasDerivAt_sinh
    (fun _ => by simp [Function1.apply, Functions.sinhR]) (fun _ => by simp [Function1.apply, Functions.coshR])

theorem cosh {f d} (h : Slope f d) :
    Slope (fun x => Functions.coshR.apply (f x)) (fun x => Value.mul (Functions.sinhR.apply (f x)) (d x)) :=
  chain h Functions.coshR.apply Functions.sinhR.apply Real.cosh Real.sinh Real.contDiff_cosh Real.hasDerivAt_cosh
    (fun _ => by simp [Function1.apply, Functions.coshR]) (fun _ => by simp [Function1.apply, Functions.sinhR])

theorem length {f d} (h : Slope f d) :
    value (Tensor.consValue (some f) Tensor.nilValue) =
      weightValue (some fun x => Value.abs (d x)) lebesgueValue := by
  obtain ⟨g, dg, cg, hg, eqf, eqd⟩ := h
  exact singleton_length cg eqf (fun x => by rw [eqd, (hg x).deriv]; rfl)

theorem restricted {f d} (p : ℝ → Option Bool) (h : Slope f d) :
    Coordinates.restricted (some p) (Tensor.consValue (some f) Tensor.nilValue) =
      weightValue (some fun x => Value.mask ((f x).bind p) (Value.abs (d x))) lebesgueValue := by
  obtain ⟨g, dg, cg, hg, eqf, eqd⟩ := h
  refine (restricted_pieces_eq (singleton_displays (.smooth g cg) eqf) p).trans ?_
  change weightValue (some fun x => Value.mask (p (g x)) (some |deriv g x|)) _ = _
  congr 2
  funext x
  rw [eqf, eqd, (hg x).deriv]
  rfl

end Slope

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

/-- The actual one-sided values need not both occur as source values. -/
theorem traceEndpoints {f a p q} (l r : ℚ) (g : Germ f a p q)
    (hl : l = polyEvalQ p a) (hr : r = polyEvalQ q a) :
    Function.leftLim (coord f) (a:ℝ) = (l:ℝ) ∧ Function.rightLim (coord f) (a:ℝ) = (r:ℝ) :=
  ⟨(leftLim_eq_of_tendsto (NeBot.ne inferInstance) (traceL g)).trans (value_eq hl).symm,
    (rightLim_eq_of_tendsto (NeBot.ne inferInstance) (traceR g)).trans (value_eq hr).symm⟩

/-- Both open germs tend to the actual value at a continuous join. -/
theorem continuousJoin {f a p q} (v : ℚ) (g : Germ f a p q) (hf : f a = some (v:ℝ))
    (hl : v = polyEvalQ p a) (hr : v = polyEvalQ q a) : ContinuousAt (coord f) (a:ℝ) := by
  have hv : coord f a = (v:ℝ) := by simp [coord, hf]
  apply continuousAt_iff_continuous_left'_right'.2
  unfold ContinuousWithinAt
  exact ⟨by rw [hv, value_eq hl]; exact traceL g, by rw [hv, value_eq hr]; exact traceR g⟩

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

def Checked.chart {f w es} (h : Checked f w none es) : VariationChart := by
  have exceptional x : x ∈ es.map Prod.fst ↔ ¬ DifferentiableAt ℝ (coord f) x := by
    constructor
    · intro hx; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact (h.breaks e he).nonsmooth
    · contrapose!
      exact fun hx => (h.regular _ trivial hx).smooth.differentiableAt le_rfl
  exact ⟨coord f, es.map Prod.fst, h.sorted, exceptional,
    fun _ hx => (h.regular _ trivial hx).smooth, fun _ hx => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx; exact (h.breaks e he).traces⟩

theorem Checked.values {f w es} (h : Checked f w none es) (x : ℝ) : f x = some (coord f x) ∧ w x = some |deriv (coord f) x| := by
  by_cases hx : x ∈ es.map Prod.fst
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact ⟨(h.breaks e he).total, (h.breaks e he).weight⟩
  · exact ⟨(h.regular _ trivial hx).total, (h.regular _ trivial hx).weight⟩

theorem Checked.fold_events {f w es} (h : Checked f w none es) (z : Option (D ℝ)) :
    (es.map Prod.fst).foldr (fun a d => addValue (VariationChart.atCut (coord f) a none) d) z =
      es.foldr (fun e d => addValue e.2 d) z := foldEvents es h.breaks z

theorem finish {f w es} (h : Checked f w none es) :
    value (Tensor.consValue (some f) Tensor.nilValue) =
      es.foldr (fun e d => addValue e.2 d) (weightValue (some w) lebesgueValue) := by
  rw [singleton_pieces (h.chart) (fun x => (h.values x).1)]
  change (es.map Prod.fst).foldr _ (weightValue (some fun x => some |deriv (coord f) x|) _) = _
  rw [← funext (fun x => (h.values x).2)]
  exact foldEvents es h.breaks _

/-- The same checked coordinate grid can be used with a restriction on its
source. Each exceptional point supplies its own restricted contribution. -/
def RestrictedEvent (f : Scalar) (pred : ℝ → Option Bool) (e : Event) (d : Option (D ℝ)) :=
  VariationChart.atCut (coord f) e.1 (some pred) = d

theorem finishRestricted {f w es ds} (pred : ℝ → Option Bool) (h : Checked f w none es)
    (events : List.Forall₂ (RestrictedEvent f pred) es ds) :
    restricted (some pred) (Tensor.consValue (some f) Tensor.nilValue) =
      ds.foldr addValue (weightValue (some fun x => Value.mask ((f x).bind pred) (w x)) lebesgueValue) := by
  refine (restricted_pieces_eq (singleton_displays (h.chart) (fun x => (h.values x).1)) pred).trans ?_
  change (es.map Prod.fst).foldr (fun a d => addValue (VariationChart.atCut (coord f) a (some pred)) d)
    (weightValue (some fun x => Value.mask (pred (coord f x)) (some |deriv (coord f) x|)) _) = _
  have eq x : Value.mask (pred (coord f x)) (some |deriv (coord f) x|) =
      Value.mask ((f x).bind pred) (w x) := by rw [(h.values x).1, (h.values x).2]; rfl
  rw [funext eq]
  clear h
  induction events with
  | nil => rfl
  | cons he _ ih => exact congrArg₂ addValue he ih

/-- Clip a jump on its whole closed traversal. Reuse the ordinary mass
certificate for the clipped indicator, including its endpoint probes. -/
theorem restrictedJump {f a p q} (pred : ℝ → Option Bool) (l r k : ℚ)
    (g : Germ f a p q) (hl : l = polyEvalQ p a) (hr : r = polyEvalQ q a) (hne : l ≠ r)
    {lo hi unit : Option ℝ} (hlo : lo = some ((min l r : ℚ):ℝ))
    (hhi : hi = some ((max l r : ℚ):ℝ)) (hu : unit = some ((1:ℚ):ℝ))
    (hm : massValue (weightValue (some fun x => Value.mask
      (Value.and (Value.le lo (some x)) (Value.le (some x) hi)) (Value.mask (pred x) unit))
      lebesgueValue) = some (k:ℝ)) :
    VariationChart.atCut (coord f) a (some pred) = VariationChart.atom a (some (k:ℝ)) := by
  classical
  have tl := traceL g; rw [← value_eq hl] at tl
  have tr := traceR g; rw [← value_eq hr] at tr
  rw [VariationChart.atCut_of_limits tl tr, if_neg (Rat.cast_injective.ne hne)]
  congr 1
  subst lo; subst hi; subst unit
  simp only [Rat.cast_one] at hm
  rw [weighted_lebesgue_mass_bridge, Model.densityMassValue_eq] at hm
  apply Eq.trans _ hm
  let s := uIcc (l:ℝ) (r:ℝ)
  let v := fun x : ℝ => Value.mask (pred x) (some (1:ℝ))
  let clipped := fun x : ℝ => Value.mask
    (Value.and (Value.le (some ((min l r : ℚ):ℝ)) (some x))
      (Value.le (some x) (some ((max l r : ℚ):ℝ)))) (v x)
  have clip (b c x : ℝ) (t : Option ℝ) : Value.mask
      (Value.and (Value.le (some b) (some x)) (Value.le (some x) (some c))) t =
      if b ≤ x ∧ x ≤ c then t else some 0 := by
    by_cases h : b ≤ x <;> by_cases j : x ≤ c <;> simp [Value.and, Value.le, Value.mask, h, j]
  have atPoint x : clipped x = if x ∈ s then v x else some 0 := by
    simp only [clipped, Rat.cast_min, Rat.cast_max, clip]
    by_cases hx : x ∈ s
    · exact (if_pos hx).trans (if_pos hx).symm
    · exact (if_neg hx).trans (if_neg hx).symm
  exact (branchIntegral_congr measurableSet_uIcc (fun x hx => ((atPoint x).trans (if_pos hx)).symm)).trans
    (branchIntegral_eq_full measurableSet_uIcc clipped (fun x hx => (atPoint x).trans (if_neg hx)))

private theorem zero_test (x : ℝ) :
    (if x = 0 then some true else some false) = Value.not (Value.nonzero (some x)) := by
  by_cases hx : x = 0 <;> simp [hx, Value.not, Value.nonzero]

theorem cornerTerm (a : ℚ) {v : Option ℝ} (hv : v = some (a:ℝ)) :
    VariationChart.corner a (some true) = realPushforwardOnValue
      (some fun x => Value.not (Value.nonzero (some x)))
      (some fun x : ℝ => Value.add ((some x).map (· ^ 2)) v) := by
  subst v; simp only [VariationChart.corner, funext zero_test]; rfl

/-- The restriction at a continuous corner sees the common trace. This is
an equality of presentations even if the predicate is undefined there. -/
theorem restrictedCorner {f a p q} (pred : ℝ → Option Bool) (v : ℚ)
    (g : Germ f a p q) (hv : f a = some (v:ℝ))
    (hl : v = polyEvalQ p a) (hr : v = polyEvalQ q a) :
    VariationChart.atCut (coord f) a (some pred) = VariationChart.corner a (pred v) := by
  rw [VariationChart.atCut_of_limits (traceL g) (traceR g),
    if_pos ((value_eq hl).symm.trans (value_eq hr))]
  simp [coord, hv]

theorem cornerGuarded (pred : ℝ → Option Bool) (a v : ℚ) {av vv : Option ℝ}
    (ha : av = some (a:ℝ)) (hv : vv = some (v:ℝ)) :
    VariationChart.corner a (pred v) = realPushforwardOnValue
      (some fun x => Value.and (Value.not (Value.nonzero (some x))) (vv.bind pred))
      (some fun x : ℝ => Value.add ((some x).map (· ^ 2)) av) := by
  subst av; subst vv
  have eq (x : ℝ) : (if x = 0 then pred v else some false) =
      Value.and (Value.not (Value.nonzero (some x))) (pred v) := by
    by_cases hx : x = 0 <;> simp [hx, Value.and, Value.not, Value.nonzero]
  simp only [VariationChart.corner, funext eq]
  rfl

theorem cornerInactive (a : ℝ) {z : Option ℝ} (hz : z = some ((0:ℚ):ℝ)) :
    VariationChart.corner a (some false) = weightValue (some fun _ => z) lebesgueValue := by
  subst z
  let f := fun x : ℝ => x^2 + a
  let d := Presentation.density (fun _ : ℝ => some (0:ℝ)) (fun x => some (f x))
  have hd (y : ℝ) : densityAt d y = some 0 := by
    have e := pushforwardOn_density ∅ f (by dsimp [f]; fun_prop) y
    have empty : y ∉ f '' ∅ := by simp
    simpa [d, densityAtValue, pushforwardOnValue, marginalOn, fibreOn_of_notMem_image empty,
      Value.mask, observe] using e
  have chart : LebesgueChart d (fun _ => some 0) := by
    refine ⟨funext hd, fun _ => ⟨0, rfl⟩, fun t => ?_⟩
    change partialIntegral _ (fun x => some (0 * t (f x))) =
      partialIntegral _ (fun x => some (0 * t x))
    simp
  have off (x : ℝ) : (if x = 0 then some false else some false) = some false := by simp
  simp only [VariationChart.corner, funext off, Rat.cast_zero]
  change some (inLebesgueCoordinates d) = _
  rw [inLebesgueCoordinates_of_chart chart]
  simp [weightValue, lebesgueValue, densityValue, weight, Value.mul]

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
