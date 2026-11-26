import QSym.LimitExponential
import QSym.LimitContinuous
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Finite limits of scalar observations whose argument tends to positive or negative infinity. -/
noncomputable section
namespace QSym.Limit
open Filter Topology Distribution.StepSource

/-- An eventually defined source tends to one of the two infinite ends.
This is intermediate evidence for limits with finite scalar results. -/
def Escapes (l : Filter ℝ) (neg : Bool) (f : ℝ → Option ℝ) : Prop :=
  ∃ g : ℝ → ℝ, (∀ᶠ x in l, f x = some (g x)) ∧ Tendsto g l (if neg then atBot else atTop)

namespace Escapes

theorem polynomial {f p} (bottom neg : Bool) (b : ℕ) (h : PolynomialOn (fun _ => True) f p)
    (hd : descends (!bottom) (if neg then p else polyScale (-1) p) b = true) :
    Escapes (if bottom then atBot else atTop) neg f := by
  refine ⟨polyEval p, Eventually.of_forall (fun x => h.equation x trivial), ?_⟩
  cases neg with
  | true =>
    cases bottom
    · exact descends_atTop hd
    · exact descends_atBot hd
  | false =>
    have ht : Tendsto (polyEval (polyScale (-1) p)) (if bottom then atBot else atTop) atBot := by
      cases bottom
      · exact descends_atTop hd
      · exact descends_atBot hd
    refine (tendsto_neg_atBot_atTop.comp ht).congr fun x => ?_
    simp [Function.comp_apply, polyEval_scale]

theorem exp {l f} (h : Escapes l false f) : Escapes l false (fun x => Functions.expR.apply (f x)) := by
  obtain ⟨g, he, ht⟩ := h
  exact ⟨Real.exp ∘ g, he.mono (fun x hx => by simp [hx, Function.comp_apply, Functions.expR, Function1.apply]),
    Real.tendsto_exp_atTop.comp ht⟩

theorem add {l neg f} (c : Option ℝ) {v : ℝ} (hc : c = some v) (right : Bool) (h : Escapes l neg f) :
    Escapes l neg (fun x => if right then Value.add (f x) c else Value.add c (f x)) := by
  obtain ⟨g, he, ht⟩ := h
  refine ⟨fun x => g x + v, he.mono (fun x hx => by cases right <;> simp [hx, hc, Value.add, add_comm]), ?_⟩
  cases neg
  · exact ht.atTop_add tendsto_const_nhds
  · exact ht.atBot_add tendsto_const_nhds

theorem addBoth {l neg f g} (hf : Escapes l neg f) (hg : Escapes l neg g) :
    Escapes l neg (fun x => Value.add (f x) (g x)) := by
  obtain ⟨u, eu, tu⟩ := hf
  obtain ⟨v, ev, tv⟩ := hg
  refine ⟨fun x => u x + v x, ?_, ?_⟩
  · filter_upwards [eu, ev] with x hu hv
    simp [hu, hv, Value.add]
  · cases neg
    · exact tu.atTop_add_atTop tv
    · exact tu.atBot_add_atBot tv

theorem scale {l neg f c} (q : ℚ) (hq : q ≠ 0) (hc : c = some (Numeric.denote (s := .real) q))
    (right : Bool) (h : Escapes l neg f) :
    Escapes l (if q < 0 then !neg else neg) (fun x => if right then Value.mul (f x) c else Value.mul c (f x)) := by
  obtain ⟨g, he, ht⟩ := h
  refine ⟨fun x => (q : ℝ)*g x, he.mono (fun x hx => by cases right <;> simp [hc, hx, Numeric.denote, Value.mul, mul_comm]), ?_⟩
  by_cases hs : q < 0
  · have hr : (q : ℝ) < 0 := by exact_mod_cast hs
    simp only [if_pos hs]
    cases neg
    · exact ht.const_mul_atTop_of_neg hr
    · exact ht.const_mul_atBot_of_neg hr
  · have hr : (0 : ℝ) < q := by exact_mod_cast lt_of_le_of_ne (le_of_not_gt hs) hq.symm
    simp only [if_neg hs]
    cases neg
    · exact ht.const_mul_atTop hr
    · exact ht.const_mul_atBot hr

theorem inv {l neg f} (h : Escapes l neg f) {z : Option ℝ}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    Exact l (fun x => Value.inv (f x)) z := by
  obtain ⟨g, he, ht⟩ := h
  have hv : z = some (0 : ℝ) := by simpa [Numeric.denote] using hz
  rw [hv]
  refine ⟨fun x => (g x)⁻¹, ?_, ?_⟩
  · have hn : ∀ᶠ x in l, g x ≠ 0 := by
      cases neg
      · exact (ht.eventually (eventually_gt_atTop 0)).mono fun _ hx => ne_of_gt hx
      · exact (ht.eventually (eventually_lt_atBot 0)).mono fun _ hx => ne_of_lt hx
    filter_upwards [he, hn] with x hx hn
    simp [Value.inv, hx, hn]
  · cases neg
    · exact tendsto_inv_atTop_zero.comp ht
    · exact tendsto_inv_atBot_zero.comp ht

theorem arctan {l neg f} (h : Escapes l neg f) {factor pi : Option ℝ}
    (hv : factor = some (Numeric.denote (s := .real) (if neg then -1/2 else 1/2)))
    (hp : pi = some Functions.pi) :
    Exact l (fun x => Functions.atanR.apply (f x)) (Value.mul factor pi) := by
  obtain ⟨g, he, ht⟩ := h
  have ev : ∀ᶠ x in l, Functions.atanR.apply (f x) = some (Real.arctan (g x)) :=
    he.mono fun x hx => by simp [hx, Functions.atanR, Function1.apply]
  rw [hv, hp]
  cases neg
  · refine ⟨fun x => Real.arctan (g x), ev, ?_⟩
    convert Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp ht using 1
    all_goals norm_num [Numeric.denote, Functions.pi]
    all_goals ring
  · refine ⟨fun x => Real.arctan (g x), ev, ?_⟩
    convert Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds |>.comp ht using 1
    all_goals norm_num [Numeric.denote, Functions.pi]
    all_goals ring

private theorem tanh_one : Tendsto Real.tanh atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => (Real.exp (-x))^2) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.pow 2
  have num := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  have den := (tendsto_const_nhds (x := (1 : ℝ))).add h
  have ht := num.div den (by norm_num)
  have eq (x : ℝ) : Real.tanh x = (1 - (Real.exp (-x))^2) / (1 + (Real.exp (-x))^2) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
    have hp := Real.exp_pos x
    field_simp
    ring
  have hlim : Tendsto (fun x : ℝ => (1 - (Real.exp (-x))^2) / (1 + (Real.exp (-x))^2)) atTop (𝓝 1) := by
    simpa using ht
  exact hlim.congr fun x => (eq x).symm

theorem tanh {l neg f} (h : Escapes l neg f) {v : Option ℝ}
    (hv : v = some (Numeric.denote (s := .real) (if neg then -1 else 1))) :
    Exact l (fun x => Functions.tanhR.apply (f x)) v := by
  obtain ⟨g, he, ht⟩ := h
  have ev : ∀ᶠ x in l, Functions.tanhR.apply (f x) = some (Real.tanh (g x)) :=
    he.mono fun x hx => by simp [hx, Functions.tanhR, Function1.apply]
  rw [hv]
  cases neg
  · exact ⟨_, ev, by simpa [Numeric.denote, Function.comp_def] using tanh_one.comp ht⟩
  · have hb := (tanh_one.comp tendsto_neg_atBot_atTop).neg
    exact ⟨_, ev, by simpa [Numeric.denote, Function.comp_def, Real.tanh_neg] using hb.comp ht⟩

end Escapes
end QSym.Limit
