import QSym.Limit
import QSym.Binding
import QSym.Numeric

/-! Limits under continuous operations: builtins that are defined and
continuous everywhere, absolute values, partial builtins at a limit in the
interior of their domain, and reciprocals of limits that are not zero.
Strict guards that are eventually decided let the limit of their value
through. -/
namespace QSym.Limit
open Filter Topology

section Maps
variable {α : Type} [TopologicalSpace α]

/-- A continuous map of the values keeps the limit. -/
theorem Exact.map {β : Type} [TopologicalSpace β] {l : Filter ℝ} {f : ℝ → Option α}
    {a : Option α} (φ : α → β) (hφ : Continuous φ) (hf : Exact l f a) :
    Exact l (fun x => (f x).map φ) (a.map φ) := by
  cases a with
  | none => exact hf.mono fun x hx => by simp [hx]
  | some a =>
    obtain ⟨u, hu, ht⟩ := hf
    exact ⟨fun x => φ (u x), hu.mono fun x hx => by simp [hx], (hφ.tendsto a).comp ht⟩

/-- A builtin that is defined and continuous everywhere. -/
def Regular {β : Type} [TopologicalSpace β] (F : Function1 α β) : Prop :=
  (∀ v, F.domain v) ∧ Continuous F.value

theorem Exact.regular {β : Type} [TopologicalSpace β] {l : Filter ℝ} {F : Function1 α β}
    {f : ℝ → Option α} {a : Option α} (hF : Regular F) (hf : Exact l f a) :
    Exact l (fun x => F.apply (f x)) (F.apply a) := by
  have h : ∀ o : Option α, F.apply o = o.map F.value := by
    intro o
    cases o with
    | none => rfl
    | some v => simp [Function1.apply, hF.1 v]
  simp only [h]
  exact hf.map F.value hF.2

end Maps

/-- A strict guard that is eventually decided: where it holds the value keeps
its limit, and otherwise nothing is defined. -/
theorem Exact.guard {α : Type} [TopologicalSpace α] {l : Filter ℝ} {p : ℝ → Option Bool}
    {g : Option Bool} {f : ℝ → Option α} {out : Option α} (hp : Eventual l p g)
    (hf : Exact l f out) :
    Exact l (fun x => Binding.guardValue (p x) (f x)) (Binding.guardValue g out) := by
  have hm : ∀ᶠ x in l, Binding.guardValue (p x) (f x) = Binding.guardValue g (f x) :=
    hp.mono fun x hx => by rw [hx]
  by_cases hg : g = some true
  · subst hg
    exact hf.congr hm
  · have hn : ∀ v : Option α, Binding.guardValue g v = none := by
      intro v
      unfold Binding.guardValue
      rw [if_neg]
      simpa using hg
    rw [hn]
    exact hm.mono fun x hx => hx.trans (hn _)

theorem Exact.abs {l : Filter ℝ} {f : ℝ → Option ℝ} {a : Option ℝ} (hf : Exact l f a) :
    Exact l (fun x => Value.abs (f x)) (Value.abs a) :=
  hf.map (fun v => |v|) continuous_abs

theorem regular_castQR : Regular Functions.castQR := ⟨fun _ => trivial, Rat.continuous_coe_real⟩
theorem regular_castRC : Regular Functions.castRC := ⟨fun _ => trivial, Complex.continuous_ofReal⟩
theorem regular_expR : Regular Functions.expR := ⟨fun _ => trivial, Real.continuous_exp⟩
theorem regular_sinR : Regular Functions.sinR := ⟨fun _ => trivial, Real.continuous_sin⟩
theorem regular_cosR : Regular Functions.cosR := ⟨fun _ => trivial, Real.continuous_cos⟩
theorem regular_sinhR : Regular Functions.sinhR := ⟨fun _ => trivial, Real.continuous_sinh⟩
theorem regular_coshR : Regular Functions.coshR := ⟨fun _ => trivial, Real.continuous_cosh⟩
theorem regular_tanhR : Regular Functions.tanhR :=
  ⟨fun _ => trivial, by
    have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
    show Continuous Real.tanh
    rw [h]
    exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'⟩
theorem regular_atanR : Regular Functions.atanR := ⟨fun _ => trivial, Real.continuous_arctan⟩
theorem regular_asinhR : Regular Functions.asinhR := ⟨fun _ => trivial, Real.continuous_arsinh⟩
theorem regular_exp2R : Regular Functions.exp2R :=
  ⟨fun _ => trivial, Real.continuous_const_rpow (by norm_num)⟩
theorem regular_expC : Regular Functions.expC := ⟨fun _ => trivial, Complex.continuous_exp⟩
theorem regular_sinC : Regular Functions.sinC := ⟨fun _ => trivial, Complex.continuous_sin⟩
theorem regular_cosC : Regular Functions.cosC := ⟨fun _ => trivial, Complex.continuous_cos⟩
theorem regular_sinhC : Regular Functions.sinhC := ⟨fun _ => trivial, Complex.continuous_sinh⟩
theorem regular_coshC : Regular Functions.coshC := ⟨fun _ => trivial, Complex.continuous_cosh⟩
theorem regular_reC : Regular Functions.reC := ⟨fun _ => trivial, Complex.continuous_re⟩
theorem regular_imC : Regular Functions.imC := ⟨fun _ => trivial, Complex.continuous_im⟩
theorem regular_absC : Regular Functions.absC := ⟨fun _ => trivial, continuous_norm⟩
theorem regular_cisR : Regular Functions.cisR :=
  ⟨fun _ => trivial, Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)⟩
theorem regular_expiC : Regular Functions.expiC :=
  ⟨fun _ => trivial, Complex.continuous_exp.comp (continuous_const.mul continuous_id)⟩

/-- A partial builtin is defined near this value and continuous there. -/
def Interior (F : Function1 ℝ ℝ) (v : ℝ) : Prop :=
  (∀ᶠ y in 𝓝 v, F.domain y) ∧ ContinuousAt F.value v

/-- A partial builtin keeps a limit in the interior of its domain. -/
theorem Exact.interior {l : Filter ℝ} {F : Function1 ℝ ℝ} {f : ℝ → Option ℝ} {a : Option ℝ}
    (hf : Exact l f a) (q : ℚ) (ha : a = some (Numeric.denote (s := .real) q))
    (hF : Interior F (q : ℝ)) : Exact l (fun x => F.apply (f x)) (F.apply a) := by
  have hq : a = some (q : ℝ) := by rw [ha]; simp [Numeric.denote]
  subst hq
  obtain ⟨u, hu, ht⟩ := hf
  have hd : F.apply (some (q : ℝ)) = some (F.value q) := by
    simp [Function1.apply, hF.1.self_of_nhds]
  rw [hd]
  refine ⟨fun x => F.value (u x), (hu.and (ht.eventually hF.1)).mono fun x hx => ?_,
    hF.2.tendsto.comp ht⟩
  show F.apply (f x) = some (F.value (u x))
  rw [hx.1]
  simp [Function1.apply, hx.2]

private theorem positive {q : ℚ} (hq : decide (0 < q) = true) : (0 : ℝ) < q := by
  exact_mod_cast of_decide_eq_true hq

theorem interior_logR {q : ℚ} (hq : decide (0 < q) = true) : Interior Functions.logR q :=
  ⟨lt_mem_nhds (positive hq), Real.continuousAt_log (positive hq).ne'⟩

theorem interior_log2R {q : ℚ} (hq : decide (0 < q) = true) : Interior Functions.log2R q :=
  ⟨lt_mem_nhds (positive hq), (Real.continuousAt_log (positive hq).ne').div_const _⟩

theorem interior_log10R {q : ℚ} (hq : decide (0 < q) = true) : Interior Functions.log10R q :=
  ⟨lt_mem_nhds (positive hq), (Real.continuousAt_log (positive hq).ne').div_const _⟩

theorem interior_sqrtR {q : ℚ} (hq : decide (0 < q) = true) : Interior Functions.sqrtR q :=
  ⟨(lt_mem_nhds (positive hq)).mono fun _ h => le_of_lt h, Real.continuous_sqrt.continuousAt⟩

private theorem unit {q : ℚ} (hq : decide (-1 < q ∧ q < 1) = true) :
    ∀ᶠ y : ℝ in 𝓝 (q : ℝ), -1 ≤ y ∧ y ≤ 1 := by
  have h := of_decide_eq_true hq
  have h1 : (-1 : ℝ) < q := by exact_mod_cast h.1
  have h2 : (q : ℝ) < 1 := by exact_mod_cast h.2
  exact ((lt_mem_nhds h1).and (gt_mem_nhds h2)).mono fun _ hy => ⟨hy.1.le, hy.2.le⟩

theorem interior_asinR {q : ℚ} (hq : decide (-1 < q ∧ q < 1) = true) :
    Interior Functions.asinR q :=
  ⟨unit hq, Real.continuous_arcsin.continuousAt⟩

theorem interior_acosR {q : ℚ} (hq : decide (-1 < q ∧ q < 1) = true) :
    Interior Functions.acosR q :=
  ⟨unit hq, Real.continuous_arccos.continuousAt⟩

/-- The reciprocal keeps a limit that is not zero. Nothing is said of a limit
that is zero: the reciprocal may then diverge, or be undefined arbitrarily
far out. -/
theorem Exact.inv {l : Filter ℝ} {f : ℝ → Option ℝ} {a : Option ℝ} (hf : Exact l f a)
    (ha : a ≠ some 0) : Exact l (fun x => Value.inv (f x)) (Value.inv a) := by
  cases a with
  | none => exact hf.mono fun x hx => by simp [hx, Value.inv]
  | some v =>
    have hv : v ≠ 0 := fun h => ha (by rw [h])
    obtain ⟨u, hu, ht⟩ := hf
    have hne : ∀ᶠ x in l, u x ≠ 0 := ht.eventually_ne hv
    have hi : Value.inv (some v) = some v⁻¹ := by simp [Value.inv, hv]
    rw [hi]
    exact ⟨fun x => (u x)⁻¹, (hu.and hne).mono fun x hx => by simp [hx.1, Value.inv, hx.2],
      ht.inv₀ hv⟩

theorem nonzero_literal {a : Option ℝ} (q : ℚ) (h : a = some (Numeric.denote (s := .real) q))
    (hq : decide (q ≠ 0) = true) : a ≠ some 0 := by
  rw [h]
  have hq' : q ≠ 0 := of_decide_eq_true hq
  simp [Numeric.denote, hq']

end QSym.Limit
