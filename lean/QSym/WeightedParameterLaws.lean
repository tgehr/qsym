import QSym.WeightedParameter
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Abstract observer laws and their closed weighted-parameter implementation.
An abstract theorem is conditional until applied to `parameterTheory` (or a
different verified implementation). No global axioms are introduced.
-/
namespace QSym.WeightedParameter
open MeasureTheory Set

theorem finiteIntegral_interval (a b c : ℝ) (hab : a ≤ b) :
    finiteIntegral volume (fun x => if a ≤ x ∧ x ≤ b then c else 0) =
      some (c * (b - a)) := by
  let f : ℝ → ℝ := (Icc a b).indicator (fun _ => c)
  have hi : Integrable f volume := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const.mpr (Or.inr (by simp [Real.volume_Icc]))
  have hf : (fun x => if a ≤ x ∧ x ≤ b then c else 0) = f := by
    funext x
    simp [f, Set.indicator, Set.mem_Icc]
  rw [hf]
  simp only [finiteIntegral, if_pos hi]
  congr 1
  simp [f, integral_indicator_const, Real.volume_real_Icc_of_le hab, mul_comm]

/-- This is a deliberately small law set, not a claim that all `sym` laws have
already been axiomatized or implemented. `Chart` records supported geometry;
its choice cannot affect the returned pointwise density. -/
structure ParameterTheory extends KernelTheory where
  scalarIntegral : (ℝ → ℝ) → Option ℝ
  scalarIntegral_congr_ae : ∀ {f g : ℝ → ℝ}, f =ᵐ[volume] g →
    scalarIntegral f = scalarIntegral g
  scalarIntegral_interval : ∀ a b c : ℝ, a ≤ b →
    scalarIntegral (fun x => if a ≤ x ∧ x ≤ b then c else 0) = some (c * (b - a))
  density : {A : Type} → (A → ℝ → ℝ) → K ℝ A ℝ
  observe : {Ω A B : Type} → [MeasurableSpace Ω] →
    Measure Ω → K Ω A B → A → (B → ℝ) → Option ℝ
  observe_pure : ∀ {A B} (f : A → B) (a : A) (g : B → ℝ),
    observe (Measure.dirac PUnit.unit) (pure f) a g = some (g (f a))
  observe_reweight : ∀ {Ω A B} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : K Ω A B) (a : A) (g : A → B → ℝ) (f : B → ℝ),
    observe μ (reweight g p) a f = observe μ p a (fun b => g a b * f b)
  observe_pull : ∀ {Ω Ψ A B} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {μ : Measure Ω} {ν : Measure Ψ} (e : Ω ≃ᵐ Ψ), MeasurePreserving e μ ν →
    ∀ (p : K Ψ A B) (a : A) (f : B → ℝ),
      observe μ (pull e.toEquiv p) a f = observe ν p a f
  observe_density : ∀ {A} (w : A → ℝ → ℝ) (a : A) (f : ℝ → ℝ),
    observe volume (density w) a f = scalarIntegral (fun x => w a x * f x)
  Chart : {Ω A : Type} → [MeasurableSpace Ω] → Measure Ω → K Ω A ℝ → A → Type
  densityAt : {Ω A : Type} → [MeasurableSpace Ω] → {μ : Measure Ω} →
    {p : K Ω A ℝ} → {a : A} → Chart μ p a → ℝ → ℝ
  densityAt_unique : ∀ {Ω A} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : K Ω A ℝ} {a : A} (c d : Chart μ p a) (x : ℝ), densityAt c x = densityAt d x
  densityChart : ∀ {A} (w : A → ℝ → ℝ) (a : A), Measurable (w a) →
    Chart volume (density w) a
  densityAt_density : ∀ {A} (w : A → ℝ → ℝ) (a : A) (hw : Measurable (w a)) (x : ℝ),
    densityAt (densityChart w a hw) x = w a x
  chartPull : ∀ {Ω Ψ A} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {μ : Measure Ω} {ν : Measure Ψ} {p : K Ψ A ℝ} {a : A},
    Chart ν p a → (e : Ω ≃ᵐ Ψ) → MeasurePreserving e μ ν → Chart μ (pull e.toEquiv p) a
  densityAt_pull : ∀ {Ω Ψ A} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {μ : Measure Ω} {ν : Measure Ψ} {p : K Ψ A ℝ} {a : A}
    (c : Chart ν p a) (e : Ω ≃ᵐ Ψ) (he : MeasurePreserving e μ ν) (x : ℝ),
    densityAt (chartPull c e he) x = densityAt c x
  chartCompPure : ∀ {Ω A} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {p : K Ω A ℝ} {a : A}, Chart μ p a →
      Chart (μ.prod (Measure.dirac PUnit.unit)) (comp p (pure id)) a
  densityAt_comp_pure : ∀ {Ω A} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {p : K Ω A ℝ} {a : A} (c : Chart μ p a) (x : ℝ),
      densityAt (chartCompPure c) x = densityAt c x
  chartReweight : ∀ {Ω A} [MeasurableSpace Ω] {μ : Measure Ω} {p : K Ω A ℝ} {a : A},
    Chart μ p a → (g : A → ℝ → ℝ) → Measurable (g a) → Chart μ (reweight g p) a
  densityAt_reweight : ∀ {Ω A} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : K Ω A ℝ} {a : A} (c : Chart μ p a) (g : A → ℝ → ℝ) (hg : Measurable (g a)) (x : ℝ),
    densityAt (chartReweight c g hg) x = densityAt c x * g a x
  observe_chart : ∀ {Ω A} [MeasurableSpace Ω] {μ : Measure Ω} {p : K Ω A ℝ} {a : A}
    (c : Chart μ p a) (f : ℝ → ℝ),
    observe μ p a f = scalarIntegral (fun x => densityAt c x * f x)

noncomputable def parameterTheory : ParameterTheory where
  toKernelTheory := kernelTheory
  scalarIntegral := finiteIntegral volume
  scalarIntegral_congr_ae := finiteIntegral_congr_ae
  scalarIntegral_interval := finiteIntegral_interval
  density := Kernel.density
  observe := Kernel.integrate
  observe_pure := Kernel.integrate_pure
  observe_reweight := Kernel.integrate_reweight
  observe_pull := Kernel.integrate_pull
  observe_density := fun _ _ _ => rfl
  Chart := DensityChart
  densityAt := DensityChart.densityAt
  densityAt_unique := DensityChart.densityAt_unique
  densityChart := DensityChart.identity
  densityAt_density := DensityChart.densityAt_identity
  chartPull := DensityChart.pull
  densityAt_pull := DensityChart.densityAt_pull
  chartCompPure := DensityChart.compPure
  densityAt_comp_pure := DensityChart.densityAt_compPure
  chartReweight := DensityChart.reweight
  densityAt_reweight := DensityChart.densityAt_reweight
  observe_chart := DensityChart.integrate_eq

namespace ParameterTheory

/-- The scalar right-unit rule is derived from structural composition and
parameter invariance, rather than added as another primitive law. -/
theorem observe_comp_pure (T : ParameterTheory) {Ω A B : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (p : T.K Ω A B) (a : A) (f : B → ℝ) :
    T.observe (μ.prod (Measure.dirac PUnit.unit)) (T.comp p (T.pure id)) a f =
      T.observe μ p a f := by
  rw [T.comp_pure]
  exact T.observe_pull _ (measurePreserving_prodPUnit μ) p a f

theorem observe_comp_assoc (T : ParameterTheory) {Ω Ψ Ξ A B C D : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ψ) (τ : Measure Ξ) [SFinite ν] [SFinite τ]
    (p : T.K Ω A B) (q : T.K Ψ B C) (r : T.K Ξ C D) (a : A) (f : D → ℝ) :
    T.observe ((μ.prod ν).prod τ) (T.comp (T.comp p q) r) a f =
      T.observe (μ.prod (ν.prod τ)) (T.comp p (T.comp q r)) a f := by
  rw [T.comp_assoc]
  exact T.observe_pull _ (MeasureTheory.measurePreserving_prodAssoc μ ν τ) _ a f

/-- An interval simplification using only the abstract interface. -/
theorem mass_interval (T : ParameterTheory) (a b c : ℝ) (hab : a ≤ b) :
    T.observe volume (T.density (fun _ : PUnit =>
      fun x => if a ≤ x ∧ x ≤ b then c else 0)) PUnit.unit (fun _ => 1) =
      some (c * (b - a)) := by
  rw [T.observe_density]
  simpa using T.scalarIntegral_interval a b c hab

/-- Almost-everywhere equality is used only under the scalar observer. -/
theorem mass_density_congr_ae (T : ParameterTheory) {w v : ℝ → ℝ}
    (h : w =ᵐ[volume] v) :
    T.observe volume (T.density (fun _ : PUnit => w)) PUnit.unit (fun _ => 1) =
      T.observe volume (T.density (fun _ : PUnit => v)) PUnit.unit (fun _ => 1) := by
  rw [T.observe_density, T.observe_density]
  simpa using T.scalarIntegral_congr_ae h

end ParameterTheory
end QSym.WeightedParameter
