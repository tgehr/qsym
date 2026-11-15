import QSym.WeightedKernel
import QSym.Integration
import Mathlib.MeasureTheory.Integral.Prod

/-! Scalar and pointwise-density observers for fixed-fibre weighted kernels.
Unsupported density extraction is absence of a chart certificate, not the value
`none`. Scalar `none` means a genuinely nonintegrable real-valued integral.
Weights and return maps in this first fragment are total; signed weights are
allowed, and no measurability structure is required on the result carrier.

Composition is observed using the joint product measure. Replacing a joint
integral by iterated strict integrals is NOT a law of this module.
-/
namespace QSym.WeightedParameter
open MeasureTheory

noncomputable def finiteIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Option ℝ := by
  classical
  exact if Integrable f μ then some (∫ ω, f ω ∂μ) else none

theorem finiteIntegral_eq_partialIntegral {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) :
    finiteIntegral μ f = QSym.partialIntegral μ (fun ω => some (f ω)) := by
  classical
  simp [finiteIntegral, QSym.partialIntegral, QSym.Value.Defined]

theorem finiteIntegral_defined_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) :
    (finiteIntegral μ f).isSome ↔ Integrable f μ := by
  classical
  simp [finiteIntegral]

theorem finiteIntegral_congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℝ} (h : f =ᵐ[μ] g) :
    finiteIntegral μ f = finiteIntegral μ g := by
  classical
  simp only [finiteIntegral]
  rw [integrable_congr h, integral_congr_ae h]

theorem finiteIntegral_comp {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {μ : Measure Ω} {ν : Measure Ψ} (e : Ω ≃ᵐ Ψ)
    (he : MeasurePreserving e μ ν) (f : Ψ → ℝ) :
    finiteIntegral μ (fun ω => f (e ω)) = finiteIntegral ν f := by
  classical
  have hi := he.integrable_comp_emb e.measurableEmbedding (g := f)
  simp only [Function.comp_def] at hi
  simp only [finiteIntegral]
  rw [hi, he.integral_comp' f]

namespace Kernel

noncomputable def integrate {Ω A B : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : Kernel Ω A B) (a : A) (f : B → ℝ) : Option ℝ :=
  finiteIntegral μ (fun ω => p.weight a ω * f (p.value a ω))

theorem integrate_pull {Ω Ψ A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {μ : Measure Ω} {ν : Measure Ψ} (e : Ω ≃ᵐ Ψ)
    (he : MeasurePreserving e μ ν) (p : Kernel Ψ A B) (a : A) (f : B → ℝ) :
    integrate μ (pull e.toEquiv p) a f = integrate ν p a f :=
  finiteIntegral_comp e he (fun ω => p.weight a ω * f (p.value a ω))

theorem integrate_pure {A B : Type*} (f : A → B) (a : A) (g : B → ℝ) :
    integrate (Measure.dirac PUnit.unit) (pure f) a g = some (g (f a)) := by
  simp [integrate, finiteIntegral, pure]

theorem integrate_reweight {Ω A B : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : Kernel Ω A B) (a : A) (g : A → B → ℝ) (f : B → ℝ) :
    integrate μ (reweight g p) a f = integrate μ p a (fun b => g a b * f b) := by
  simp only [integrate, reweight, mul_assoc]

end Kernel

theorem measurePreserving_prodPUnit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] :
    MeasurePreserving (MeasurableEquiv.prodPUnit : Ω × PUnit ≃ᵐ Ω)
      (μ.prod (Measure.dirac PUnit.unit)) μ := by
  refine ⟨measurable_fst, ?_⟩
  change Measure.map Prod.fst (μ.prod (Measure.dirac PUnit.unit)) = μ
  rw [Measure.prod_dirac, Measure.map_map measurable_fst measurable_prodMk_right]
  exact Measure.map_id

theorem measurePreserving_punitProd {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] :
    MeasurePreserving (MeasurableEquiv.punitProd : PUnit × Ω ≃ᵐ Ω)
      ((Measure.dirac PUnit.unit).prod μ) μ := by
  refine ⟨measurable_snd, ?_⟩
  change Measure.map Prod.snd ((Measure.dirac PUnit.unit).prod μ) = μ
  rw [Measure.dirac_prod, Measure.map_map measurable_snd measurable_prodMk_left]
  exact Measure.map_id

namespace Kernel

theorem integrate_comp_pure {Ω A B : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (p : Kernel Ω A B) (a : A) (f : B → ℝ) :
    integrate (μ.prod (Measure.dirac PUnit.unit)) (comp p (pure id)) a f =
      integrate μ p a f := by
  rw [comp_pure]
  exact integrate_pull _ (measurePreserving_prodPUnit μ) p a f

theorem integrate_pure_comp {Ω A B : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (p : Kernel Ω A B) (a : A) (f : B → ℝ) :
    integrate ((Measure.dirac PUnit.unit).prod μ) (comp (pure id) p) a f =
      integrate μ p a f := by
  rw [pure_comp]
  exact integrate_pull _ (measurePreserving_punitProd μ) p a f

theorem integrate_comp_assoc {Ω Ψ Ξ A B C D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ψ) (τ : Measure Ξ) [SFinite ν] [SFinite τ]
    (p : Kernel Ω A B) (q : Kernel Ψ B C) (r : Kernel Ξ C D) (a : A) (f : D → ℝ) :
    integrate ((μ.prod ν).prod τ) (comp (comp p q) r) a f =
      integrate (μ.prod (ν.prod τ)) (comp p (comp q r)) a f := by
  rw [comp_assoc]
  exact integrate_pull _ (MeasureTheory.measurePreserving_prodAssoc μ ν τ) _ a f

/-- A pointwise-weighted real-coordinate trace. Forming it makes no claim that
its scalar integrals exist. -/
def density {A : Type*} (w : A → ℝ → ℝ) : Kernel ℝ A ℝ := ⟨w, fun _ x => x⟩

def lebesgue (A : Type*) : Kernel ℝ A ℝ := density (fun _ _ => 1)

end Kernel

/-- A supported density observation. The coordinate is an exact measurable
bijection preserving the reference measure, and the weight is measurable.
General many-to-one fibres and Jacobian-changing charts are separate extensions.
The certificate selects geometry, not an arbitrary Radon--Nikodym version. -/
structure DensityChart {Ω A : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : Kernel Ω A ℝ) (a : A) where
  coord : Ω ≃ᵐ ℝ
  preserving : MeasurePreserving coord μ volume
  output : ∀ ω, p.value a ω = coord ω
  measurable_weight : Measurable (p.weight a)

namespace DensityChart

def densityAt {Ω A : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : Kernel Ω A ℝ} {a : A} (c : DensityChart μ p a) (x : ℝ) : ℝ :=
  p.weight a (c.coord.symm x)

def identity {A : Type*} (w : A → ℝ → ℝ) (a : A) (hw : Measurable (w a)) :
    DensityChart volume (Kernel.density w) a where
  coord := MeasurableEquiv.refl ℝ
  preserving := MeasurePreserving.id volume
  output := fun _ => rfl
  measurable_weight := hw

@[simp] theorem densityAt_identity {A : Type*} (w : A → ℝ → ℝ) (a : A)
    (hw : Measurable (w a)) (x : ℝ) : densityAt (identity w a hw) x = w a x := rfl

theorem densityAt_unique {Ω A : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : Kernel Ω A ℝ} {a : A} (c d : DensityChart μ p a) (x : ℝ) :
    densityAt c x = densityAt d x := by
  have h : c.coord = d.coord := by
    ext ω
    exact (c.output ω).symm.trans (d.output ω)
  simp [densityAt, h]

def pull {Ω Ψ A : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {μ : Measure Ω} {ν : Measure Ψ} {p : Kernel Ψ A ℝ} {a : A}
    (c : DensityChart ν p a) (e : Ω ≃ᵐ Ψ) (he : MeasurePreserving e μ ν) :
    DensityChart μ (Kernel.pull e.toEquiv p) a where
  coord := e.trans c.coord
  preserving := c.preserving.comp he
  output := fun ω => c.output (e ω)
  measurable_weight := c.measurable_weight.comp e.measurable

theorem densityAt_pull {Ω Ψ A : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {μ : Measure Ω} {ν : Measure Ψ} {p : Kernel Ψ A ℝ} {a : A}
    (c : DensityChart ν p a) (e : Ω ≃ᵐ Ψ) (he : MeasurePreserving e μ ν) (x : ℝ) :
    densityAt (pull c e he) x = densityAt c x := by
  change p.weight a (e (e.symm (c.coord.symm x))) = p.weight a (c.coord.symm x)
  rw [e.apply_symm_apply]

def compPure {Ω A : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {p : Kernel Ω A ℝ} {a : A} (c : DensityChart μ p a) :
    DensityChart (μ.prod (Measure.dirac PUnit.unit)) (Kernel.comp p (Kernel.pure id)) a where
  coord := MeasurableEquiv.prodPUnit.trans c.coord
  preserving := c.preserving.comp (measurePreserving_prodPUnit μ)
  output := fun ω => c.output ω.1
  measurable_weight := by
    simpa [Kernel.comp, Kernel.pure] using c.measurable_weight.comp measurable_fst

theorem densityAt_compPure {Ω A : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {p : Kernel Ω A ℝ} {a : A} (c : DensityChart μ p a) (x : ℝ) :
    densityAt (compPure c) x = densityAt c x := by
  change p.weight a (c.coord.symm x) * 1 = p.weight a (c.coord.symm x)
  exact mul_one _

def reweight {Ω A : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : Kernel Ω A ℝ} {a : A} (c : DensityChart μ p a)
    (g : A → ℝ → ℝ) (hg : Measurable (g a)) :
    DensityChart μ (Kernel.reweight g p) a where
  coord := c.coord
  preserving := c.preserving
  output := c.output
  measurable_weight := by
    apply c.measurable_weight.mul
    simpa only [c.output] using hg.comp c.coord.measurable

theorem densityAt_reweight {Ω A : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : Kernel Ω A ℝ} {a : A} (c : DensityChart μ p a)
    (g : A → ℝ → ℝ) (hg : Measurable (g a)) (x : ℝ) :
    densityAt (reweight c g hg) x = densityAt c x * g a x := by
  change p.weight a (c.coord.symm x) * g a (p.value a (c.coord.symm x)) = _
  rw [c.output, c.coord.apply_symm_apply]
  rfl

theorem integrate_eq {Ω A : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : Kernel Ω A ℝ} {a : A} (c : DensityChart μ p a) (f : ℝ → ℝ) :
    Kernel.integrate μ p a f = finiteIntegral volume (fun x => densityAt c x * f x) := by
  have h := finiteIntegral_comp c.coord c.preserving (fun x => densityAt c x * f x)
  simpa [Kernel.integrate, densityAt, c.output] using h

end DensityChart
end QSym.WeightedParameter
