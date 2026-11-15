import QSym.WeightedFibreReindex
import QSym.IntegrationLaws

/-! Strict partial observations on the reference-aware quotient.

An undefined test at even one parameter point remains undefined. We use the
same pointwise-definedness convention as the current source interpreter, not
an almost-everywhere or undefined-as-zero convention. Return maps and stored
weights are still total; partial tests do not yet implement general partial
sampling kernels. The scalar and pointwise observers both descend to `Hom`.
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory
open scoped ProbabilityTheory

namespace Family
variable {X : Type} [MeasurableSpace X] {A B : Type*}

def observePartial (p : Family X A B) (x : X) (a : A) (f : B → Option ℝ) : Option ℝ :=
  partialIntegral (p.space.reference x)
    (fun ω => Value.mul (some ((p.body x).weight a ω)) (f ((p.body x).value a ω)))

def observeJointPartial (p : Family X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → Option ℝ) : Option ℝ :=
  partialIntegral (μ ⊗ₘ p.space.reference)
    (fun z => Value.mul (some ((p.body z.1).weight a z.2)) (f z.1 ((p.body z.1).value a z.2)))

theorem Iso.observePartial_eq {p q : Family X A B} (h : Iso p q)
    (x : X) (a : A) (f : B → Option ℝ) : p.observePartial x a f = q.observePartial x a f := by
  unfold observePartial
  simp_rw [h.weight, h.value]
  exact partialIntegral_comp (h.coordinates.coord x) (h.preserving x)
    (fun ω => Value.mul (some ((q.body x).weight a ω)) (f ((q.body x).value a ω)))

theorem Iso.observeJointPartial_eq {p q : Family X A B} (h : Iso p q)
    (μ : Measure X) [SFinite μ] (a : A) (f : X → B → Option ℝ) :
    p.observeJointPartial μ a f = q.observeJointPartial μ a f := by
  unfold observeJointPartial
  simp_rw [h.weight, h.value]
  exact partialIntegral_comp h.coordinates.joint
    (h.coordinates.preserving_joint h.preserving μ)
    (fun z => Value.mul (some ((q.body z.1).weight a z.2)) (f z.1 ((q.body z.1).value a z.2)))

end Family

namespace Hom
variable {X : Type} [MeasurableSpace X] {A B : Type*}

def observePartial (p : Hom X A B) (x : X) (a : A) (f : B → Option ℝ) : Option ℝ :=
  Quotient.liftOn p (fun p => p.observePartial x a f) (by
    intro p q ⟨h⟩; exact h.observePartial_eq x a f)

def observeJointPartial (p : Hom X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → Option ℝ) : Option ℝ :=
  Quotient.liftOn p (fun p => p.observeJointPartial μ a f) (by
    intro p q ⟨h⟩; exact h.observeJointPartial_eq μ a f)

theorem observePartial_some (p : Hom X A B) (x : X) (a : A) (f : B → ℝ) :
    observePartial p x a (fun b => some (f b)) = observe p x a f := by
  induction p using Quotient.inductionOn with | _ p =>
    exact (finiteIntegral_eq_partialIntegral _ _).symm

theorem observeJointPartial_some (p : Hom X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → ℝ) :
    observeJointPartial p μ a (fun x b => some (f x b)) = observeJoint p μ a f := by
  induction p using Quotient.inductionOn with | _ p =>
    exact (finiteIntegral_eq_partialIntegral _ _).symm

theorem observePartial_pure (f : X → A → B) (x : X) (a : A) (g : B → Option ℝ) :
    observePartial (pure f) x a g = g (f x a) := by
  change partialIntegral (Measure.dirac PUnit.unit)
    (fun _ : PUnit => Value.mul (some 1) (g (f x a))) = _
  rw [partialIntegral_point, Value.mul_one_left]

theorem observePartial_reweight (p : Hom X A B) (g : X → A → B → ℝ)
    (x : X) (a : A) (f : B → Option ℝ) :
    observePartial (reweight g p) x a f =
      observePartial p x a (fun b => Value.mul (some (g x a b)) (f b)) := by
  induction p using Quotient.inductionOn with | _ p =>
    change partialIntegral _ _ = partialIntegral _ _
    congr 1
    funext ω
    change Value.mul (some ((p.body x).weight a ω * g x a ((p.body x).value a ω)))
        (f ((p.body x).value a ω)) =
      Value.mul (some ((p.body x).weight a ω))
        (Value.mul (some (g x a ((p.body x).value a ω))) (f ((p.body x).value a ω)))
    cases f ((p.body x).value a ω) <;> simp [Value.mul, mul_assoc]

theorem observePartial_reindex {X' : Type} [MeasurableSpace X'] (p : Hom X A B)
    (f : X' → X) (hf : Measurable f) (x : X') (a : A) (g : B → Option ℝ) :
    observePartial (reindex p f hf) x a g = observePartial p (f x) a g := by
  induction p using Quotient.inductionOn with | _ p => rfl

end Hom
end QSym.WeightedParameter.Fibre
