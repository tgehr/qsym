import QSym.WeightedFibrePartial

/-! A model-backed law boundary for distribution simplification.

This interface covers uniform composition and partial observations at a retained
coordinate. It deliberately has no unconditional Fubini, arbitrary bind, or
mass-of-scale field. The existing presentation interpreter is not an instance
of a full distribution theory; the observation bridges are separate theorems.
-/
noncomputable section
namespace QSym.Distribution
open MeasureTheory
open scoped ProbabilityTheory
open WeightedParameter.Fibre

structure ObservationTheory (X : Type) where
  K : Type → Type → Type 1
  pure : {A B : Type} → (X → A → B) → K A B
  comp : {A B C : Type} → K A B → K B C → K A C
  reweight : {A B : Type} → (X → A → B → ℝ) → K A B → K A B
  observe : {A B : Type} → K A B → X → A → (B → Option ℝ) → Option ℝ
  comp_pure : ∀ {A B} (p : K A B), comp p (pure (fun _ => id)) = p
  pure_comp : ∀ {A B} (p : K A B), comp (pure (fun _ => id)) p = p
  comp_assoc : ∀ {A B C D} (p : K A B) (q : K B C) (r : K C D),
    comp (comp p q) r = comp p (comp q r)
  observe_pure : ∀ {A B} (f : X → A → B) x a g, observe (pure f) x a g = g (f x a)
  observe_reweight : ∀ {A B} (p : K A B) g x a f,
    observe (reweight g p) x a f = observe p x a (fun b => Value.mul (some (g x a b)) (f b))
  reweight_one : ∀ {A B} (p : K A B), reweight (fun _ _ _ => 1) p = p
  reweight_mul : ∀ {A B} (p : K A B) g h,
    reweight g (reweight h p) = reweight (fun x a b => h x a b * g x a b) p

def fibreObservationTheory (X : Type) [MeasurableSpace X] : ObservationTheory X where
  K := Hom X
  pure := Hom.pure
  comp := Hom.comp
  reweight := Hom.reweight
  observe := Hom.observePartial
  comp_pure := Hom.comp_pure
  pure_comp := Hom.pure_comp
  comp_assoc := Hom.comp_assoc
  observe_pure := Hom.observePartial_pure
  observe_reweight := Hom.observePartial_reweight
  reweight_one := Hom.reweight_one
  reweight_mul := Hom.reweight_mul

namespace Model

/-- Test an atom through the reference-aware model, including partial source
arguments. The type of the atom may be a function, type code, or distribution. -/
def atomTestValue {A : Type} (f : Option (A → Option ℝ)) (a : Option A) : Option ℝ :=
  f.bind (fun g => a.bind (fun b =>
    (fibreObservationTheory PUnit).observe
      ((fibreObservationTheory PUnit).pure (fun _ _ : PUnit => b)) PUnit.unit PUnit.unit g))

theorem atomTestValue_eq {A : Type} (f : Option (A → Option ℝ)) (a : Option A) :
    atomTestValue f a = f.bind (fun g => a.bind g) := by
  cases f <;> cases a <;> simp [atomTestValue, ObservationTheory.observe_pure]

/-- A density query is observation of the explicitly retained real coordinate.
The possibly partial density is a test; it is not silently made total. -/
def densityTestValue (f : Option (ℝ → Option ℝ)) (x : Option ℝ) : Option ℝ :=
  f.bind (fun g => x.bind (fun y =>
    (fibreObservationTheory ℝ).observe
      ((fibreObservationTheory ℝ).pure (fun (z : ℝ) (_ : PUnit) => z)) y PUnit.unit g))

theorem densityTestValue_eq (f : Option (ℝ → Option ℝ)) (x : Option ℝ) :
    densityTestValue f x = f.bind (fun g => x.bind g) := by
  cases f <;> cases x <;> simp [densityTestValue, ObservationTheory.observe_pure]

/-- Joint scalar observation of the same retained-coordinate family. -/
def densityMassValue (f : Option (ℝ → Option ℝ)) : Option ℝ :=
  f.bind (fun g => Hom.observeJointPartial
    (Hom.pure (fun x : ℝ => fun _ : PUnit.{1} => x)) volume PUnit.unit (fun _ x => g x))

theorem densityMassValue_eq (f : Option (ℝ → Option ℝ)) :
    densityMassValue f = f.bind (partialIntegral volume) := by
  cases f with
  | none => rfl
  | some f =>
    change partialIntegral (volume ⊗ₘ ProbabilityTheory.Kernel.const ℝ (Measure.dirac PUnit.unit))
      (fun z : ℝ × PUnit => Value.mul (some 1) (f z.1)) = partialIntegral volume f
    simp only [Value.mul_one_left, Measure.compProd_const]
    exact partialIntegral_comp MeasurableEquiv.prodPUnit
      (WeightedParameter.measurePreserving_prodPUnit volume) f

end Model
end QSym.Distribution
