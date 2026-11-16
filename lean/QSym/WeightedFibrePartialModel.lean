import QSym.WeightedFibrePartial

/-! Partial-body reference-aware weighted families.

This is a conservative extension of `Family`: stored weights and returned values
may be undefined pointwise, rather than merely allowing a partial final test.
The old total model embeds into this one with the same strict observations.
No almost-everywhere quotient, automatic Fubini law, or general disintegration
is introduced.
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory
open scoped ProbabilityTheory

/-- A weighted body with strict pointwise partial weights and values. -/
structure PartialKernel (Ω : Type*) (A : Type*) (B : Type*) where
  weight : A → Ω → Option ℝ
  value : A → Ω → Option B

namespace PartialKernel

/-- Deterministic partial introduction with a trivial latent reference. -/
def pure {A B : Type*} (f : A → Option B) : PartialKernel PUnit A B where
  weight := fun _ _ => some 1
  value := fun a _ => f a

/-- Uniform composition. The intermediate value is strict in both fields. -/
def comp {Ω Ψ A B C : Type*} (p : PartialKernel Ω A B)
    (q : PartialKernel Ψ B C) : PartialKernel (Ω × Ψ) A C where
  weight := fun a ω => (p.value a ω.1).bind fun b =>
    Value.mul (p.weight a ω.1) (q.weight b ω.2)
  value := fun a ω => (p.value a ω.1).bind fun b => q.value b ω.2

/-- Reweighting inspects the stored value and remains strict in every input. -/
def reweight {Ω A B : Type*} (g : A → B → Option ℝ)
    (p : PartialKernel Ω A B) : PartialKernel Ω A B where
  weight := fun a ω => (p.value a ω).bind fun b =>
    Value.mul (p.weight a ω) (g a b)
  value := p.value

/-- The conservative embedding of the existing total weighted body. -/
def ofKernel {Ω A B : Type*} (p : Kernel Ω A B) : PartialKernel Ω A B where
  weight := fun a ω => some (p.weight a ω)
  value := fun a ω => some (p.value a ω)

end PartialKernel

/-- A partial weighted family over one explicitly retained coordinate. -/
structure PartialFamily (X : Type) [MeasurableSpace X] (A B : Type*) where
  space : Space X
  body : X → PartialKernel space.Carrier A B

namespace PartialFamily
variable {X : Type} [MeasurableSpace X] {A B C : Type*}

def pure (f : X → A → Option B) : PartialFamily X A B where
  space := Space.point
  body := fun x => PartialKernel.pure (f x)

def comp (p : PartialFamily X A B) (q : PartialFamily X B C) : PartialFamily X A C where
  space := p.space.prod q.space
  body := fun x => PartialKernel.comp (p.body x) (q.body x)

def reweight (g : X → A → B → Option ℝ) (p : PartialFamily X A B) :
    PartialFamily X A B where
  space := p.space
  body := fun x => PartialKernel.reweight (g x) (p.body x)

/-- Strict scalar observation of a partial body at one retained point. -/
def observe (p : PartialFamily X A B) (x : X) (a : A)
    (f : B → Option ℝ) : Option ℝ :=
  partialIntegral (p.space.reference x) fun ω =>
    Value.mul ((p.body x).weight a ω) (((p.body x).value a ω).bind f)

/-- Strict joint observation with an explicitly supplied outer base measure. -/
def observeJoint (p : PartialFamily X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → Option ℝ) : Option ℝ :=
  partialIntegral (μ ⊗ₘ p.space.reference) fun z =>
    Value.mul ((p.body z.1).weight a z.2)
      (((p.body z.1).value a z.2).bind (f z.1))

/-- The conservative embedding of the existing total family. -/
def ofFamily (p : Family X A B) : PartialFamily X A B where
  space := p.space
  body := fun x => PartialKernel.ofKernel (p.body x)

/-- Pointwise reference-preserving latent isomorphisms for partial bodies. -/
structure Iso (p q : PartialFamily X A B) where
  coordinates : Coordinates X p.space.Carrier q.space.Carrier
  preserving : ∀ x, MeasurePreserving (coordinates.coord x)
    (p.space.reference x) (q.space.reference x)
  weight : ∀ x a ω, (p.body x).weight a ω =
    (q.body x).weight a (coordinates.coord x ω)
  value : ∀ x a ω, (p.body x).value a ω =
    (q.body x).value a (coordinates.coord x ω)

namespace Iso

def refl (p : PartialFamily X A B) : Iso p p where
  coordinates := Coordinates.refl
  preserving := fun _ => MeasurePreserving.id _
  weight := fun _ _ _ => rfl
  value := fun _ _ _ => rfl

def symm {p q : PartialFamily X A B} (h : Iso p q) : Iso q p where
  coordinates := h.coordinates.symm
  preserving := fun x => MeasurePreserving.symm (h.coordinates.coord x) (h.preserving x)
  weight := fun x a ω => by
    simpa using (h.weight x a ((h.coordinates.coord x).symm ω)).symm
  value := fun x a ω => by
    simpa using (h.value x a ((h.coordinates.coord x).symm ω)).symm

def trans {p q r : PartialFamily X A B} (h : Iso p q) (k : Iso q r) : Iso p r where
  coordinates := h.coordinates.trans k.coordinates
  preserving := fun x => (k.preserving x).comp (h.preserving x)
  weight := fun x a ω => (h.weight x a ω).trans (k.weight x a (h.coordinates.coord x ω))
  value := fun x a ω => (h.value x a ω).trans (k.value x a (h.coordinates.coord x ω))

def comp {p p' : PartialFamily X A B} {q q' : PartialFamily X B C}
    (h : Iso p p') (k : Iso q q') : Iso (p.comp q) (p'.comp q') where
  coordinates := h.coordinates.prod k.coordinates
  preserving := fun x => by
    change MeasurePreserving _ ((p.space.reference ×ₖ q.space.reference) x)
      ((p'.space.reference ×ₖ q'.space.reference) x)
    simp only [ProbabilityTheory.Kernel.prod_apply]
    exact (h.preserving x).prod (k.preserving x)
  weight := by
    intro x a ω
    change ((p.body x).value a ω.1).bind (fun b =>
      Value.mul ((p.body x).weight a ω.1) ((q.body x).weight b ω.2)) =
      ((p'.body x).value a (h.coordinates.coord x ω.1)).bind (fun b =>
        Value.mul ((p'.body x).weight a (h.coordinates.coord x ω.1))
          ((q'.body x).weight b (k.coordinates.coord x ω.2)))
    rw [h.weight, h.value]
    cases (p'.body x).value a (h.coordinates.coord x ω.1) with
    | none => rfl
    | some b => simp only [Option.some_bind]; rw [k.weight]
  value := by
    intro x a ω
    change ((p.body x).value a ω.1).bind (fun b => (q.body x).value b ω.2) =
      ((p'.body x).value a (h.coordinates.coord x ω.1)).bind (fun b =>
        (q'.body x).value b (k.coordinates.coord x ω.2))
    rw [h.value]
    cases (p'.body x).value a (h.coordinates.coord x ω.1) with
    | none => rfl
    | some b => simp only [Option.some_bind]; rw [k.value]

def reweight {p q : PartialFamily X A B} (g : X → A → B → Option ℝ)
    (h : Iso p q) : Iso (p.reweight g) (q.reweight g) where
  coordinates := h.coordinates
  preserving := h.preserving
  weight := by
    intro x a ω
    change ((p.body x).value a ω).bind (fun b =>
      Value.mul ((p.body x).weight a ω) (g x a b)) =
      ((q.body x).value a (h.coordinates.coord x ω)).bind (fun b =>
        Value.mul ((q.body x).weight a (h.coordinates.coord x ω)) (g x a b))
    rw [h.weight, h.value]
  value := h.value

/-- Transport an isomorphism of the old total model through the embedding. -/
def ofTotal {p q : Family X A B} (h : Family.Iso p q) :
    Iso (ofFamily p) (ofFamily q) where
  coordinates := h.coordinates
  preserving := h.preserving
  weight := by
    intro x a ω
    change some ((p.body x).weight a ω) =
      some ((q.body x).weight a (h.coordinates.coord x ω))
    rw [h.weight]
  value := by
    intro x a ω
    change some ((p.body x).value a ω) =
      some ((q.body x).value a (h.coordinates.coord x ω))
    rw [h.value]

theorem observe_eq {p q : PartialFamily X A B} (h : Iso p q)
    (x : X) (a : A) (f : B → Option ℝ) : p.observe x a f = q.observe x a f := by
  unfold PartialFamily.observe
  simp_rw [h.weight, h.value]
  exact partialIntegral_comp (h.coordinates.coord x) (h.preserving x)
    (fun ω => Value.mul ((q.body x).weight a ω) (((q.body x).value a ω).bind f))

theorem observeJoint_eq {p q : PartialFamily X A B} (h : Iso p q)
    (μ : Measure X) [SFinite μ] (a : A) (f : X → B → Option ℝ) :
    p.observeJoint μ a f = q.observeJoint μ a f := by
  unfold PartialFamily.observeJoint
  simp_rw [h.weight, h.value]
  exact partialIntegral_comp h.coordinates.joint
    (h.coordinates.preserving_joint h.preserving μ)
    (fun z => Value.mul ((q.body z.1).weight a z.2)
      (((q.body z.1).value a z.2).bind (f z.1)))

end Iso

instance partialFamilySetoid (X : Type) [MeasurableSpace X] (A B : Type*) :
    Setoid (PartialFamily X A B) where
  r p q := Nonempty (Iso p q)
  iseqv := ⟨fun p => ⟨Iso.refl p⟩, fun ⟨h⟩ => ⟨h.symm⟩,
    fun ⟨h⟩ ⟨k⟩ => ⟨h.trans k⟩⟩

end PartialFamily

/-- Partial reference-aware families modulo pointwise fibre isomorphism. -/
def PartialHom (X : Type) [MeasurableSpace X] (A B : Type*) :=
  Quotient (PartialFamily.partialFamilySetoid X A B)

namespace PartialHom
variable {X : Type} [MeasurableSpace X] {A B C : Type*}

def ofFamily (p : PartialFamily X A B) : PartialHom X A B := Quotient.mk _ p

def pure (f : X → A → Option B) : PartialHom X A B :=
  ofFamily (PartialFamily.pure f)

def comp (p : PartialHom X A B) (q : PartialHom X B C) : PartialHom X A C :=
  Quotient.liftOn₂ p q (fun p q => ofFamily (p.comp q)) (by
    intro p q p' q' ⟨h⟩ ⟨k⟩
    exact Quotient.sound ⟨h.comp k⟩)

def reweight (g : X → A → B → Option ℝ) (p : PartialHom X A B) :
    PartialHom X A B :=
  Quotient.liftOn p (fun p => ofFamily (p.reweight g)) (by
    intro p q ⟨h⟩
    exact Quotient.sound ⟨h.reweight g⟩)

def observe (p : PartialHom X A B) (x : X) (a : A)
    (f : B → Option ℝ) : Option ℝ :=
  Quotient.liftOn p (fun p => p.observe x a f) (by
    intro p q ⟨h⟩
    exact h.observe_eq x a f)

def observeJoint (p : PartialHom X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → Option ℝ) : Option ℝ :=
  Quotient.liftOn p (fun p => p.observeJoint μ a f) (by
    intro p q ⟨h⟩
    exact h.observeJoint_eq μ a f)

/-- Conservative embedding of the existing reference-aware quotient. -/
def ofHom (p : Hom X A B) : PartialHom X A B :=
  Quotient.liftOn p (fun p => ofFamily (PartialFamily.ofFamily p)) (by
    intro p q ⟨h⟩
    exact Quotient.sound ⟨PartialFamily.Iso.ofTotal h⟩)

@[simp] theorem observe_pure (f : X → A → Option B)
    (x : X) (a : A) (g : B → Option ℝ) :
    observe (pure f) x a g = (f x a).bind g := by
  change partialIntegral (Measure.dirac PUnit.unit)
    (fun _ : PUnit => Value.mul (some 1) ((f x a).bind g)) = _
  rw [partialIntegral_point, Value.mul_one_left]

theorem observe_reweight (p : PartialHom X A B)
    (g : X → A → B → Option ℝ) (x : X) (a : A) (f : B → Option ℝ) :
    observe (reweight g p) x a f =
      observe p x a (fun b => Value.mul (g x a b) (f b)) := by
  induction p using Quotient.inductionOn with | _ p =>
    change partialIntegral (p.space.reference x) (fun ω =>
      Value.mul (((p.body x).value a ω).bind (fun b =>
        Value.mul ((p.body x).weight a ω) (g x a b)))
        (((p.body x).value a ω).bind f)) =
      partialIntegral (p.space.reference x) (fun ω =>
        Value.mul ((p.body x).weight a ω)
          (((p.body x).value a ω).bind (fun b => Value.mul (g x a b) (f b))))
    congr 1
    funext ω
    cases hw : (p.body x).weight a ω with
    | none =>
      cases hv : (p.body x).value a ω <;>
        simp [hw, hv, Value.mul]
    | some w =>
      cases hv : (p.body x).value a ω with
      | none => simp [hw, hv, Value.mul]
      | some b =>
        cases hg : g x a b <;> cases hf : f b <;>
          simp [hw, hv, hg, hf, Value.mul, mul_assoc]

@[simp] theorem ofHom_pure (f : X → A → B) :
    ofHom (Hom.pure f) = pure (fun x a => some (f x a)) := rfl

theorem ofHom_comp (p : Hom X A B) (q : Hom X B C) :
    ofHom (Hom.comp p q) = comp (ofHom p) (ofHom q) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q => rfl

theorem ofHom_reweight (p : Hom X A B) (g : X → A → B → ℝ) :
    ofHom (Hom.reweight g p) = reweight (fun x a b => some (g x a b)) (ofHom p) := by
  induction p using Quotient.inductionOn with | _ p => rfl

theorem ofHom_observePartial (p : Hom X A B) (x : X) (a : A)
    (f : B → Option ℝ) :
    observe (ofHom p) x a f = Hom.observePartial p x a f := by
  induction p using Quotient.inductionOn with | _ p => rfl

theorem ofHom_observeJointPartial (p : Hom X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → Option ℝ) :
    observeJoint (ofHom p) μ a f = Hom.observeJointPartial p μ a f := by
  induction p using Quotient.inductionOn with | _ p => rfl

end PartialHom

/-- A partial pointwise family of traces with arbitrary returned values. -/
abbrev PartialTrace (X : Type) [MeasurableSpace X] (B : Type*) :=
  PartialHom X PUnit B

end QSym.WeightedParameter.Fibre
