import QSym.WeightedFibreTransport

/-! Reference-aware weighted families over a fixed retained coordinate `X`.

The quotient identifies only jointly measurable, pointwise reference-preserving
latent reparametrizations. Both pointwise fibre observations and joint scalar
observations descend to it. Signed integrals retain their original L1 domain.

Composition is uniform in the arbitrary input/output value types, which need
no measurable structure. The latent reference may depend measurably on `X`,
but not on a previous sampled value. This is a category of such families, not
yet a general distribution monad or a model of arbitrary disintegration. In
particular, choosing/altering the retained projection is additional geometry:
this quotient must not erase data needed for a subsequent conditioning query.
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory
open scoped ProbabilityTheory

structure Space (X : Type*) [MeasurableSpace X] where
  Carrier : Type
  [measurable : MeasurableSpace Carrier]
  reference : ProbabilityTheory.Kernel X Carrier
  [sfinite : ProbabilityTheory.IsSFiniteKernel reference]

attribute [instance] Space.measurable Space.sfinite

namespace Space
variable {X : Type*} [MeasurableSpace X]

def point : Space X where
  Carrier := PUnit
  reference := ProbabilityTheory.Kernel.const X (Measure.dirac PUnit.unit)

def ofMeasure (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] : Space X where
  Carrier := Ω
  reference := ProbabilityTheory.Kernel.const X μ

def prod (p q : Space X) : Space X where
  Carrier := p.Carrier × q.Carrier
  reference := p.reference ×ₖ q.reference

end Space

structure Family (X : Type*) [MeasurableSpace X] (A B : Type*) where
  space : Space X
  body : X → Kernel space.Carrier A B

namespace Family
variable {X : Type*} [MeasurableSpace X] {A B C D : Type*}

def pure (f : X → A → B) : Family X A B :=
  ⟨Space.point, fun x => Kernel.pure (f x)⟩

def comp (p : Family X A B) (q : Family X B C) : Family X A C :=
  ⟨p.space.prod q.space, fun x => Kernel.comp (p.body x) (q.body x)⟩

def reweight (g : X → A → B → ℝ) (p : Family X A B) : Family X A B :=
  ⟨p.space, fun x => Kernel.reweight (g x) (p.body x)⟩

def observe (p : Family X A B) (x : X) (a : A) (f : B → ℝ) : Option ℝ :=
  Kernel.integrate (p.space.reference x) (p.body x) a f

def observeJoint (p : Family X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → ℝ) : Option ℝ :=
  finiteIntegral (μ ⊗ₘ p.space.reference)
    (fun z => (p.body z.1).weight a z.2 * f z.1 ((p.body z.1).value a z.2))

structure Iso (p q : Family X A B) where
  coordinates : Coordinates X p.space.Carrier q.space.Carrier
  preserving : ∀ x, MeasurePreserving (coordinates.coord x)
    (p.space.reference x) (q.space.reference x)
  weight : ∀ x a ω, (p.body x).weight a ω = (q.body x).weight a (coordinates.coord x ω)
  value : ∀ x a ω, (p.body x).value a ω = (q.body x).value a (coordinates.coord x ω)

namespace Iso
variable {p q r : Family X A B}

def refl (p : Family X A B) : Iso p p where
  coordinates := Coordinates.refl
  preserving := fun _ => MeasurePreserving.id _
  weight := fun _ _ _ => rfl
  value := fun _ _ _ => rfl

def symm (h : Iso p q) : Iso q p where
  coordinates := h.coordinates.symm
  preserving := fun x => MeasurePreserving.symm (h.coordinates.coord x) (h.preserving x)
  weight := fun x a ω => by simpa using (h.weight x a ((h.coordinates.coord x).symm ω)).symm
  value := fun x a ω => by simpa using (h.value x a ((h.coordinates.coord x).symm ω)).symm

def trans (h : Iso p q) (k : Iso q r) : Iso p r where
  coordinates := h.coordinates.trans k.coordinates
  preserving := fun x => (k.preserving x).comp (h.preserving x)
  weight := fun x a ω => (h.weight x a ω).trans (k.weight x a (h.coordinates.coord x ω))
  value := fun x a ω => (h.value x a ω).trans (k.value x a (h.coordinates.coord x ω))

def comp {p p' : Family X A B} {q q' : Family X B C}
    (h : Iso p p') (k : Iso q q') : Iso (p.comp q) (p'.comp q') where
  coordinates := h.coordinates.prod k.coordinates
  preserving := fun x => by
    change MeasurePreserving _ ((p.space.reference ×ₖ q.space.reference) x)
      ((p'.space.reference ×ₖ q'.space.reference) x)
    simp only [ProbabilityTheory.Kernel.prod_apply]
    exact (h.preserving x).prod (k.preserving x)
  weight := by
    intro x a ω
    change (p.body x).weight a ω.1 * (q.body x).weight ((p.body x).value a ω.1) ω.2 =
      (p'.body x).weight a (h.coordinates.coord x ω.1) *
        (q'.body x).weight ((p'.body x).value a (h.coordinates.coord x ω.1)) (k.coordinates.coord x ω.2)
    rw [h.weight, h.value, k.weight]
  value := by
    intro x a ω
    change (q.body x).value ((p.body x).value a ω.1) ω.2 =
      (q'.body x).value ((p'.body x).value a (h.coordinates.coord x ω.1)) (k.coordinates.coord x ω.2)
    rw [h.value, k.value]

def reweight (h : Iso p q) (g : X → A → B → ℝ) : Iso (p.reweight g) (q.reweight g) where
  coordinates := h.coordinates
  preserving := h.preserving
  weight := by
    intro x a ω
    change (p.body x).weight a ω * g x a ((p.body x).value a ω) =
      (q.body x).weight a (h.coordinates.coord x ω) * g x a ((q.body x).value a (h.coordinates.coord x ω))
    rw [h.weight, h.value]
  value := h.value

theorem observe_eq (h : Iso p q) (x : X) (a : A) (f : B → ℝ) :
    p.observe x a f = q.observe x a f := by
  have hb : p.body x = Kernel.pull (h.coordinates.coord x).toEquiv (q.body x) :=
    Kernel.ext (h.weight x) (h.value x)
  simp only [observe, hb]
  exact Kernel.integrate_pull _ (h.preserving x) _ a f

theorem observeJoint_eq (h : Iso p q) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → ℝ) : p.observeJoint μ a f = q.observeJoint μ a f := by
  unfold observeJoint
  simp_rw [h.weight, h.value]
  exact finiteIntegral_comp h.coordinates.joint
    (h.coordinates.preserving_joint h.preserving μ)
    (fun z => (q.body z.1).weight a z.2 * f z.1 ((q.body z.1).value a z.2))

end Iso

def compPureIso (p : Family X A B) : Iso (p.comp (pure (fun _ => id))) p where
  coordinates := Coordinates.const MeasurableEquiv.prodPUnit
  preserving := fun x => by
    change MeasurePreserving _ ((p.space.reference ×ₖ Space.point.reference) x) _
    rw [ProbabilityTheory.Kernel.prod_apply]
    exact measurePreserving_prodPUnit (p.space.reference x)
  weight := by intro x a ω; simp [comp, pure, Kernel.comp, Kernel.pure]; rfl
  value := fun _ _ _ => rfl

def pureCompIso (p : Family X A B) : Iso ((pure (fun _ => id)).comp p) p where
  coordinates := Coordinates.const MeasurableEquiv.punitProd
  preserving := fun x => by
    change MeasurePreserving _ ((Space.point.reference ×ₖ p.space.reference) x) _
    rw [ProbabilityTheory.Kernel.prod_apply]
    exact measurePreserving_punitProd (p.space.reference x)
  weight := by intro x a ω; simp [comp, pure, Kernel.comp, Kernel.pure]; rfl
  value := fun _ _ _ => rfl

def compAssocIso (p : Family X A B) (q : Family X B C) (r : Family X C D) :
    Iso ((p.comp q).comp r) (p.comp (q.comp r)) where
  coordinates := Coordinates.const MeasurableEquiv.prodAssoc
  preserving := fun x => by
    change MeasurePreserving _ (((p.space.reference ×ₖ q.space.reference) ×ₖ r.space.reference) x)
      ((p.space.reference ×ₖ (q.space.reference ×ₖ r.space.reference)) x)
    simp only [ProbabilityTheory.Kernel.prod_apply]
    exact measurePreserving_prodAssoc _ _ _
  weight := by intro x a ω; simp [comp, Kernel.comp, mul_assoc]; rfl
  value := fun _ _ _ => rfl

/-- Pull back the weight and value together with the reference. Changing the
weight alone is not a valid reparametrization. -/
def pull {Y : Type} [MeasurableSpace Y] (p : Family X A B)
    (e : Coordinates X Y p.space.Carrier) : Family X A B where
  space := ⟨Y, e.symm.transport p.space.reference⟩
  body := fun x => Kernel.pull (e.coord x).toEquiv (p.body x)

def pullIso {Y : Type} [MeasurableSpace Y] (p : Family X A B)
    (e : Coordinates X Y p.space.Carrier) : Iso (p.pull e) p where
  coordinates := e
  preserving := fun x => by
    exact MeasurePreserving.symm (e.coord x).symm (e.symm.preserving_transport p.space.reference x)
  weight := fun _ _ _ => rfl
  value := fun _ _ _ => rfl

instance familySetoid (X : Type*) [MeasurableSpace X] (A B : Type*) : Setoid (Family X A B) where
  r p q := Nonempty (Iso p q)
  iseqv := ⟨fun p => ⟨Iso.refl p⟩, fun ⟨h⟩ => ⟨h.symm⟩, fun ⟨h⟩ ⟨k⟩ => ⟨h.trans k⟩⟩

end Family

def Hom (X : Type*) [MeasurableSpace X] (A B : Type*) := Quotient (Family.familySetoid X A B)

namespace Hom
variable {X : Type*} [MeasurableSpace X] {A B C D : Type*}

def ofFamily (p : Family X A B) : Hom X A B := Quotient.mk _ p

def pure (f : X → A → B) : Hom X A B := ofFamily (Family.pure f)

def comp (p : Hom X A B) (q : Hom X B C) : Hom X A C :=
  Quotient.liftOn₂ p q (fun p q => ofFamily (p.comp q)) (by
    intro p q p' q' ⟨h⟩ ⟨k⟩
    exact Quotient.sound ⟨h.comp k⟩)

theorem comp_pure (p : Hom X A B) : comp p (pure (fun _ => id)) = p := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound ⟨p.compPureIso⟩

theorem pure_comp (p : Hom X A B) : comp (pure (fun _ => id)) p = p := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound ⟨p.pureCompIso⟩

theorem comp_assoc (p : Hom X A B) (q : Hom X B C) (r : Hom X C D) :
    comp (comp p q) r = comp p (comp q r) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      induction r using Quotient.inductionOn with | _ r =>
        exact Quotient.sound ⟨Family.compAssocIso p q r⟩

def reweight (g : X → A → B → ℝ) (p : Hom X A B) : Hom X A B :=
  Quotient.liftOn p (fun p => ofFamily (p.reweight g)) (by
    intro p q ⟨h⟩; exact Quotient.sound ⟨h.reweight g⟩)

def observe (p : Hom X A B) (x : X) (a : A) (f : B → ℝ) : Option ℝ :=
  Quotient.liftOn p (fun p => p.observe x a f) (by
    intro p q ⟨h⟩; exact h.observe_eq x a f)

def observeJoint (p : Hom X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → ℝ) : Option ℝ :=
  Quotient.liftOn p (fun p => p.observeJoint μ a f) (by
    intro p q ⟨h⟩; exact h.observeJoint_eq μ a f)

theorem observe_pure (f : X → A → B) (x : X) (a : A) (g : B → ℝ) :
    observe (pure f) x a g = some (g (f x a)) :=
  Kernel.integrate_pure (f x) a g

theorem observe_reweight (p : Hom X A B) (g : X → A → B → ℝ)
    (x : X) (a : A) (f : B → ℝ) :
    observe (reweight g p) x a f = observe p x a (fun b => g x a b * f b) := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Kernel.integrate_reweight _ _ a _ f

theorem reweight_one (p : Hom X A B) : reweight (fun _ _ _ => 1) p = p := by
  induction p using Quotient.inductionOn with | _ p =>
    change ofFamily ⟨p.space, fun x => Kernel.reweight (fun _ _ => 1) (p.body x)⟩ = ofFamily p
    simp only [Kernel.reweight_one]

theorem reweight_mul (p : Hom X A B) (g h : X → A → B → ℝ) :
    reweight g (reweight h p) = reweight (fun x a b => h x a b * g x a b) p := by
  induction p using Quotient.inductionOn with | _ p =>
    change ofFamily ⟨p.space, fun x => Kernel.reweight (g x) (Kernel.reweight (h x) (p.body x))⟩ = _
    simp only [Kernel.reweight_mul]
    rfl

theorem ofFamily_pull {Y : Type} [MeasurableSpace Y] (p : Family X A B)
    (e : Coordinates X Y p.space.Carrier) : ofFamily (p.pull e) = ofFamily p :=
  Quotient.sound ⟨p.pullIso e⟩

end Hom

/-- A pointwise family of traces with arbitrary (possibly higher order) results. -/
abbrev Trace (X : Type*) [MeasurableSpace X] (B : Type*) := Hom X PUnit B

end QSym.WeightedParameter.Fibre
