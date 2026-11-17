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

namespace Space

/-- Disjoint latent sum, with each reference pushed into its corresponding branch. -/
def sum {X : Type*} [MeasurableSpace X] (p q : Space X) : Space X where
  Carrier := p.Carrier ⊕ q.Carrier
  reference := p.reference.map Sum.inl + q.reference.map Sum.inr

end Space

namespace Coordinates
variable {X Y Z Y' Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace Y'] [MeasurableSpace Z']

/-- Branchwise transport over a disjoint latent sum. -/
def sum (e : Coordinates X Y Z) (f : Coordinates X Y' Z') :
    Coordinates X (Y ⊕ Y') (Z ⊕ Z') where
  coord := fun x => (e.coord x).sumCongr (f.coord x)
  forward := by
    have h := (measurable_inl.comp e.forward).sumElim (measurable_inr.comp f.forward)
    convert h.comp (MeasurableEquiv.prodSumDistrib X Y Y').measurable using 1
    ext p
    rcases p with ⟨x, y | y'⟩ <;> rfl
  backward := by
    have h := (measurable_inl.comp e.backward).sumElim (measurable_inr.comp f.backward)
    convert h.comp (MeasurableEquiv.prodSumDistrib X Z Z').measurable using 1
    ext p
    rcases p with ⟨x, z | z'⟩ <;> rfl

end Coordinates

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

/-- Disjoint sum of partial bodies; neither branch is hidden by the other. -/
def sum {Ω Ψ A B : Type*} (p : PartialKernel Ω A B)
    (q : PartialKernel Ψ A B) : PartialKernel (Ω ⊕ Ψ) A B where
  weight := fun a z => match z with
    | Sum.inl ω => p.weight a ω
    | Sum.inr ψ => q.weight a ψ
  value := fun a z => match z with
    | Sum.inl ω => p.value a ω
    | Sum.inr ψ => q.value a ψ

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

/-- Direct sum of two families over the same retained coordinate. -/
def sum (p q : PartialFamily X A B) : PartialFamily X A B where
  space := p.space.sum q.space
  body := fun x => PartialKernel.sum (p.body x) (q.body x)

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

/-- A disjoint sum observes as the strict sum of its two fibre observations. -/
theorem observe_sum (p q : PartialFamily X A B) (x : X) (a : A) (f : B → Option ℝ) :
    (p.sum q).observe x a f = Value.add (p.observe x a f) (q.observe x a f) := by
  unfold PartialFamily.observe PartialFamily.sum Space.sum PartialKernel.sum
  dsimp only
  simp only [ProbabilityTheory.Kernel.add_apply,
    ProbabilityTheory.Kernel.map_apply _ measurable_inl,
    ProbabilityTheory.Kernel.map_apply _ measurable_inr]
  convert partialIntegral_sum (p.space.reference x) (q.space.reference x)
    (fun ω => Value.mul ((p.body x).weight a ω) (((p.body x).value a ω).bind f))
    (fun ψ => Value.mul ((q.body x).weight a ψ) (((q.body x).value a ψ).bind f)) using 1
  congr 1
  funext z
  cases z <;> rfl

private theorem compProd_map {Ω Ψ : Type} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure X) [SFinite μ] (κ : ProbabilityTheory.Kernel X Ω)
    [ProbabilityTheory.IsSFiniteKernel κ] (g : Ω → Ψ) (hg : Measurable g) :
    μ ⊗ₘ κ.map g = (μ ⊗ₘ κ).map (fun z => (z.1, g z.2)) := by
  have hF : Measurable (fun z : X × Ω => (z.1, g z.2)) :=
    measurable_fst.prodMk (hg.comp measurable_snd)
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hF hs,
    Measure.compProd_apply (hF hs)]
  apply lintegral_congr
  intro x
  rw [ProbabilityTheory.Kernel.map_apply' κ hg x (measurable_prodMk_left hs)]
  rfl

/-- Rooted observation over a sum of reference kernels splits by branch. -/
private theorem partialIntegral_compProd_sum {Ω Ψ : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ψ] (μ : Measure X) [SFinite μ]
    (κ : ProbabilityTheory.Kernel X Ω) [ProbabilityTheory.IsSFiniteKernel κ]
    (η : ProbabilityTheory.Kernel X Ψ) [ProbabilityTheory.IsSFiniteKernel η]
    (f : X × Ω → Option ℝ) (g : X × Ψ → Option ℝ) :
    partialIntegral (μ ⊗ₘ (κ.map Sum.inl + η.map Sum.inr))
      (fun z : X × (Ω ⊕ Ψ) =>
        Sum.elim (fun ω => f (z.1, ω)) (fun ψ => g (z.1, ψ)) z.2) =
      Value.add (partialIntegral (α := X × Ω) (E := ℝ) (μ ⊗ₘ κ) f)
        (partialIntegral (α := X × Ψ) (E := ℝ) (μ ⊗ₘ η) g) := by
  let e := MeasurableEquiv.prodSumDistrib X Ω Ψ
  let M := μ ⊗ₘ (κ.map Sum.inl + η.map Sum.inr)
  let N := (μ ⊗ₘ κ).map Sum.inl + (μ ⊗ₘ η).map Sum.inr
  have hinl : Measurable (fun z : X × Ω => (z.1, @Sum.inl Ω Ψ z.2)) :=
    measurable_fst.prodMk (measurable_inl.comp measurable_snd)
  have hinr : Measurable (fun z : X × Ψ => (z.1, @Sum.inr Ω Ψ z.2)) :=
    measurable_fst.prodMk (measurable_inr.comp measurable_snd)
  have hmeasure : M.map e = N := by
    dsimp only [M, N]
    rw [Measure.compProd_add_right, Measure.map_add _ _ e.measurable,
      compProd_map μ κ Sum.inl measurable_inl, compProd_map μ η Sum.inr measurable_inr,
      Measure.map_map e.measurable hinl, Measure.map_map e.measurable hinr]
    rfl
  have he : MeasurePreserving e M N := ⟨e.measurable, hmeasure⟩
  calc
    partialIntegral M (fun z => Sum.elim (fun ω => f (z.1, ω))
        (fun ψ => g (z.1, ψ)) z.2) =
        partialIntegral M (fun z => Sum.elim f g (e z)) := by
      congr 1
      funext z
      rcases z with ⟨x, ω | ψ⟩ <;> rfl
    _ = partialIntegral N (Sum.elim f g) := partialIntegral_comp e he _
    _ = Value.add (partialIntegral (μ ⊗ₘ κ) f) (partialIntegral (μ ⊗ₘ η) g) := by
      dsimp only [N]
      exact partialIntegral_sum (μ ⊗ₘ κ) (μ ⊗ₘ η) f g

/-- Joint observation of a direct sum is strict addition of the branch observations. -/
theorem observeJoint_sum (p q : PartialFamily X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → Option ℝ) :
    (p.sum q).observeJoint μ a f = Value.add (p.observeJoint μ a f) (q.observeJoint μ a f) := by
  unfold PartialFamily.observeJoint PartialFamily.sum Space.sum PartialKernel.sum
  dsimp only
  convert partialIntegral_compProd_sum μ p.space.reference q.space.reference
    (fun z => Value.mul ((p.body z.1).weight a z.2)
      (((p.body z.1).value a z.2).bind (f z.1)))
    (fun z => Value.mul ((q.body z.1).weight a z.2)
      (((q.body z.1).value a z.2).bind (f z.1))) using 1
  congr 1
  funext z
  rcases z with ⟨x, ω | ψ⟩ <;> rfl

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

/-- Branchwise isomorphisms induce an isomorphism of disjoint sums. -/
def sum {p p' q q' : PartialFamily X A B}
    (h : Iso p p') (k : Iso q q') : Iso (p.sum q) (p'.sum q') where
  coordinates := h.coordinates.sum k.coordinates
  preserving := by
    intro x
    let e := (h.coordinates.coord x).sumCongr (k.coordinates.coord x)
    dsimp only [PartialFamily.sum, Space.sum, Coordinates.sum]
    simp only [ProbabilityTheory.Kernel.add_apply,
      ProbabilityTheory.Kernel.map_apply _ measurable_inl,
      ProbabilityTheory.Kernel.map_apply _ measurable_inr]
    change MeasurePreserving e
      ((p.space.reference x).map Sum.inl + (q.space.reference x).map Sum.inr)
      ((p'.space.reference x).map Sum.inl + (q'.space.reference x).map Sum.inr)
    refine ⟨e.measurable, ?_⟩
    change Measure.map e
      ((p.space.reference x).map Sum.inl + (q.space.reference x).map Sum.inr) = _
    rw [Measure.map_add _ _ e.measurable, Measure.map_map e.measurable measurable_inl,
      Measure.map_map e.measurable measurable_inr]
    change Measure.map (Sum.inl ∘ h.coordinates.coord x) (p.space.reference x) +
      Measure.map (Sum.inr ∘ k.coordinates.coord x) (q.space.reference x) = _
    rw [← Measure.map_map measurable_inl (h.coordinates.coord x).measurable,
      ← Measure.map_map measurable_inr (k.coordinates.coord x).measurable,
      (h.preserving x).map_eq, (k.preserving x).map_eq]
  weight := by
    intro x a ω
    cases ω with
    | inl ω => exact h.weight x a ω
    | inr ψ => exact k.weight x a ψ
  value := by
    intro x a ω
    cases ω with
    | inl ω => exact h.value x a ω
    | inr ψ => exact k.value x a ψ

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

/-- Strict addition of partial homs by disjoint latent sums. -/
def add (p q : PartialHom X A B) : PartialHom X A B :=
  Quotient.liftOn₂ p q (fun p q => ofFamily (p.sum q)) (by
    intro p q p' q' ⟨h⟩ ⟨k⟩
    exact Quotient.sound ⟨h.sum k⟩)

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

theorem observe_add (p q : PartialHom X A B) (x : X) (a : A)
    (f : B → Option ℝ) :
    observe (add p q) x a f = Value.add (observe p x a f) (observe q x a f) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      exact PartialFamily.observe_sum p q x a f

theorem observeJoint_add (p q : PartialHom X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → Option ℝ) :
    observeJoint (add p q) μ a f =
      Value.add (observeJoint p μ a f) (observeJoint q μ a f) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      exact PartialFamily.observeJoint_sum p q μ a f

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
