import QSym.WeightedFibrePartialModel

/-! Partial weighted families with an intrinsic base measure.

A rooted hom is indexed by its base measure. Composition therefore requires both
sides to have the same root by construction. The underlying unrooted quotient is
unchanged; rooting only supplies the measure used by joint observations. No
change-of-base, Fubini, or disintegration law is introduced.
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory
open scoped ProbabilityTheory

namespace PartialHom
variable {X : Type} [MeasurableSpace X] {A B : Type*}

/-- Joint observation is strict under partial reweighting as well. -/
theorem observeJoint_reweight (p : PartialHom X A B) (μ : Measure X) [SFinite μ]
    (g : X → A → B → Option ℝ) (a : A) (f : X → B → Option ℝ) :
    observeJoint (reweight g p) μ a f =
      observeJoint p μ a (fun x b => Value.mul (g x a b) (f x b)) := by
  induction p using Quotient.inductionOn with | _ p =>
    change partialIntegral (μ ⊗ₘ p.space.reference) (fun z =>
      Value.mul (((p.body z.1).value a z.2).bind (fun b =>
        Value.mul ((p.body z.1).weight a z.2) (g z.1 a b)))
        (((p.body z.1).value a z.2).bind (f z.1))) =
      partialIntegral (μ ⊗ₘ p.space.reference) (fun z =>
        Value.mul ((p.body z.1).weight a z.2)
          (((p.body z.1).value a z.2).bind (fun b =>
            Value.mul (g z.1 a b) (f z.1 b))))
    congr 1
    funext z
    cases hw : (p.body z.1).weight a z.2 with
    | none =>
      cases hv : (p.body z.1).value a z.2 <;>
        simp [hw, hv, Value.mul]
    | some w =>
      cases hv : (p.body z.1).value a z.2 with
      | none => simp [hw, hv, Value.mul]
      | some b =>
        cases hg : g z.1 a b <;> cases hf : f z.1 b <;>
          simp [hw, hv, hg, hf, Value.mul, mul_assoc]

end PartialHom

/-- A partial hom with its base measure fixed in the type. -/
structure RootedPartialHom (X : Type) [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (A B : Type*) where
  underlying : PartialHom X A B

namespace RootedPartialHom
variable {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ] {A B C : Type*}

/-- Forget the root, retaining the verified unrooted semantic object. -/
def eraseRoot (p : RootedPartialHom X μ A B) : PartialHom X A B := p.underlying

/-- Root an existing unrooted hom at a chosen base measure. -/
def ofPartialHom (p : PartialHom X A B) : RootedPartialHom X μ A B := ⟨p⟩

/-- Root a representative without introducing another quotient. -/
def ofFamily (p : PartialFamily X A B) : RootedPartialHom X μ A B :=
  ofPartialHom (PartialHom.ofFamily p)

/-- Deterministic partial introduction at any fixed root. -/
def pure (f : X → A → Option B) : RootedPartialHom X μ A B :=
  ofPartialHom (PartialHom.pure f)

/-- Composition is well-typed only when both operands have the same root. -/
def comp (p : RootedPartialHom X μ A B) (q : RootedPartialHom X μ B C) :
    RootedPartialHom X μ A C :=
  ofPartialHom (PartialHom.comp p.underlying q.underlying)

/-- Reweighting does not change the root. -/
def reweight (g : X → A → B → Option ℝ) (p : RootedPartialHom X μ A B) :
    RootedPartialHom X μ A B :=
  ofPartialHom (PartialHom.reweight g p.underlying)

/-- Constant scaling is semantic reweighting at the same intrinsic root. -/
def scale (r : ℝ) (p : RootedPartialHom X μ A B) : RootedPartialHom X μ A B :=
  reweight (fun _ _ _ => some r) p

/-- Strict addition uses disjoint latent sums and preserves the intrinsic root. -/
def add (p q : RootedPartialHom X μ A B) : RootedPartialHom X μ A B :=
  ofPartialHom (PartialHom.add p.underlying q.underlying)

/-- A pointwise fibre observation is independent of the root. -/
def observe (p : RootedPartialHom X μ A B) (x : X) (a : A)
    (f : B → Option ℝ) : Option ℝ :=
  PartialHom.observe p.underlying x a f

/-- Joint observation uses the root stored in the type, not an extra argument. -/
def observeJoint (p : RootedPartialHom X μ A B) (a : A)
    (f : X → B → Option ℝ) : Option ℝ :=
  PartialHom.observeJoint p.underlying μ a f

/-- Conservative rooting of the old total quotient. -/
def ofTotalHom (p : Hom X A B) : RootedPartialHom X μ A B :=
  ofPartialHom (PartialHom.ofHom p)

theorem ofTotalHom_observeJoint (p : Hom X A B) (a : A) (f : X → B → Option ℝ) :
    observeJoint (ofTotalHom (μ := μ) p) a f = Hom.observeJointPartial p μ a f :=
  PartialHom.ofHom_observeJointPartial p μ a f

@[simp] theorem observe_pure (f : X → A → Option B)
    (x : X) (a : A) (g : B → Option ℝ) :
    observe (pure (μ := μ) f) x a g = (f x a).bind g :=
  PartialHom.observe_pure f x a g

theorem observe_reweight (p : RootedPartialHom X μ A B)
    (g : X → A → B → Option ℝ) (x : X) (a : A) (f : B → Option ℝ) :
    observe (reweight g p) x a f =
      observe p x a (fun b => Value.mul (g x a b) (f b)) :=
  PartialHom.observe_reweight p.underlying g x a f

theorem observeJoint_reweight (p : RootedPartialHom X μ A B)
    (g : X → A → B → Option ℝ) (a : A) (f : X → B → Option ℝ) :
    observeJoint (reweight g p) a f =
      observeJoint p a (fun x b => Value.mul (g x a b) (f x b)) :=
  PartialHom.observeJoint_reweight p.underlying μ g a f

/-- Addition is branch-strict for pointwise observations. -/
theorem observe_add (p q : RootedPartialHom X μ A B)
    (x : X) (a : A) (f : B → Option ℝ) :
    observe (add p q) x a f = Value.add (observe p x a f) (observe q x a f) :=
  PartialHom.observe_add p.underlying q.underlying x a f

/-- Addition is branch-strict for rooted joint observations, with no domain guard. -/
theorem observeJoint_add (p q : RootedPartialHom X μ A B)
    (a : A) (f : X → B → Option ℝ) :
    observeJoint (add p q) a f =
      Value.add (observeJoint p a f) (observeJoint q a f) :=
  PartialHom.observeJoint_add p.underlying q.underlying μ a f

/-- Scaling can be moved into the strict test without any domain hypothesis. -/
theorem observeJoint_scale (p : RootedPartialHom X μ A B)
    (r : ℝ) (a : A) (f : X → B → Option ℝ) :
    observeJoint (scale r p) a f =
      observeJoint p a (fun x b => Value.mul (some r) (f x b)) :=
  observeJoint_reweight p (fun _ _ _ => some r) a f

/-- A constant factor can be pulled out of a defined joint observation.
When identifying the result with scaling the source observation, the guard is
necessary: direct zero scaling can differ at undefined or nonintegrable sources. -/
theorem observeJoint_scale_defined (p : RootedPartialHom X μ A B)
    (r : ℝ) (a : A) (f : X → B → Option ℝ)
    (hd : Value.Defined (observeJoint p a f)) :
    observeJoint (scale r p) a f = Value.mul (some r) (observeJoint p a f) := by
  rw [observeJoint_scale]
  rcases p with ⟨p⟩
  induction p using Quotient.inductionOn with | _ p =>
    unfold observeJoint PartialHom.observeJoint at hd ⊢
    rw [Quotient.liftOn_mk] at hd ⊢
    change partialIntegral (μ ⊗ₘ p.space.reference) (fun z =>
      Value.mul ((p.body z.1).weight a z.2)
        (((p.body z.1).value a z.2).bind (fun b => Value.mul (some r) (f z.1 b)))) =
      Value.mul (some r) (partialIntegral (μ ⊗ₘ p.space.reference) (fun z =>
        Value.mul ((p.body z.1).weight a z.2)
          (((p.body z.1).value a z.2).bind (f z.1))))
    change Value.Defined (partialIntegral (μ ⊗ₘ p.space.reference) (fun z =>
      Value.mul ((p.body z.1).weight a z.2)
        (((p.body z.1).value a z.2).bind (f z.1)))) at hd
    have hrow : (fun z : X × p.space.Carrier =>
        Value.mul ((p.body z.1).weight a z.2)
          (((p.body z.1).value a z.2).bind (fun b => Value.mul (some r) (f z.1 b)))) =
        fun z => Value.mul (some r) (Value.mul ((p.body z.1).weight a z.2)
          (((p.body z.1).value a z.2).bind (f z.1))) := by
      funext z
      cases hw : (p.body z.1).weight a z.2 with
      | none =>
        cases hv : (p.body z.1).value a z.2 <;> simp [hw, hv, Value.mul]
      | some w =>
        cases hv : (p.body z.1).value a z.2 with
        | none => simp [hw, hv, Value.mul]
        | some b =>
          cases hf : f z.1 b <;>
            simp [hw, hv, hf, Value.mul, mul_assoc, mul_left_comm]
    rw [hrow]
    exact partialIntegral_scale_defined (μ ⊗ₘ p.space.reference) r _ hd

@[simp] theorem eraseRoot_pure (f : X → A → Option B) :
    eraseRoot (pure (μ := μ) f) = PartialHom.pure f := rfl

@[simp] theorem eraseRoot_comp (p : RootedPartialHom X μ A B)
    (q : RootedPartialHom X μ B C) :
    eraseRoot (comp p q) = PartialHom.comp p.underlying q.underlying := rfl

@[simp] theorem eraseRoot_reweight (g : X → A → B → Option ℝ)
    (p : RootedPartialHom X μ A B) :
    eraseRoot (reweight g p) = PartialHom.reweight g p.underlying := rfl

@[simp] theorem eraseRoot_scale (r : ℝ) (p : RootedPartialHom X μ A B) :
    eraseRoot (scale r p) = PartialHom.reweight (fun _ _ _ => some r) p.underlying := rfl

@[simp] theorem eraseRoot_add (p q : RootedPartialHom X μ A B) :
    eraseRoot (add p q) = PartialHom.add p.underlying q.underlying := rfl

end RootedPartialHom

/-- A rooted pointwise family of traces. -/
abbrev RootedPartialTrace (X : Type) [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (B : Type*) :=
  RootedPartialHom X μ PUnit B

namespace RootedPartialHom
variable {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ] {B : Type*}

/-- Intrinsic mass of a rooted trace. -/
def mass (p : RootedPartialTrace X μ B) : Option ℝ :=
  p.observeJoint PUnit.unit (fun _ _ => some 1)

/-- Erasing the root recovers exactly the previous explicitly based observer. -/
theorem mass_eraseRoot (p : RootedPartialTrace X μ B) :
    p.mass = PartialHom.observeJoint p.underlying μ PUnit.unit (fun _ _ => some 1) := rfl

/-- Defined source mass scales exactly, including by a negative or zero factor. -/
theorem mass_scale_defined (p : RootedPartialTrace X μ B) (r : ℝ)
    (hd : Value.Defined p.mass) :
    (scale r p).mass = Value.mul (some r) p.mass :=
  observeJoint_scale_defined p r PUnit.unit (fun _ _ => some 1) hd

/-- Mass addition is exact and remains undefined if either branch is undefined. -/
theorem mass_add (p q : RootedPartialTrace X μ B) :
    (add p q).mass = Value.add p.mass q.mass :=
  observeJoint_add p q PUnit.unit (fun _ _ => some 1)

end RootedPartialHom
end QSym.WeightedParameter.Fibre
