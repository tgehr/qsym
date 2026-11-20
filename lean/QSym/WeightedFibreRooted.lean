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

/-- Nonzero scaling preserves and reflects integrability. Only a zero factor
needs a domain premise to move it outside the joint observation. -/
theorem observeJoint_scale_of_zero_defined (p : RootedPartialHom X μ A B)
    (r : ℝ) (a : A) (f : X → B → Option ℝ)
    (hd : r = 0 → Value.Defined (observeJoint p a f)) :
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
    change (r = 0 → Value.Defined (partialIntegral (μ ⊗ₘ p.space.reference) (fun z =>
      Value.mul ((p.body z.1).weight a z.2)
        (((p.body z.1).value a z.2).bind (f z.1))))) at hd
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
    by_cases hz : r = 0
    · exact partialIntegral_scale_defined _ _ _ (hd hz)
    · exact partialIntegral_scale_nonzero _ _ hz _

theorem observeJoint_scale_defined (p : RootedPartialHom X μ A B)
    (r : ℝ) (a : A) (f : X → B → Option ℝ) (hd : Value.Defined (observeJoint p a f)) :
    observeJoint (scale r p) a f = Value.mul (some r) (observeJoint p a f) :=
  observeJoint_scale_of_zero_defined p r a f (fun _ => hd)

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

/-- The empty-output trace at an arbitrary intrinsic root.  Its fibres carry no
source information, so source-first strictness is supplied separately by
`GuardedRootedPartialTrace` below rather than being inferred from emptiness. -/
def zero (X : Type) [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (B : Type*) : RootedPartialHom X μ PUnit B :=
  ofFamily
    { space := Space.ofMeasure Empty 0
      body := fun _ =>
        { weight := fun _ ω => nomatch ω
          value := fun _ ω => nomatch ω } }

@[simp] theorem observeJoint_zero (X : Type) [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (B : Type*) (f : X → B → Option ℝ) :
    (zero X μ B).observeJoint PUnit.unit f = some 0 := by
  unfold observeJoint PartialHom.observeJoint zero ofFamily ofPartialHom
    PartialHom.ofFamily
  rw [Quotient.liftOn_mk]
  unfold PartialFamily.observeJoint
  change partialIntegral _ (fun z : X × Empty => _) = some 0
  rw [partialIntegral_valid _ _ (fun z => isEmptyElim z.2) Integrable.of_isEmpty,
    integral_of_isEmpty]

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

@[simp] theorem mass_zero (X : Type) [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (B : Type*) :
    (zero X μ B).mass = some 0 :=
  observeJoint_zero X μ B (fun _ _ => some 1)

end RootedPartialHom

/-- A rooted trace together with the result of source-first strict evaluation.
An undefined guard cannot be erased by an empty output fibre, a zero scale, or
an empty sum.  Existing nonempty fragments use the defined guard and therefore
retain their previous rooted observations definitionally. -/
structure GuardedRootedPartialTrace (X : Type) [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (B : Type*) where
  guard : Option PUnit.{1}
  trace : RootedPartialHom X μ PUnit.{1} B

namespace GuardedRootedPartialTrace
variable {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ] {B : Type*}

/-- Conservatively embed an existing rooted trace with a defined guard. -/
def ofTrace (p : RootedPartialHom X μ PUnit.{1} B) : GuardedRootedPartialTrace X μ B where
  guard := some PUnit.unit
  trace := p

/-- An empty-output trace whose only observation is its source-first guard. -/
def zero (guard : Option PUnit.{1}) : GuardedRootedPartialTrace X μ B where
  guard := guard
  trace := RootedPartialHom.zero X μ B

/-- Strict ordered observation: inspect the source guard before the output. -/
def observeJoint (p : GuardedRootedPartialTrace X μ B)
    (f : X → B → Option ℝ) : Option ℝ :=
  p.guard.bind fun _ => p.trace.observeJoint PUnit.unit f

/-- Intrinsic mass of a guarded rooted trace. -/
def mass (p : GuardedRootedPartialTrace X μ B) : Option ℝ :=
  p.observeJoint (fun _ _ => some 1)

/-- Scaling acts only after the source-first guard has succeeded. -/
def scale (r : ℝ) (p : GuardedRootedPartialTrace X μ B) :
    GuardedRootedPartialTrace X μ B where
  guard := p.guard
  trace := RootedPartialHom.scale r p.trace

/-- Addition evaluates both source guards strictly before adding the traces. -/
def add (p q : GuardedRootedPartialTrace X μ B) :
    GuardedRootedPartialTrace X μ B where
  guard := p.guard.bind fun _ => q.guard
  trace := RootedPartialHom.add p.trace q.trace

@[simp] theorem observeJoint_ofTrace (p : RootedPartialHom X μ PUnit.{1} B)
    (f : X → B → Option ℝ) :
    (ofTrace p).observeJoint f = p.observeJoint PUnit.unit f := rfl

@[simp] theorem mass_ofTrace (p : RootedPartialHom X μ PUnit.{1} B) :
    (ofTrace p).mass = p.mass := rfl

@[simp] theorem observeJoint_zero (guard : Option PUnit.{1})
    (f : X → B → Option ℝ) :
    (zero (X := X) (μ := μ) (B := B) guard).observeJoint f =
      guard.bind fun _ => some 0 := by
  cases guard <;> simp [observeJoint, zero]

@[simp] theorem mass_zero (guard : Option PUnit.{1}) :
    (zero (X := X) (μ := μ) (B := B) guard).mass =
      guard.bind fun _ => some 0 :=
  observeJoint_zero guard (fun _ _ => some 1)

/-- Scaling retains source failure even when the scale factor is zero. -/
theorem observeJoint_scale (p : GuardedRootedPartialTrace X μ B) (r : ℝ)
    (f : X → B → Option ℝ) :
    (scale r p).observeJoint f =
      p.observeJoint (fun x b => Value.mul (some r) (f x b)) := by
  rcases p with ⟨guard, trace⟩
  cases guard <;>
    simp [observeJoint, scale, RootedPartialHom.observeJoint_scale]

theorem observeJoint_scale_of_zero_defined (p : GuardedRootedPartialTrace X μ B)
    (r : ℝ) (f : X → B → Option ℝ) (hd : r = 0 → Value.Defined (p.observeJoint f)) :
    (scale r p).observeJoint f = Value.mul (some r) (p.observeJoint f) := by
  rcases p with ⟨guard, trace⟩
  cases guard with
  | none => rfl
  | some u =>
      change r = 0 → Value.Defined (trace.observeJoint PUnit.unit f) at hd
      change (RootedPartialHom.scale r trace).observeJoint PUnit.unit f =
        Value.mul (some r) (trace.observeJoint PUnit.unit f)
      exact RootedPartialHom.observeJoint_scale_of_zero_defined trace r PUnit.unit f hd

theorem observeJoint_scale_defined (p : GuardedRootedPartialTrace X μ B)
    (r : ℝ) (f : X → B → Option ℝ) (hd : Value.Defined (p.observeJoint f)) :
    (scale r p).observeJoint f = Value.mul (some r) (p.observeJoint f) :=
  observeJoint_scale_of_zero_defined p r f (fun _ => hd)

/-- Guarded addition has exactly the same strict observation algebra as the
legacy ordered observer, including failure in either source guard. -/
theorem observeJoint_add (p q : GuardedRootedPartialTrace X μ B)
    (f : X → B → Option ℝ) :
    (add p q).observeJoint f = Value.add (p.observeJoint f) (q.observeJoint f) := by
  rcases p with ⟨gp, tp⟩
  rcases q with ⟨gq, tq⟩
  cases gp <;> cases gq <;>
    simp [observeJoint, add, RootedPartialHom.observeJoint_add, Value.add]

theorem mass_scale_defined (p : GuardedRootedPartialTrace X μ B) (r : ℝ)
    (hd : Value.Defined p.mass) :
    (scale r p).mass = Value.mul (some r) p.mass :=
  observeJoint_scale_defined p r (fun _ _ => some 1) hd

theorem mass_add (p q : GuardedRootedPartialTrace X μ B) :
    (add p q).mass = Value.add p.mass q.mass :=
  observeJoint_add p q (fun _ _ => some 1)

end GuardedRootedPartialTrace
end QSym.WeightedParameter.Fibre
