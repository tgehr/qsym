import QSym.WeightedFibreRooted
import QSym.WeightedFibreDependent
import QSym.DependentIntegrationLaws

/-! Strict partial dependent composition and two-stage reference towers.

The dependent latent reference machinery is shared with the total model. Only
stored weights and values need a new strict composition. Flattening is an
observation operation: a `PartialTower` retains the intermediate fibre for row
queries, while its flattened family can be quotiented or rooted as before.
No almost-everywhere quotient, unconditional Fubini law, or disintegration is
introduced.
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory
open scoped ProbabilityTheory

namespace PartialFamily
variable {X X' : Type} [MeasurableSpace X] [MeasurableSpace X'] {A B C : Type*}

/-- Substitute the retained coordinate without changing any strict stored body. -/
def reindex (p : PartialFamily X A B) (f : X' → X) (hf : Measurable f) :
    PartialFamily X' A B where
  space := ⟨p.space.Carrier, p.space.reference.comap f hf⟩
  body := fun x => p.body (f x)

/-- Reindexing preserves pointwise latent isomorphisms. -/
def Iso.reindex {p q : PartialFamily X A B} (h : Iso p q)
    (f : X' → X) (hf : Measurable f) : Iso (p.reindex f hf) (q.reindex f hf) where
  coordinates := h.coordinates.reindex f hf
  preserving := fun x => h.preserving (f x)
  weight := fun x => h.weight (f x)
  value := fun x => h.value (f x)

@[simp] theorem observe_reindex (p : PartialFamily X A B)
    (f : X' → X) (hf : Measurable f) (x : X') (a : A) (g : B → Option ℝ) :
    (p.reindex f hf).observe x a g = p.observe (f x) a g := rfl

/-- Flatten a strict partial body over the existing dependent reference. -/
def depComp (p : PartialFamily X A B)
    (q : PartialFamily (X × p.space.Carrier) B C) : PartialFamily X A C where
  space := p.space.dependent q.space
  body := fun x =>
    { weight := fun a ω => ((p.body x).value a ω.1).bind fun b =>
        Value.mul ((p.body x).weight a ω.1) ((q.body (x, ω.1)).weight b ω.2)
      value := fun a ω => ((p.body x).value a ω.1).bind fun b =>
        (q.body (x, ω.1)).value b ω.2 }

/-- Uniform strict composition is dependent composition at an independent
continuation reference. -/
def depCompUniformIso (p : PartialFamily X A B) (q : PartialFamily X B C) :
    Iso (p.depComp (q.reindex Prod.fst measurable_fst)) (p.comp q) where
  coordinates := Coordinates.refl
  preserving := fun x => by
    have href : ((p.space.reference ⊗ₖ q.space.reference.comap Prod.fst measurable_fst) x) =
        ((p.space.reference ×ₖ q.space.reference) x) := by
      ext s hs
      rw [ProbabilityTheory.Kernel.compProd_apply hs,
        ProbabilityTheory.Kernel.prod_apply' _ _ _ hs]
      rfl
    change MeasurePreserving id
      ((p.space.reference ⊗ₖ q.space.reference.comap Prod.fst measurable_fst) x)
      ((p.space.reference ×ₖ q.space.reference) x)
    rw [href]
    exact MeasurePreserving.id _
  weight := fun _ _ _ => rfl
  value := fun _ _ _ => rfl

/-- Observation of the uniform special case agrees with ordinary strict
composition. -/
theorem observe_depCompUniform (p : PartialFamily X A B) (q : PartialFamily X B C)
    (x : X) (a : A) (f : C → Option ℝ) :
    (p.depComp (q.reindex Prod.fst measurable_fst)).observe x a f =
      (p.comp q).observe x a f :=
  (p.depCompUniformIso q).observe_eq x a f

/-- Dependent composition is congruent in both stages. The continuation is
compared after transporting the first-stage latent coordinate. -/
def Iso.depComp {p p' : PartialFamily X A B}
    {q : PartialFamily (X × p.space.Carrier) B C}
    {q' : PartialFamily (X × p'.space.Carrier) B C}
    (h : Iso p p')
    (k : Iso q (q'.reindex h.coordinates.joint h.coordinates.joint.measurable)) :
    Iso (p.depComp q) (p'.depComp q') where
  coordinates := h.coordinates.dependent k.coordinates
  preserving := h.coordinates.preserving_dependent k.coordinates h.preserving
    (fun x y => k.preserving (x, y))
  weight := by
    intro x a ω
    change ((p.body x).value a ω.1).bind (fun b =>
      Value.mul ((p.body x).weight a ω.1) ((q.body (x, ω.1)).weight b ω.2)) =
      ((p'.body x).value a (h.coordinates.coord x ω.1)).bind (fun b =>
        Value.mul ((p'.body x).weight a (h.coordinates.coord x ω.1))
          ((q'.body (x, h.coordinates.coord x ω.1)).weight b
            (k.coordinates.coord (x, ω.1) ω.2)))
    rw [h.weight, h.value]
    cases (p'.body x).value a (h.coordinates.coord x ω.1) with
    | none => rfl
    | some b => simp only [Option.some_bind]; rw [k.weight]; rfl
  value := by
    intro x a ω
    change ((p.body x).value a ω.1).bind (fun b => (q.body (x, ω.1)).value b ω.2) =
      ((p'.body x).value a (h.coordinates.coord x ω.1)).bind (fun b =>
        (q'.body (x, h.coordinates.coord x ω.1)).value b
          (k.coordinates.coord (x, ω.1) ω.2))
    rw [h.value]
    cases (p'.body x).value a (h.coordinates.coord x ω.1) with
    | none => rfl
    | some b => simp only [Option.some_bind]; rw [k.value]; rfl

/-- The strict dependent layer conservatively embeds total dependent
composition, including its stored bodies. -/
def ofFamily_depComp (p : Family X A B)
    (q : Family (X × p.space.Carrier) B C) :
    Iso (ofFamily (p.depComp q)) ((ofFamily p).depComp (ofFamily q)) where
  coordinates := Coordinates.refl
  preserving := fun _ => MeasurePreserving.id _
  weight := fun _ _ _ => rfl
  value := fun _ _ _ => rfl

/-- The embedded total dependent observer is exactly the strict dependent
observer. -/
theorem ofFamily_depComp_observe (p : Family X A B)
    (q : Family (X × p.space.Carrier) B C) (x : X) (a : A) (f : C → Option ℝ) :
    ((ofFamily p).depComp (ofFamily q)).observe x a f =
      (p.depComp q).observePartial x a f :=
  (ofFamily_depComp p q).symm.observe_eq x a f

end PartialFamily

/-- A strict two-stage family retaining its intermediate latent fibre. -/
structure PartialTower (X : Type) [MeasurableSpace X] (A B C : Type*) where
  first : PartialFamily X A B
  next : PartialFamily (X × first.space.Carrier) B C

namespace PartialTower
variable {X : Type} [MeasurableSpace X] {A B C : Type*}

/-- Flattening is used for observation, not as an equality of towers. -/
def flatten (t : PartialTower X A B C) : PartialFamily X A C :=
  t.first.depComp t.next

/-- The strict flattened integrand. Neither a zero first weight nor a zero
continuation weight erases an undefined stored value or final test. -/
def integrand (t : PartialTower X A B C) (x : X) (a : A) (f : C → Option ℝ)
    (ω : t.first.space.Carrier × t.next.space.Carrier) : Option ℝ :=
  Value.mul ((t.flatten.body x).weight a ω) (((t.flatten.body x).value a ω).bind f)

def observe (t : PartialTower X A B C) (x : X) (a : A)
    (f : C → Option ℝ) : Option ℝ :=
  t.flatten.observe x a f

/-- Query a retained intermediate coordinate, including zero-measure points. -/
def observeRow (t : PartialTower X A B C) (x : X) (a : A)
    (y : t.first.space.Carrier) (f : C → Option ℝ) : Option ℝ :=
  partialIntegral (t.next.space.reference (x, y)) (fun z => t.integrand x a f (y, z))

/-- The flattened family can enter the original partial quotient. -/
def hom (t : PartialTower X A B C) : PartialHom X A C :=
  PartialHom.ofFamily t.flatten

/-- Rooting a flattened tower fixes its base measure without quotienting away
the tower itself. -/
def rootedFlatten (t : PartialTower X A B C) (μ : Measure X) [SFinite μ] :
    RootedPartialHom X μ A C :=
  RootedPartialHom.ofFamily t.flatten

@[simp] theorem observe_hom (t : PartialTower X A B C) (x : X) (a : A)
    (f : C → Option ℝ) : PartialHom.observe t.hom x a f = t.observe x a f := rfl

@[simp] theorem eraseRoot_rootedFlatten (t : PartialTower X A B C)
    (μ : Measure X) [SFinite μ] : (t.rootedFlatten μ).eraseRoot = t.hom := rfl

@[simp] theorem observe_rootedFlatten (t : PartialTower X A B C)
    (μ : Measure X) [SFinite μ] (x : X) (a : A) (f : C → Option ℝ) :
    (t.rootedFlatten μ).observe x a f = t.observe x a f := rfl

structure Iso (s t : PartialTower X A B C) where
  first : PartialFamily.Iso s.first t.first
  next : PartialFamily.Iso s.next
    (t.next.reindex first.coordinates.joint first.coordinates.joint.measurable)

/-- Tower congruence induces congruence of the flattened observations. -/
def Iso.flatten {s t : PartialTower X A B C} (h : Iso s t) :
    PartialFamily.Iso s.flatten t.flatten :=
  h.first.depComp h.next

theorem Iso.observe_eq {s t : PartialTower X A B C} (h : Iso s t)
    (x : X) (a : A) (f : C → Option ℝ) : s.observe x a f = t.observe x a f :=
  h.flatten.observe_eq x a f

/-- Congruence also preserves every retained row, after transporting its
intermediate coordinate. -/
theorem Iso.observeRow_eq {s t : PartialTower X A B C} (h : Iso s t)
    (x : X) (a : A) (y : s.first.space.Carrier) (f : C → Option ℝ) :
    s.observeRow x a y f = t.observeRow x a (h.first.coordinates.coord x y) f := by
  unfold observeRow integrand
  simp_rw [h.flatten.weight, h.flatten.value]
  exact partialIntegral_comp (h.next.coordinates.coord (x, y)) (h.next.preserving (x, y))
    (fun z => Value.mul ((t.flatten.body x).weight a (h.first.coordinates.coord x y, z))
      (((t.flatten.body x).value a (h.first.coordinates.coord x y, z)).bind f))

/-- Every-row L1 is separate from joint L1 because strict integration observes
null rows as well. -/
def Rows (t : PartialTower X A B C) (x : X) (a : A) (f : C → Option ℝ) : Prop :=
  IntegrableEveryRow (ProbabilityTheory.Kernel.sectR t.next.space.reference x)
    (t.integrand x a f)

def JointL1 (t : PartialTower X A B C) (x : X) (a : A) (f : C → Option ℝ) : Prop :=
  Integrable (fun ω => (t.integrand x a f ω).getD 0) (t.flatten.space.reference x)

/-- Guarded Fubini for strict partial towers. -/
theorem observe_fubini (t : PartialTower X A B C) (x : X) (a : A) (f : C → Option ℝ)
    (hr : t.Rows x a f) (hi : t.JointL1 x a f) :
    t.observe x a f = partialIntegral (t.first.space.reference x)
      (fun y => t.observeRow x a y f) := by
  change partialIntegral ((t.first.space.reference ⊗ₖ t.next.space.reference) x) _ = _
  rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
  apply partialIntegral_compProd_of_integrable _ _ _ hr
  simpa only [JointL1, flatten, PartialFamily.depComp, Space.dependent,
    ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR] using hi

/-- The one-sided law needs only the every-row capability. -/
theorem observe_fubini_refines (t : PartialTower X A B C) (x : X) (a : A)
    (f : C → Option ℝ) (hr : t.Rows x a f) :
    Value.Refines (t.observe x a f)
      (partialIntegral (t.first.space.reference x) (fun y => t.observeRow x a y f)) := by
  change Value.Refines (partialIntegral ((t.first.space.reference ⊗ₖ t.next.space.reference) x) _) _
  rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
  exact partialIntegral_compProd_refines _ _ _ hr

end PartialTower
end QSym.WeightedParameter.Fibre
