import QSym.WeightedFibreModel

/-! Substitution of retained coordinates, including evaluation at null points.

The retained coordinate is an explicit index, not recovered from a joint
measure. Measurable substitutions preserve the chosen versions pointwise and
commute with uniform composition. This does not select a disintegration for
an arbitrary function of the returned value.
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory

namespace Coordinates

def reindex {X X' Y Z : Type*} [MeasurableSpace X] [MeasurableSpace X']
    [MeasurableSpace Y] [MeasurableSpace Z] (e : Coordinates X Y Z)
    (f : X' → X) (hf : Measurable f) : Coordinates X' Y Z where
  coord := fun x => e.coord (f x)
  forward := e.forward.comp ((hf.comp measurable_fst).prodMk measurable_snd)
  backward := e.backward.comp ((hf.comp measurable_fst).prodMk measurable_snd)

end Coordinates

namespace Family
variable {X X' X'' : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace X'']
  {A B C : Type*}

def reindex (p : Family X A B) (f : X' → X) (hf : Measurable f) : Family X' A B where
  space := ⟨p.space.Carrier, p.space.reference.comap f hf⟩
  body := fun x => p.body (f x)

def Iso.reindex {p q : Family X A B} (h : Iso p q) (f : X' → X) (hf : Measurable f) :
    Iso (p.reindex f hf) (q.reindex f hf) where
  coordinates := h.coordinates.reindex f hf
  preserving := fun x => h.preserving (f x)
  weight := fun x => h.weight (f x)
  value := fun x => h.value (f x)

def reindexIdIso (p : Family X A B) : Iso (p.reindex id measurable_id) p where
  coordinates := Coordinates.refl
  preserving := fun _ => MeasurePreserving.id _
  weight := fun _ _ _ => rfl
  value := fun _ _ _ => rfl

def reindexCompIso (p : Family X A B) (f : X' → X) (hf : Measurable f)
    (g : X'' → X') (hg : Measurable g) :
    Iso ((p.reindex f hf).reindex g hg) (p.reindex (f ∘ g) (hf.comp hg)) where
  coordinates := Coordinates.refl
  preserving := fun _ => MeasurePreserving.id _
  weight := fun _ _ _ => rfl
  value := fun _ _ _ => rfl

def reindexPureIso (f : X → A → B) (g : X' → X) (hg : Measurable g) :
    Iso ((pure f).reindex g hg) (pure (fun x => f (g x))) where
  coordinates := Coordinates.refl
  preserving := fun _ => MeasurePreserving.id _
  weight := fun _ _ _ => rfl
  value := fun _ _ _ => rfl

def reindexCompFamilyIso (p : Family X A B) (q : Family X B C) (f : X' → X)
    (hf : Measurable f) :
    Iso ((p.comp q).reindex f hf) ((p.reindex f hf).comp (q.reindex f hf)) where
  coordinates := Coordinates.refl
  preserving := fun x => by
    change MeasurePreserving id ((p.space.reference.prod q.space.reference) (f x))
      (((p.space.reference.comap f hf).prod (q.space.reference.comap f hf)) x)
    simp only [ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.comap_apply]
    exact MeasurePreserving.id _
  weight := fun _ _ _ => rfl
  value := fun _ _ _ => rfl

end Family

namespace Hom
variable {X X' X'' : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace X'']
  {A B C : Type*}

def reindex (p : Hom X A B) (f : X' → X) (hf : Measurable f) : Hom X' A B :=
  Quotient.liftOn p (fun p => ofFamily (p.reindex f hf)) (by
    intro p q ⟨h⟩; exact Quotient.sound ⟨h.reindex f hf⟩)

theorem reindex_id (p : Hom X A B) : reindex p id measurable_id = p := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound ⟨p.reindexIdIso⟩

theorem reindex_reindex (p : Hom X A B) (f : X' → X) (hf : Measurable f)
    (g : X'' → X') (hg : Measurable g) :
    reindex (reindex p f hf) g hg = reindex p (f ∘ g) (hf.comp hg) := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound ⟨p.reindexCompIso f hf g hg⟩

theorem reindex_pure (f : X → A → B) (g : X' → X) (hg : Measurable g) :
    reindex (pure f) g hg = pure (fun x => f (g x)) :=
  Quotient.sound ⟨Family.reindexPureIso f g hg⟩

theorem reindex_comp (p : Hom X A B) (q : Hom X B C) (f : X' → X) (hf : Measurable f) :
    reindex (comp p q) f hf = comp (reindex p f hf) (reindex q f hf) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      exact Quotient.sound ⟨Family.reindexCompFamilyIso p q f hf⟩

theorem observe_reindex (p : Hom X A B) (f : X' → X) (hf : Measurable f)
    (x : X') (a : A) (g : B → ℝ) :
    observe (reindex p f hf) x a g = observe p (f x) a g := by
  induction p using Quotient.inductionOn with | _ p => rfl

end Hom
end QSym.WeightedParameter.Fibre
