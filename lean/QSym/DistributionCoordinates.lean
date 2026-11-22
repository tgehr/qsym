import QSym.WeightedFibrePartialDependent

/-! Coordinate elimination for a joint term with an explicitly retained reference.
Marginalization moves a coordinate into the latent parameter space. Disintegration
at a retained coordinate specializes its chosen fibre, including at null points.
Both are operations on the quotient by pointwise fibre isomorphisms. -/
noncomputable section
namespace QSym.WeightedParameter.Fibre

open MeasureTheory
open scoped ProbabilityTheory

variable {X X' Y Z : Type} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Z] {A B : Type*}

namespace PartialFamily

def marginalize (κ : ProbabilityTheory.Kernel X Y) [ProbabilityTheory.IsSFiniteKernel κ]
    (p : PartialFamily (X × Y) A B) : PartialFamily X A B where
  space := (⟨Y, κ⟩ : Space X).dependent p.space
  body := fun x => {
    weight := fun a yz => (p.body (x, yz.1)).weight a yz.2
    value := fun a yz => (p.body (x, yz.1)).value a yz.2 }

def Iso.marginalize {p q : PartialFamily (X × Y) A B} (e : Iso p q)
    (κ : ProbabilityTheory.Kernel X Y) [ProbabilityTheory.IsSFiniteKernel κ] :
    Iso (p.marginalize κ) (q.marginalize κ) where
  coordinates := (Coordinates.refl (X := X) (Y := Y)).dependent e.coordinates
  preserving := Coordinates.preserving_dependent _ _ (fun _ => MeasurePreserving.id _)
    (fun x y => e.preserving (x, y))
  weight := fun x a yz => e.weight (x, yz.1) a yz.2
  value := fun x a yz => e.value (x, yz.1) a yz.2

end PartialFamily

namespace PartialHom

def reindex (p : PartialHom X A B) (g : X' → X) (hg : Measurable g) : PartialHom X' A B :=
  Quotient.liftOn p (fun p => ofFamily (p.reindex g hg)) (by
    intro p q ⟨e⟩; exact Quotient.sound ⟨e.reindex g hg⟩)

/-- Strip the explicit coordinate reference at this particular point. -/
def sectionAt (p : PartialHom X A B) (x : X) : PartialHom PUnit.{1} A B :=
  p.reindex (fun _ => x) measurable_const

theorem observe_sectionAt (p : PartialHom X A B) (x : X) (a : A) (f : B → Option ℝ) :
    (p.sectionAt x).observe PUnit.unit a f = p.observe x a f := by
  induction p using Quotient.inductionOn with | _ p => rfl

/-- Cancel the explicit reference of a weighted deterministic term at a point,
then substitute its return in the test. A partial return, weight or test stays partial. -/
theorem observe_sectionAt_weighted_pure (r : X → A → Option B) (w : X → A → B → Option ℝ)
    (x : X) (a : A) (f : B → Option ℝ) :
    ((reweight w (pure r)).sectionAt x).observe PUnit.unit a f =
      (r x a).bind (fun b => Value.mul (w x a b) (f b)) := by
  rw [observe_sectionAt, observe_reweight, observe_pure]

def marginalize (κ : ProbabilityTheory.Kernel X Y) [ProbabilityTheory.IsSFiniteKernel κ]
    (p : PartialHom (X × Y) A B) : PartialHom X A B :=
  Quotient.liftOn p (fun p => ofFamily (p.marginalize κ)) (by
    intro p q ⟨e⟩; exact Quotient.sound ⟨e.marginalize κ⟩)

theorem sectionAt_reweight (p : PartialHom X A B) (w : X → A → B → Option ℝ) (x : X) :
    (reweight w p).sectionAt x = reweight (fun _ => w x) (p.sectionAt x) := by
  induction p using Quotient.inductionOn with | _ p => rfl

/-- Disintegration of an explicitly referenced sum keeps both pointwise summands. -/
theorem sectionAt_add (p q : PartialHom X A B) (x : X) :
    (add p q).sectionAt x = add (p.sectionAt x) (q.sectionAt x) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      apply Quotient.sound
      refine ⟨{ coordinates := Coordinates.refl, preserving := ?_, weight := fun _ _ _ => rfl,
                value := fun _ _ _ => rfl }⟩
      intro u
      let atX := fun _ : PUnit.{1} => x
      change MeasurePreserving id ((p.space.sum q.space).reference x)
        (((p.reindex atX measurable_const).space.sum (q.reindex atX measurable_const).space).reference u)
      simp only [PartialFamily.reindex, Space.sum, ProbabilityTheory.Kernel.add_apply, ProbabilityTheory.Kernel.map_apply _ measurable_inl,
        ProbabilityTheory.Kernel.map_apply _ measurable_inr, ProbabilityTheory.Kernel.comap_apply]
      exact MeasurePreserving.id _

/-- A factor independent of the eliminated coordinate can be moved outside
the marginal, including a partial factor on a function-valued return. -/
theorem marginalize_reweight (p : PartialHom (X × Y) A B) (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] (w : X → A → B → Option ℝ) :
    marginalize κ (reweight (fun xy => w xy.1) p) = reweight w (marginalize κ p) := by
  induction p using Quotient.inductionOn with | _ p => rfl

/-- Substitution of a retained coordinate commutes with elimination of a
different coordinate. Its reference is substituted along with the body. -/
theorem reindex_marginalize (p : PartialHom (X × Y) A B) (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] (g : X' → X) (hg : Measurable g) :
    (marginalize κ p).reindex g hg = marginalize (κ.comap g hg)
      (p.reindex (fun xy : X' × Y => (g xy.1, xy.2)) ((hg.comp measurable_fst).prodMk measurable_snd)) := by
  induction p using Quotient.inductionOn with | _ p =>
    apply Quotient.sound
    refine ⟨{ coordinates := Coordinates.refl, preserving := ?_, weight := fun _ _ _ => rfl,
              value := fun _ _ _ => rfl }⟩
    intro x
    change MeasurePreserving id ((κ ⊗ₖ p.space.reference) (g x))
      ((κ.comap g hg ⊗ₖ p.space.reference.comap _ ((hg.comp measurable_fst).prodMk measurable_snd)) x)
    have eq : ((κ ⊗ₖ p.space.reference) (g x)) =
        ((κ.comap g hg ⊗ₖ p.space.reference.comap
          (fun xy : X' × Y => (g xy.1, xy.2)) ((hg.comp measurable_fst).prodMk measurable_snd)) x) := by
      ext s hs
      rw [ProbabilityTheory.Kernel.compProd_apply hs, ProbabilityTheory.Kernel.compProd_apply hs]
      rfl
    rw [eq]
    exact MeasurePreserving.id _

theorem sectionAt_marginalize (p : PartialHom (X × Y) A B) (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] (x : X) :
    (marginalize κ p).sectionAt x = marginalize (κ.comap (fun _ : PUnit.{1} => x) measurable_const)
      (p.reindex (fun uy : PUnit.{1} × Y => (x, uy.2)) (measurable_const.prodMk measurable_snd)) :=
  reindex_marginalize p κ (fun _ => x) measurable_const

/-- A fibre of the marginal is the joint observation of the remaining
coordinates at exactly that point. The test may itself be partial. -/
theorem observe_marginalize (p : PartialHom (X × Y) A B) (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] (x : X) (a : A) (f : B → Option ℝ) :
    (marginalize κ p).observe x a f =
      (p.reindex (Prod.mk x) measurable_prodMk_left).observeJoint (κ x) a (fun _ => f) := by
  induction p using Quotient.inductionOn with | _ p =>
    apply congrArg (fun μ => partialIntegral μ (fun yz : Y × p.space.Carrier =>
      Value.mul ((p.body (x, yz.1)).weight a yz.2) (((p.body (x, yz.1)).value a yz.2).bind f)))
    exact ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR κ p.space.reference x

/-- Moving a coordinate into the latent space preserves joint observations at
any s-finite root. This changes the bracketing of one integral, so even a
partial or nonintegrable probe needs no side condition. -/
theorem observeJoint_marginalize (p : PartialHom (X × Y) A B) (μ : Measure X) [SFinite μ]
    (κ : ProbabilityTheory.Kernel X Y) [ProbabilityTheory.IsSFiniteKernel κ]
    (a : A) (f : X → B → Option ℝ) :
    (marginalize κ p).observeJoint μ a f = p.observeJoint (μ ⊗ₘ κ) a (fun xy => f xy.1) := by
  induction p using Quotient.inductionOn with | _ p =>
    let η := p.space.reference
    let e : (X × Y) × p.space.Carrier ≃ᵐ X × (Y × p.space.Carrier) := MeasurableEquiv.prodAssoc
    have he : MeasurePreserving e ((μ ⊗ₘ κ) ⊗ₘ η) (μ ⊗ₘ (κ ⊗ₖ η)) := by
      refine ⟨e.measurable, ?_⟩
      apply Measure.ext_of_lintegral
      intro g hg
      have hge : Measurable (fun t => g (e t)) := hg.comp e.measurable
      rw [lintegral_map hg e.measurable, Measure.lintegral_compProd hge,
        Measure.lintegral_compProd (hge.lintegral_kernel_prod_right' (κ := η)),
        Measure.lintegral_compProd hg]
      apply lintegral_congr
      intro x
      exact (ProbabilityTheory.Kernel.lintegral_compProd κ η x (hg.comp measurable_prodMk_left)).symm
    exact (partialIntegral_comp e he (fun t =>
      Value.mul ((p.body (t.1, t.2.1)).weight a t.2.2)
        (((p.body (t.1, t.2.1)).value a t.2.2).bind (f t.1)))).symm

/-- Eliminating two coordinates in succession is elimination against their
dependent joint reference. Only the latent coordinates are reassociated. -/
theorem marginalize_marginalize (p : PartialHom ((X × Y) × Z) A B)
    (κ : ProbabilityTheory.Kernel X Y) (η : ProbabilityTheory.Kernel (X × Y) Z)
    [ProbabilityTheory.IsSFiniteKernel κ] [ProbabilityTheory.IsSFiniteKernel η] :
    marginalize κ (marginalize η p) = marginalize (κ ⊗ₖ η)
      (p.reindex MeasurableEquiv.prodAssoc.symm MeasurableEquiv.prodAssoc.symm.measurable) := by
  induction p using Quotient.inductionOn with | _ p =>
    symm
    apply Quotient.sound
    exact ⟨{ coordinates := Coordinates.const MeasurableEquiv.prodAssoc
             preserving := preserving_depAssoc κ η p.space.reference
             weight := fun _ _ _ => rfl
             value := fun _ _ _ => rfl }⟩

end PartialHom

namespace RootedPartialHom

/-- The input type witnesses the factorization of the explicit joint reference.
Moving its second coordinate into the latent space leaves the first reference. -/
def marginalize {μ : Measure X} [SFinite μ] (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] (p : RootedPartialHom (X × Y) (μ ⊗ₘ κ) A B) :
    RootedPartialHom X μ A B :=
  ofPartialHom (PartialHom.marginalize κ p.eraseRoot)

theorem observeJoint_marginalize {μ : Measure X} [SFinite μ] (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] (p : RootedPartialHom (X × Y) (μ ⊗ₘ κ) A B)
    (a : A) (f : X → B → Option ℝ) :
    (marginalize κ p).observeJoint a f = p.observeJoint a (fun xy => f xy.1) :=
  PartialHom.observeJoint_marginalize p.eraseRoot μ κ a f

end RootedPartialHom

namespace PartialFamily

/-- Integrand of a fixed probe, retaining both the base and latent point. -/
def testBody (p : PartialFamily X A B) (a : A) (f : X → B → Option ℝ)
    (xz : X × p.space.Carrier) : Option ℝ :=
  Value.mul ((p.body xz.1).weight a xz.2) (((p.body xz.1).value a xz.2).bind (f xz.1))

/-- Numerical reconstruction from the actual pointwise section observations.
The absolute profile protects against latent signed cancellation. -/
theorem observeJoint_sections (p : PartialFamily X A B) (μ : Measure X) [SFinite μ]
    (a : A) (f : X → B → Option ℝ)
    (hm : AEStronglyMeasurable (fun xz => (p.testBody a f xz).getD 0) (μ ⊗ₘ p.space.reference)) :
    (PartialHom.ofFamily p).observeJoint μ a f =
      integrateSections μ (∀ xz, Value.Defined (p.testBody a f xz))
        (fun x => ((PartialHom.ofFamily p).sectionAt x).observe PUnit.unit a (f x))
        (fun x => ∫ z, |(p.testBody a f (x, z)).getD 0| ∂p.space.reference x) :=
  partialIntegral_compProd_sections μ p.space.reference (p.testBody a f) hm

end PartialFamily
end QSym.WeightedParameter.Fibre
