import QSym.WeightedFibrePartial

/-! Dependent latent references. A second reference may depend on the first
latent coordinate, without imposing a measurable space on returned values.

`depComp` flattens a two-stage family for observations at the retained `X`.
It is not an identification of all conditioning data: the two references must
still be retained for queries at the intermediate coordinate. The congruence
below preserves the second reference at *every* intermediate point.
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory
open scoped ProbabilityTheory

namespace Coordinates
variable {X Y Y' Z Z' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Y'] [MeasurableSpace Z] [MeasurableSpace Z']

/-- Triangular coordinates: the second change can depend on the first sample. -/
def dependent (e : Coordinates X Y Y') (f : Coordinates (X × Y) Z Z') :
    Coordinates X (Y × Z) (Y' × Z') where
  coord := fun x =>
    { toEquiv :=
        { toFun := fun p => (e.coord x p.1, f.coord (x, p.1) p.2)
          invFun := fun p => ((e.coord x).symm p.1,
            (f.coord (x, (e.coord x).symm p.1)).symm p.2)
          left_inv := by intro p; simp
          right_inv := by intro p; simp }
      measurable_toFun := ((e.coord x).measurable.comp measurable_fst).prodMk
        (f.forward.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
      measurable_invFun := ((e.coord x).symm.measurable.comp measurable_fst).prodMk
        (f.backward.comp ((measurable_const.prodMk
          ((e.coord x).symm.measurable.comp measurable_fst)).prodMk measurable_snd)) }
  forward := (e.forward.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
    (f.forward.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd))
  backward := (e.backward.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
    (f.backward.comp ((measurable_fst.prodMk
      (e.backward.comp (measurable_fst.prodMk measurable_snd.fst))).prodMk measurable_snd.snd))

theorem preserving_dependent (e : Coordinates X Y Y') (f : Coordinates (X × Y) Z Z')
    {κ : ProbabilityTheory.Kernel X Y} {κ' : ProbabilityTheory.Kernel X Y'}
    {η : ProbabilityTheory.Kernel (X × Y) Z} {η' : ProbabilityTheory.Kernel (X × Y') Z'}
    [ProbabilityTheory.IsSFiniteKernel κ] [ProbabilityTheory.IsSFiniteKernel κ']
    [ProbabilityTheory.IsSFiniteKernel η] [ProbabilityTheory.IsSFiniteKernel η']
    (he : ∀ x, MeasurePreserving (e.coord x) (κ x) (κ' x))
    (hf : ∀ x y, MeasurePreserving (f.coord (x, y)) (η (x, y)) (η' (x, e.coord x y)))
    (x : X) :
    MeasurePreserving ((e.dependent f).coord x) ((κ ⊗ₖ η) x) ((κ' ⊗ₖ η') x) where
  measurable := ((e.dependent f).coord x).measurable
  map_eq := by
    apply Measure.ext_of_lintegral
    intro g hg
    rw [lintegral_map hg ((e.dependent f).coord x).measurable,
      ProbabilityTheory.Kernel.lintegral_compProd κ η x
        (f := fun p => g ((e.dependent f).coord x p))
        (hg.comp ((e.dependent f).coord x).measurable),
      ProbabilityTheory.Kernel.lintegral_compProd _ _ _ hg]
    change (∫⁻ y, ∫⁻ z, g (e.coord x y, f.coord (x, y) z) ∂η (x, y) ∂κ x) = _
    refine Eq.trans ?_ ((he x).lintegral_comp_emb (e.coord x).measurableEmbedding
      (fun y => ∫⁻ z, g (y, z) ∂η' (x, y)))
    apply lintegral_congr
    intro y
    exact (hf x y).lintegral_comp_emb (f.coord (x, y)).measurableEmbedding
      (fun z => g (e.coord x y, z))

end Coordinates

/-- Reassociation of dependent references preserves their flattened measure
at every retained point. No almost-everywhere choice of a conditional occurs. -/
theorem preserving_depAssoc {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W]
    (κ : ProbabilityTheory.Kernel X Y) (η : ProbabilityTheory.Kernel (X × Y) Z)
    (θ : ProbabilityTheory.Kernel ((X × Y) × Z) W)
    [ProbabilityTheory.IsSFiniteKernel κ] [ProbabilityTheory.IsSFiniteKernel η]
    [ProbabilityTheory.IsSFiniteKernel θ] (x : X) :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (Y × Z) × W ≃ᵐ Y × (Z × W))
      (((κ ⊗ₖ η) ⊗ₖ θ.comap MeasurableEquiv.prodAssoc.symm
        MeasurableEquiv.prodAssoc.symm.measurable) x)
      ((κ ⊗ₖ (η ⊗ₖ θ)) x) where
  measurable := MeasurableEquiv.prodAssoc.measurable
  map_eq := by
    apply Measure.ext_of_lintegral
    intro g hg
    rw [lintegral_map hg MeasurableEquiv.prodAssoc.measurable]
    change (∫⁻ p : (Y × Z) × W, g (p.1.1, (p.1.2, p.2)) ∂_) = _
    rw [ProbabilityTheory.Kernel.lintegral_compProd _ _ _
      (f := fun p : (Y × Z) × W => g (p.1.1, (p.1.2, p.2)))
      (hg.comp MeasurableEquiv.prodAssoc.measurable)]
    change (∫⁻ p : Y × Z, ∫⁻ w, g (p.1, (p.2, w)) ∂θ ((x, p.1), p.2) ∂(κ ⊗ₖ η) x) = _
    rw [ProbabilityTheory.Kernel.lintegral_compProd κ η x
      (f := fun p => ∫⁻ w, g (p.1, (p.2, w)) ∂θ ((x, p.1), p.2))
      ((show Measurable (fun p : (Y × Z) × W => g (p.1.1, (p.1.2, p.2))) from
        hg.comp MeasurableEquiv.prodAssoc.measurable).lintegral_kernel_prod_right''
        (η := θ.comap MeasurableEquiv.prodAssoc.symm MeasurableEquiv.prodAssoc.symm.measurable))]
    rw [ProbabilityTheory.Kernel.lintegral_compProd _ _ _ hg]
    apply lintegral_congr
    intro y
    rw [ProbabilityTheory.Kernel.lintegral_compProd _ _ _
      (f := fun p => g (y, p))
      (hg.comp measurable_prodMk_left)]

namespace Space
variable {X : Type*} [MeasurableSpace X]

def dependent (p : Space X) (q : Space (X × p.Carrier)) : Space X where
  Carrier := p.Carrier × q.Carrier
  reference := p.reference ⊗ₖ q.reference

end Space

namespace Family
variable {X : Type*} [MeasurableSpace X] {A B C : Type*}

/-- Flatten a chosen dependent reference tower. Keep `p` and `q` when an
intermediate-coordinate query may follow; `Hom.ofFamily` alone forgets it. -/
def depComp (p : Family X A B) (q : Family (X × p.space.Carrier) B C) : Family X A C where
  space := p.space.dependent q.space
  body := fun x =>
    { weight := fun a ω => (p.body x).weight a ω.1 *
        (q.body (x, ω.1)).weight ((p.body x).value a ω.1) ω.2
      value := fun a ω => (q.body (x, ω.1)).value ((p.body x).value a ω.1) ω.2 }

/-- The existing uniform composition is the special case whose second
reference ignores the first latent coordinate. -/
def depCompUniformIso (p : Family X A B) (q : Family X B C) :
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

/-- The continuation comparison is made after transporting the first-stage
coordinate. This prevents an almost-everywhere equality of rows from being
used as a pointwise conditioning law. -/
def Iso.depComp {p p' : Family X A B}
    {q : Family (X × p.space.Carrier) B C} {q' : Family (X × p'.space.Carrier) B C}
    (h : Iso p p')
    (k : Iso q (q'.reindex h.coordinates.joint h.coordinates.joint.measurable)) :
    Iso (p.depComp q) (p'.depComp q') where
  coordinates := h.coordinates.dependent k.coordinates
  preserving := h.coordinates.preserving_dependent k.coordinates h.preserving
    (fun x y => k.preserving (x, y))
  weight := by
    intro x a ω
    change (p.body x).weight a ω.1 * (q.body (x, ω.1)).weight ((p.body x).value a ω.1) ω.2 =
      (p'.body x).weight a (h.coordinates.coord x ω.1) *
        (q'.body (x, h.coordinates.coord x ω.1)).weight
          ((p'.body x).value a (h.coordinates.coord x ω.1)) (k.coordinates.coord (x, ω.1) ω.2)
    rw [h.weight, h.value, k.weight]
    rfl
  value := by
    intro x a ω
    change (q.body (x, ω.1)).value ((p.body x).value a ω.1) ω.2 =
      (q'.body (x, h.coordinates.coord x ω.1)).value
        ((p'.body x).value a (h.coordinates.coord x ω.1)) (k.coordinates.coord (x, ω.1) ω.2)
    rw [h.value, k.value]
    rfl

/-- Associativity for the flattened family. The three chosen stage references
remain the data for any later intermediate-coordinate queries. -/
def depAssocIso {D : Type*} (p : Family X A B)
    (q : Family (X × p.space.Carrier) B C)
    (r : Family ((X × p.space.Carrier) × q.space.Carrier) C D) :
    Iso ((p.depComp q).depComp
      (r.reindex MeasurableEquiv.prodAssoc.symm MeasurableEquiv.prodAssoc.symm.measurable))
      (p.depComp (q.depComp r)) where
  coordinates := Coordinates.const MeasurableEquiv.prodAssoc
  preserving := preserving_depAssoc p.space.reference q.space.reference r.space.reference
  weight := by intro x a ω; exact mul_assoc _ _ _
  value := fun _ _ _ => rfl

end Family
end QSym.WeightedParameter.Fibre
