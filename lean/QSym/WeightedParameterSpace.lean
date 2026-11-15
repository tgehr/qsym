import QSym.WeightedParameterLaws

/-! Uniform weighted kernels modulo exact parameter isomorphisms.

This supplies actual equality for identity and associative composition, rather
than just equality after a scalar observer. It is a category of fixed-fibre
kernels. It is not yet a monad accepting arbitrary functions into the quotient:
such functions need a jointly admissible, uniform (or dependent) presentation.
The quotient does not integrate out latent variables or discard null points.
-/
noncomputable section
namespace QSym.WeightedParameter
open MeasureTheory

structure ParameterSpace where
  Carrier : Type
  [measurable : MeasurableSpace Carrier]
  reference : Measure Carrier
  [sfinite : SFinite reference]

attribute [instance] ParameterSpace.measurable ParameterSpace.sfinite

namespace ParameterSpace

def point : ParameterSpace where
  Carrier := PUnit
  reference := Measure.dirac PUnit.unit

def real : ParameterSpace where
  Carrier := ℝ
  reference := volume

def prod (p q : ParameterSpace) : ParameterSpace where
  Carrier := p.Carrier × q.Carrier
  reference := p.reference.prod q.reference

end ParameterSpace

structure ParamKernel (A B : Type*) where
  space : ParameterSpace
  body : Kernel space.Carrier A B

namespace ParamKernel

def pure {A B : Type*} (f : A → B) : ParamKernel A B :=
  ⟨ParameterSpace.point, Kernel.pure f⟩

def comp {A B C : Type*} (p : ParamKernel A B) (q : ParamKernel B C) : ParamKernel A C :=
  ⟨p.space.prod q.space, Kernel.comp p.body q.body⟩

def density {A : Type*} (w : A → ℝ → ℝ) : ParamKernel A ℝ :=
  ⟨ParameterSpace.real, Kernel.density w⟩

def reweight {A B : Type*} (g : A → B → ℝ) (p : ParamKernel A B) : ParamKernel A B :=
  ⟨p.space, Kernel.reweight g p.body⟩

structure Iso {A B : Type*} (p q : ParamKernel A B) where
  coord : p.space.Carrier ≃ᵐ q.space.Carrier
  preserving : MeasurePreserving coord p.space.reference q.space.reference
  weight : ∀ a ω, p.body.weight a ω = q.body.weight a (coord ω)
  value : ∀ a ω, p.body.value a ω = q.body.value a (coord ω)

namespace Iso

def refl {A B : Type*} (p : ParamKernel A B) : Iso p p where
  coord := MeasurableEquiv.refl _
  preserving := MeasurePreserving.id _
  weight := fun _ _ => rfl
  value := fun _ _ => rfl

def symm {A B : Type*} {p q : ParamKernel A B} (h : Iso p q) : Iso q p where
  coord := h.coord.symm
  preserving := MeasurePreserving.symm h.coord h.preserving
  weight := fun a ω => by simpa using (h.weight a (h.coord.symm ω)).symm
  value := fun a ω => by simpa using (h.value a (h.coord.symm ω)).symm

def trans {A B : Type*} {p q r : ParamKernel A B} (h : Iso p q) (k : Iso q r) : Iso p r where
  coord := h.coord.trans k.coord
  preserving := k.preserving.comp h.preserving
  weight := fun a ω => (h.weight a ω).trans (k.weight a (h.coord ω))
  value := fun a ω => (h.value a ω).trans (k.value a (h.coord ω))

def comp {A B C : Type*} {p p' : ParamKernel A B} {q q' : ParamKernel B C}
    (h : Iso p p') (k : Iso q q') : Iso (p.comp q) (p'.comp q') where
  coord := h.coord.prodCongr k.coord
  preserving := h.preserving.prod k.preserving
  weight := by
    intro a ω
    change p.body.weight a ω.1 * q.body.weight (p.body.value a ω.1) ω.2 =
      p'.body.weight a (h.coord ω.1) * q'.body.weight (p'.body.value a (h.coord ω.1)) (k.coord ω.2)
    rw [h.weight, h.value, k.weight]
  value := by
    intro a ω
    change q.body.value (p.body.value a ω.1) ω.2 =
      q'.body.value (p'.body.value a (h.coord ω.1)) (k.coord ω.2)
    rw [h.value, k.value]

theorem body_eq {A B : Type*} {p q : ParamKernel A B} (h : Iso p q) :
    p.body = Kernel.pull h.coord.toEquiv q.body := Kernel.ext h.weight h.value

def reweight {A B : Type*} {p q : ParamKernel A B} (h : Iso p q) (g : A → B → ℝ) :
    Iso (p.reweight g) (q.reweight g) where
  coord := h.coord
  preserving := h.preserving
  weight := by
    intro a ω
    change p.body.weight a ω * g a (p.body.value a ω) =
      q.body.weight a (h.coord ω) * g a (q.body.value a (h.coord ω))
    rw [h.weight, h.value]
  value := h.value

theorem observe_eq {A B : Type*} {p q : ParamKernel A B} (h : Iso p q) (a : A) (f : B → ℝ) :
    Kernel.integrate p.space.reference p.body a f =
      Kernel.integrate q.space.reference q.body a f := by
  rw [h.body_eq]
  exact Kernel.integrate_pull h.coord h.preserving _ a f

def pullChart {A : Type*} {p q : ParamKernel A ℝ} (h : Iso p q) {a : A}
    (c : DensityChart q.space.reference q.body a) : DensityChart p.space.reference p.body a where
  coord := h.coord.trans c.coord
  preserving := c.preserving.comp h.preserving
  output := fun ω => (h.value a ω).trans (c.output (h.coord ω))
  measurable_weight := by
    have he : p.body.weight a = fun ω => q.body.weight a (h.coord ω) := funext (h.weight a)
    rw [he]
    exact c.measurable_weight.comp h.coord.measurable

theorem densityAt_pullChart {A : Type*} {p q : ParamKernel A ℝ} (h : Iso p q) {a : A}
    (c : DensityChart q.space.reference q.body a) (x : ℝ) :
    DensityChart.densityAt (h.pullChart c) x = DensityChart.densityAt c x := by
  change p.body.weight a (h.coord.symm (c.coord.symm x)) = q.body.weight a (c.coord.symm x)
  rw [h.weight, h.coord.apply_symm_apply]

theorem density_eq {A : Type*} {p q : ParamKernel A ℝ} (h : Iso p q) {a : A}
    (c : DensityChart p.space.reference p.body a)
    (d : DensityChart q.space.reference q.body a) (x : ℝ) :
    DensityChart.densityAt c x = DensityChart.densityAt d x :=
  (DensityChart.densityAt_unique c (h.pullChart d) x).trans (h.densityAt_pullChart d x)

end Iso

def compPureIso {A B : Type*} (p : ParamKernel A B) : Iso (p.comp (pure id)) p where
  coord := MeasurableEquiv.prodPUnit
  preserving := measurePreserving_prodPUnit p.space.reference
  weight := by intro a ω; simp [comp, pure, Kernel.comp, Kernel.pure]; rfl
  value := fun _ _ => rfl

def pureCompIso {A B : Type*} (p : ParamKernel A B) : Iso ((pure id).comp p) p where
  coord := MeasurableEquiv.punitProd
  preserving := measurePreserving_punitProd p.space.reference
  weight := by intro a ω; simp [comp, pure, Kernel.comp, Kernel.pure]; rfl
  value := fun _ _ => rfl

def compAssocIso {A B C D : Type*} (p : ParamKernel A B) (q : ParamKernel B C)
    (r : ParamKernel C D) : Iso ((p.comp q).comp r) (p.comp (q.comp r)) where
  coord := MeasurableEquiv.prodAssoc
  preserving := MeasureTheory.measurePreserving_prodAssoc _ _ _
  weight := by intro a ω; simp [comp, Kernel.comp, mul_assoc]; rfl
  value := fun _ _ => rfl

def pureCompPureIso {A B C : Type*} (f : A → B) (g : B → C) :
    Iso ((pure f).comp (pure g)) (pure (g ∘ f)) where
  coord := MeasurableEquiv.prodPUnit
  preserving := measurePreserving_prodPUnit ParameterSpace.point.reference
  weight := by intro a ω; simp [comp, pure, Kernel.comp, Kernel.pure]
  value := fun _ _ => rfl

instance kernelSetoid (A B : Type*) : Setoid (ParamKernel A B) where
  r p q := Nonempty (Iso p q)
  iseqv := ⟨fun p => ⟨Iso.refl p⟩, fun ⟨h⟩ => ⟨h.symm⟩, fun ⟨h⟩ ⟨k⟩ => ⟨h.trans k⟩⟩

end ParamKernel

def Hom (A B : Type*) := Quotient (ParamKernel.kernelSetoid A B)

namespace Hom

def ofKernel {A B : Type*} (p : ParamKernel A B) : Hom A B := Quotient.mk _ p

def pure {A B : Type*} (f : A → B) : Hom A B := ofKernel (ParamKernel.pure f)

def comp {A B C : Type*} (p : Hom A B) (q : Hom B C) : Hom A C :=
  Quotient.liftOn₂ p q (fun p q => ofKernel (p.comp q)) (by
    intro p q p' q' hp hq
    rcases hp with ⟨h⟩; rcases hq with ⟨k⟩
    exact Quotient.sound ⟨h.comp k⟩)

theorem comp_pure {A B : Type*} (p : Hom A B) : comp p (pure id) = p := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound ⟨p.compPureIso⟩

theorem pure_comp {A B : Type*} (p : Hom A B) : comp (pure id) p = p := by
  induction p using Quotient.inductionOn with | _ p =>
    exact Quotient.sound ⟨p.pureCompIso⟩

theorem comp_assoc {A B C D : Type*} (p : Hom A B) (q : Hom B C) (r : Hom C D) :
    comp (comp p q) r = comp p (comp q r) := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      induction r using Quotient.inductionOn with | _ r =>
        exact Quotient.sound ⟨ParamKernel.compAssocIso p q r⟩

theorem pure_comp_pure {A B C : Type*} (f : A → B) (g : B → C) :
    comp (pure f) (pure g) = pure (g ∘ f) :=
  Quotient.sound ⟨ParamKernel.pureCompPureIso f g⟩

noncomputable def observe {A B : Type*} (p : Hom A B) (a : A) (f : B → ℝ) : Option ℝ :=
  Quotient.liftOn p (fun p => Kernel.integrate p.space.reference p.body a f) (by
    intro p q ⟨h⟩; exact h.observe_eq a f)

theorem observe_pure {A B : Type*} (f : A → B) (a : A) (g : B → ℝ) :
    observe (pure f) a g = some (g (f a)) := by
  change Kernel.integrate (Measure.dirac PUnit.unit) (Kernel.pure f) a g = _
  exact Kernel.integrate_pure f a g

def density {A : Type*} (w : A → ℝ → ℝ) : Hom A ℝ := ofKernel (ParamKernel.density w)

def reweight {A B : Type*} (g : A → B → ℝ) (p : Hom A B) : Hom A B :=
  Quotient.liftOn p (fun p => ofKernel (p.reweight g)) (by
    intro p q ⟨h⟩; exact Quotient.sound ⟨h.reweight g⟩)

/-- A density capability on the quotient. Its result is independent of both
the chosen representative and the chosen chart. -/
structure Chart {A : Type*} (p : Hom A ℝ) (a : A) where
  representative : ParamKernel A ℝ
  represents : ofKernel representative = p
  geometry : DensityChart representative.space.reference representative.body a

namespace Chart

def densityAt {A : Type*} {p : Hom A ℝ} {a : A} (c : Chart p a) (x : ℝ) : ℝ :=
  c.geometry.densityAt x

theorem densityAt_unique {A : Type*} {p : Hom A ℝ} {a : A} (c d : Chart p a) (x : ℝ) :
    c.densityAt x = d.densityAt x := by
  obtain ⟨h⟩ := Quotient.exact (c.represents.trans d.represents.symm)
  exact h.density_eq c.geometry d.geometry x

theorem densityAt_eq_of_eq {A : Type*} {p q : Hom A ℝ} {a : A}
    (c : Chart p a) (d : Chart q a) (h : p = q) (x : ℝ) : c.densityAt x = d.densityAt x := by
  cases h
  exact densityAt_unique c d x

def density {A : Type*} (w : A → ℝ → ℝ) (a : A) (hw : Measurable (w a)) : Chart (Hom.density w) a where
  representative := ParamKernel.density w
  represents := rfl
  geometry := DensityChart.identity w a hw

@[simp] theorem densityAt_density {A : Type*} (w : A → ℝ → ℝ) (a : A)
    (hw : Measurable (w a)) (x : ℝ) : (density w a hw).densityAt x = w a x := rfl

def compPure {A : Type*} {p : Hom A ℝ} {a : A} (c : Chart p a) :
    Chart (Hom.comp p (Hom.pure id)) a where
  representative := c.representative.comp (ParamKernel.pure id)
  represents := by
    change Hom.comp (ofKernel c.representative) (Hom.pure id) = _
    rw [c.represents]
  geometry := c.geometry.compPure

theorem densityAt_compPure {A : Type*} {p : Hom A ℝ} {a : A} (c : Chart p a) (x : ℝ) :
    c.compPure.densityAt x = c.densityAt x := DensityChart.densityAt_compPure c.geometry x

def reweight {A : Type*} {p : Hom A ℝ} {a : A} (c : Chart p a)
    (g : A → ℝ → ℝ) (hg : Measurable (g a)) : Chart (Hom.reweight g p) a where
  representative := c.representative.reweight g
  represents := by
    change Hom.reweight g (ofKernel c.representative) = _
    rw [c.represents]
  geometry := c.geometry.reweight g hg

theorem densityAt_reweight {A : Type*} {p : Hom A ℝ} {a : A} (c : Chart p a)
    (g : A → ℝ → ℝ) (hg : Measurable (g a)) (x : ℝ) :
    (c.reweight g hg).densityAt x = c.densityAt x * g a x :=
  DensityChart.densityAt_reweight c.geometry g hg x

theorem observe_eq {A : Type*} {p : Hom A ℝ} {a : A} (c : Chart p a) (f : ℝ → ℝ) :
    Hom.observe p a f = finiteIntegral volume (fun x => c.densityAt x * f x) := by
  exact (congrArg (fun q => Hom.observe q a f) c.represents.symm).trans
    (DensityChart.integrate_eq c.geometry f)

end Chart
end Hom

/-- Distribution-valued objects of the uniform kernel category. Binding still
requires a `Hom A B`, not an arbitrary function `A → Trace B`. -/
abbrev Trace (A : Type*) := Hom PUnit A

end QSym.WeightedParameter
