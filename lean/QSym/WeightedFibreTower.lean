import QSym.WeightedFibreDependent
import QSym.DependentIntegrationLaws

/-! A two-stage weighted reference tower, retaining intermediate fibres.

Flattening is an observation operation, not an equality of towers. In
particular, equal flattened measures need not have equal `observeRow` values.
The output types need no measurable structure. The continuation reference is
a certified kernel on retained and latent coordinates, not an arbitrary
set-theoretic function returning measures.
-/
noncomputable section
namespace QSym.WeightedParameter.Fibre
open MeasureTheory
open scoped ProbabilityTheory

structure Tower (X : Type) [MeasurableSpace X] (A B C : Type*) where
  first : Family X A B
  next : Family (X × first.space.Carrier) B C

namespace Tower
variable {X : Type} [MeasurableSpace X] {A B C : Type*}

def flatten (t : Tower X A B C) : Family X A C := t.first.depComp t.next

def integrand (t : Tower X A B C) (x : X) (a : A) (f : C → Option ℝ)
    (ω : t.first.space.Carrier × t.next.space.Carrier) : Option ℝ :=
  Value.mul (some ((t.flatten.body x).weight a ω)) (f ((t.flatten.body x).value a ω))

def observe (t : Tower X A B C) (x : X) (a : A) (f : C → Option ℝ) : Option ℝ :=
  t.flatten.observePartial x a f

/-- Query a chosen intermediate coordinate, including zero-measure points.
The first weight stays inside the row integral, so zero scaling needs no
unjustified assumption that the unscaled continuation has finite mass. -/
def observeRow (t : Tower X A B C) (x : X) (a : A)
    (y : t.first.space.Carrier) (f : C → Option ℝ) : Option ℝ :=
  partialIntegral (t.next.space.reference (x, y)) (fun z => t.integrand x a f (y, z))

structure Iso (s t : Tower X A B C) where
  first : Family.Iso s.first t.first
  next : Family.Iso s.next
    (t.next.reindex first.coordinates.joint first.coordinates.joint.measurable)

def Iso.flatten {s t : Tower X A B C} (h : Iso s t) : Family.Iso s.flatten t.flatten :=
  h.first.depComp h.next

theorem Iso.observe_eq {s t : Tower X A B C} (h : Iso s t) (x : X) (a : A)
    (f : C → Option ℝ) : s.observe x a f = t.observe x a f :=
  h.flatten.observePartial_eq x a f

theorem Iso.observeRow_eq {s t : Tower X A B C} (h : Iso s t) (x : X) (a : A)
    (y : s.first.space.Carrier) (f : C → Option ℝ) :
    s.observeRow x a y f = t.observeRow x a (h.first.coordinates.coord x y) f := by
  unfold observeRow integrand
  simp_rw [h.flatten.weight, h.flatten.value]
  exact partialIntegral_comp (h.next.coordinates.coord (x, y)) (h.next.preserving (x, y))
    (fun z => Value.mul
      (some ((t.flatten.body x).weight a (h.first.coordinates.coord x y, z)))
      (f ((t.flatten.body x).value a (h.first.coordinates.coord x y, z))))

def Rows (t : Tower X A B C) (x : X) (a : A) (f : C → Option ℝ) : Prop :=
  IntegrableEveryRow (ProbabilityTheory.Kernel.sectR t.next.space.reference x) (t.integrand x a f)

def JointL1 (t : Tower X A B C) (x : X) (a : A) (f : C → Option ℝ) : Prop :=
  Integrable (fun ω => (t.integrand x a f ω).getD 0) (t.flatten.space.reference x)

theorem observe_fubini (t : Tower X A B C) (x : X) (a : A) (f : C → Option ℝ)
    (hr : t.Rows x a f) (hi : t.JointL1 x a f) :
    t.observe x a f = partialIntegral (t.first.space.reference x) (fun y => t.observeRow x a y f) := by
  change partialIntegral ((t.first.space.reference ⊗ₖ t.next.space.reference) x) _ = _
  rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
  apply partialIntegral_compProd_of_integrable _ _ _ hr
  simpa only [JointL1, flatten, Family.depComp, Space.dependent,
    ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR] using hi

theorem observe_fubini_refines (t : Tower X A B C) (x : X) (a : A) (f : C → Option ℝ)
    (hr : t.Rows x a f) :
    Value.Refines (t.observe x a f)
      (partialIntegral (t.first.space.reference x) (fun y => t.observeRow x a y f)) := by
  change Value.Refines (partialIntegral ((t.first.space.reference ⊗ₖ t.next.space.reference) x) _) _
  rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
  exact partialIntegral_compProd_refines _ _ _ hr

end Tower
end QSym.WeightedParameter.Fibre
