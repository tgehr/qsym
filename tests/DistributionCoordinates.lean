import QSym.DistributionPartialModel
import QSym.Refinement
import QSym.AxiomCheck

noncomputable section
namespace QSym.DistributionCoordinateTests
open MeasureTheory WeightedParameter.Fibre
open scoped ProbabilityTheory

variable {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] {A B : Type*}

/-- The ordinary rule path works with a dependent reference and an arbitrary
return type. The chosen section can be queried even at an outer null point. -/
theorem section_marginal_rule (p : PartialHom (X × Y) A B) (κ : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsSFiniteKernel κ] (x : X) :
    (PartialHom.marginalize κ p).sectionAt x =
      PartialHom.marginalize (κ.comap (fun _ : PUnit.{1} => x) measurable_const)
        (p.reindex (fun uy : PUnit.{1} × Y => (x, uy.2)) (measurable_const.prodMk measurable_snd)) := by
  qsym_rule

theorem marginal_fusion_rule (p : PartialHom ((X × Y) × Z) A B)
    (κ : ProbabilityTheory.Kernel X Y) (η : ProbabilityTheory.Kernel (X × Y) Z)
    [ProbabilityTheory.IsSFiniteKernel κ] [ProbabilityTheory.IsSFiniteKernel η] :
    PartialHom.marginalize κ (PartialHom.marginalize η p) = PartialHom.marginalize (κ ⊗ₖ η)
      (p.reindex MeasurableEquiv.prodAssoc.symm MeasurableEquiv.prodAssoc.symm.measurable) := by
  qsym_rule

theorem marginal_test_rule (p : PartialHom (X × Y) A B) (μ : Measure X) [SFinite μ]
    (κ : ProbabilityTheory.Kernel X Y) [ProbabilityTheory.IsSFiniteKernel κ] (a : A)
    (f : X → B → Option ℝ) :
    (PartialHom.marginalize κ p).observeJoint μ a f = p.observeJoint (μ ⊗ₘ κ) a (fun xy => f xy.1) := by
  qsym_rule

theorem section_probe_rule (r : X → A → Option B) (w : X → A → B → Option ℝ)
    (x : X) (a : A) (f : B → Option ℝ) :
    ((PartialHom.reweight w (PartialHom.pure r)).sectionAt x).observe PUnit.unit a f =
      (r x a).bind (fun b => Value.mul (w x a b) (f b)) := by qsym_rule

/-- A section at zero sees the hole in an otherwise negative constant
density, even when the return is a function. -/
theorem signed_function_section (x : ℝ) :
    ((PartialHom.reweight (fun y _ _ => some (if y = (0 : ℝ) then 0 else -2))
      (PartialHom.pure (fun _ (_ : Unit) => some (fun n : ℕ => n + 1)))).sectionAt x).observe
        PUnit.unit () (fun v => some (v 2 : ℝ)) = some (if x = 0 then 0 else -6) := by
  rw [section_probe_rule]
  by_cases hx : x = 0 <;> norm_num [Value.mul, hx]

/-- Direct proof term for a generated observation of a real density. -/
theorem density_section (p : Distribution.DensityProgram) (x : ℝ) :
    (p.semantic.sectionAt x).observe PUnit.unit PUnit.unit (fun _ => some 1) = p.density x :=
  p.semanticDensityAt_eq x

theorem reconstruct_rule (p : PartialFamily X A B) (μ : Measure X) [SFinite μ] (a : A)
    (f : X → B → Option ℝ)
    (hm : AEStronglyMeasurable (fun t => (p.testBody a f t).getD 0) (μ ⊗ₘ p.space.reference)) :
    (PartialHom.ofFamily p).observeJoint μ a f =
      integrateSections μ (∀ t, Value.Defined (p.testBody a f t))
        (fun x => ((PartialHom.ofFamily p).sectionAt x).observe PUnit.unit a (f x))
        (fun x => ∫ z, |(p.testBody a f (x, z)).getD 0| ∂p.space.reference x) := by qsym_rule

#qsym_check_axioms RootedPartialHom.observeJoint_marginalize
#qsym_check_axioms PartialHom.sectionAt_add
#qsym_check_axioms PartialHom.reindex_marginalize
#qsym_check_axioms PartialHom.marginalize_reweight
#qsym_check_axioms PartialHom.sectionAt_reweight
#qsym_check_axioms PartialHom.observe_marginalize
#qsym_check_axioms section_marginal_rule
#qsym_check_axioms marginal_fusion_rule
#qsym_check_axioms marginal_test_rule
#qsym_check_axioms section_probe_rule
#qsym_check_axioms signed_function_section
#qsym_check_axioms density_section
#qsym_check_axioms reconstruct_rule
end QSym.DistributionCoordinateTests
