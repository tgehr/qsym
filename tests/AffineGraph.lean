import QSym.DistributionGraphBridge
import QSym.AxiomCheck

noncomputable section
namespace QSym.Distribution.AffineGraphTests
open GraphFibre Set

theorem reversed_endpoints :
    marginalOn (Ico 0 1) (fun x => -2*x+1) 1 = some (1/2) ∧
    marginalOn (Ico 0 1) (fun x => -2*x+1) (-1) = some 0 := by
  constructor <;> rw [affine_marginalOn _ _ _ (by norm_num)] <;>
    norm_num [sourceWeight, mem_Ico]

theorem puncture (a b x : ℝ) (ha : a ≠ 0) :
    marginalOn ({x}ᶜ) (fun u => a*u+b) (a*x+b) = some 0 := by
  rw [affine_marginalOn _ _ _ ha]
  have inverse : (a*x+b-b)/a = x := by field_simp [ha]
  rw [inverse]
  simp [sourceWeight]

theorem constant_at_image {s : Set ℝ} (hs : s.Nonempty) (b : ℝ) :
    marginalOn s (fun _ => b) b = none := by
  obtain ⟨x, hx⟩ := hs
  rw [marginalOn, fibreOn_of_critical hx rfl (by simp)]
  rfl

/-- Even one undefined value on the joint graph invalidates the strict
integral reconstructed from its fibres. -/
theorem joint_missing_point :
    partialIntegral MeasureTheory.volume (fun y =>
      (fibre (fun x : ℝ => -2*x+1) y).bind (fun atoms =>
        observe atoms (fun x => if x = 2 ∧ y = -3 then none else some 0))) = none := by
  classical
  rw [← affine_disintegrates (-2) 1 (by norm_num)]
  unfold partialIntegral
  split
  · rename_i h
    have bad := h.1 2
    norm_num [Value.Defined] at bad
    obtain ⟨_, hv⟩ := bad
    cases hv
  · rfl

/-- Discarding the inverse point over a puncture can turn a missing strict
integral into zero, even if the test is defined everywhere else. -/
private def hole (x : ℝ) : Option ℝ := if x = 0 then none else some 0

theorem excluded_missing_point :
    partialIntegral MeasureTheory.volume (fun x =>
      Value.mul (some (sourceWeight ({0}ᶜ) x)) (hole x)) = none ∧
    partialIntegral MeasureTheory.volume (fun y => (fibreOn ({0}ᶜ) (fun x => 1*x+0) y).bind
      (fun atoms => observe atoms hole)) = some 0 := by
  classical
  constructor
  · unfold partialIntegral
    split
    · rename_i h
      obtain ⟨_, hv⟩ := h.1 0
      simp [hole, sourceWeight, Value.mul] at hv
    · rfl
  · have zero (y : ℝ) : (fibreOn ({0}ᶜ) (fun x => 1*x+0) y).bind
        (fun atoms => observe atoms hole) = some 0 := by
      rw [affine_fibreOn _ 1 0 one_ne_zero]
      by_cases hy : y = 0 <;> simp [hy, hole, observe, Value.add, Value.mul]
    simp only [zero]
    exact partialIntegral_zero _

#qsym_check_axioms affine_disintegratesOn
#qsym_check_axioms affine_disintegratesOn_strict
#qsym_check_axioms excluded_missing_point
#qsym_check_axioms joint_missing_point
#qsym_check_axioms affine_disintegrates
#qsym_check_axioms affine_fibre_rule
#qsym_check_axioms affine_mass_rule
#qsym_check_axioms integral_dirac_graph
#qsym_check_axioms bind_dirac_graph
#qsym_check_axioms affine_chart_rule
#qsym_check_axioms affine_lebesgue
#qsym_check_axioms affine_fibreOn
#qsym_check_axioms affine_marginalOn
#qsym_check_axioms reversed_endpoints
#qsym_check_axioms puncture
#qsym_check_axioms constant_at_image

end QSym.Distribution.AffineGraphTests
