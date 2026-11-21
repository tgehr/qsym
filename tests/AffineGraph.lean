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
