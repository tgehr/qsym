import QSym.FixedPoint
import QSym.AxiomCheck

namespace QSym.FixedPointTests
open OmegaCompletePartialOrder FixedPoint

noncomputable def lookup (n : ℕ) : (ℕ → Part ℕ) →𝒄 Part ℕ :=
  ⟨Pi.evalOrderHom n, fun _ => rfl⟩

noncomputable def step : (ℕ → Part ℕ) →𝒄 (ℕ → Part ℕ) :=
  ContinuousHom.flip (fun n => if n = 0 then ContinuousHom.const (Part.some 0)
    else if n < 10 then lookup (n - 1) else lookup (n + 1))

theorem step_apply (f : ℕ → Part ℕ) (n : ℕ) :
    step f n = if n = 0 then Part.some 0 else if n < 10 then f (n - 1) else f (n + 1) := by
  simp only [step, ContinuousHom.flip_apply]
  split_ifs <;> rfl

def answer (n : ℕ) : Part ℕ := if n < 10 then Part.some 0 else Part.none

theorem answer_fixed : step answer = answer := by
  funext n
  rw [step_apply]
  by_cases h0 : n = 0
  · simp [h0, answer]
  · by_cases h : n < 10
    · have hp : n - 1 < 10 := by omega
      simp [h0, h, answer, hp]
    · have hp : ¬n + 1 < 10 := by omega
      simp [h0, h, answer, hp]

theorem terminates (n : ℕ) (hn : n < 10) : 0 ∈ approx step (n + 1) n := by
  induction n with
  | zero => simp [approx, step_apply]
  | succ n ih =>
    have h : n < 10 := by omega
    simpa [approx, Function.iterate_succ_apply', step_apply, hn] using ih h

theorem exact_domain (n : ℕ) : (least step n).Dom ↔ n < 10 := by
  constructor
  · intro hd
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    have upper := least_le step (le_of_eq answer_fixed)
    have hy' := upper n y hy
    by_contra hn
    simp [answer, hn] at hy'
  · intro hn
    exact Part.dom_iff_mem.mpr ⟨0, (mem_least_iff step n 0).mpr ⟨n + 1, terminates n hn⟩⟩

theorem option_domain (n : ℕ) : Value.Defined (value step n) ↔ n < 10 :=
  (defined_value step n).trans (exact_domain n)

theorem terminates_at_nine : Value.Defined (value step 9) := (option_domain 9).mpr (by decide)
theorem diverges_at_ten : ¬Value.Defined (value step 10) :=
  fun h => (by decide : ¬10 < 10) ((option_domain 10).mp h)

#qsym_check_axioms FixedPoint.unfold
#qsym_check_axioms FixedPoint.least_le
#qsym_check_axioms FixedPoint.approx_le
#qsym_check_axioms FixedPoint.least_eq_of_le
#qsym_check_axioms FixedPoint.least_id
#qsym_check_axioms FixedPoint.least_const
#qsym_check_axioms FixedPoint.mem_least_iff
#qsym_check_axioms FixedPoint.domain_least_iff
#qsym_check_axioms FixedPoint.defined_value_iff
#qsym_check_axioms FixedPoint.value_eq_some_iff
#qsym_check_axioms answer_fixed
#qsym_check_axioms terminates
#qsym_check_axioms exact_domain
#qsym_check_axioms option_domain
#qsym_check_axioms terminates_at_nine
#qsym_check_axioms diverges_at_ten
end QSym.FixedPointTests
