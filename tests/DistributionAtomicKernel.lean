import QSym.DistributionAtomicKernel
import QSym.AxiomCheck

noncomputable section
open scoped ENNReal
open QSym.Distribution QSym.Distribution.Atomic

namespace AtomicKernelTest

private def half := ENNReal.ofReal (1/2 : ℝ)

private theorem half_eq : half = (1/2 : ℝ≥0∞) := by
  rw [half, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem succ_iterate_zero (n : ℕ) : Nat.succ^[n] 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]

private def seed (i : ℕ) : Model ℕ := (fun y => half * atom i y, {i})

-- Emit the current counter with weight 1/2 and otherwise increment and retry.
private def walk (k : ℕ → Option (D ℕ)) (i : ℕ) : Option (D ℕ) :=
  addValue (scaleValue (some (1/2)) (diracValue (some i))) (scaleValue (some (1/2)) (k i.succ))

private theorem walk_step (i : ℕ) (k : ℕ → Option (D ℕ)) (d : D ℕ) (m : Model ℕ)
    (h : k i.succ = some d) (hd : Presents d m) :
    ∃ e, walk k i = some e ∧ Presents e (strictRetryStep (seed i) half m) := by
  have hpos : 0 ≤ (1/2 : ℝ) := by norm_num
  refine ⟨.add (.scale (1/2) (.dirac i)) (.scale (1/2) d), by simp [walk, h, scaleValue, diracValue, addValue], ?_, ?_⟩
  · exact ((Represents.dirac i).scale hpos).add (hd.1.scale hpos)
  · simp [strictRetryStep, seed, hd.2]

theorem walk_limit (i : ℕ) :
    kernelModelAt walk i = some ((kernelStep seed (fun _ => half) Nat.succ).lfp i) :=
  kernelModelAt_on walk seed (fun _ => half) Nat.succ Set.univ (fun _ _ => Set.mem_univ _)
    (fun x _ => walk_step x) (Set.mem_univ i)

theorem walk_weight (j : ℕ) :
    ((kernelStep seed (fun _ => half) Nat.succ).lfp 0).1 j = (1/2 : ℝ≥0∞)^(j+1) := by
  rw [kernel_lfp_weight, tsum_eq_single j]
  · simp [reachWeight_const, seed, atom, succ_iterate_zero, half_eq, pow_succ]
  · intro i hi
    simp [seed, atom, succ_iterate_zero, Ne.symm hi]

theorem walk_visits (j : ℕ) : j ∈ ((kernelStep seed (fun _ => half) Nat.succ).lfp 0).2 := by
  rw [kernel_lfp_visits]
  exact ⟨j, by simp [seed, succ_iterate_zero]⟩

-- A zero recursive coefficient suppresses later weights. Probes still visit them.
theorem zero_weight_continuation :
    ((kernelStep seed (fun _ => 0) Nat.succ).lfp 0).1 1 = 0 ∧
    1 ∈ ((kernelStep seed (fun _ => 0) Nat.succ).lfp 0).2 := by
  constructor
  · rw [kernel_lfp_weight]
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    cases n <;> simp [reachWeight, seed, atom]
  · rw [kernel_lfp_visits]
    exact ⟨1, by simp [seed]⟩

private def partialWalk (k : ℕ → Option (D ℕ)) (i : ℕ) :=
  if i = 0 then none else walk k i

theorem partial_walk_positive (i : ℕ) (hi : 0 < i) :
    kernelModelAt partialWalk i = some ((kernelStep seed (fun _ => half) Nat.succ).lfp i) := by
  apply kernelModelAt_on partialWalk seed (fun _ => half) Nat.succ (Set.Ioi 0)
    (fun x _ => Nat.zero_lt_succ x) _ hi
  intro x hx k d m hk hd
  simpa [partialWalk, ne_of_gt (Set.mem_Ioi.mp hx)] using walk_step x k d m hk hd

theorem partial_walk_zero : kernelModelAt partialWalk 0 = none :=
  limitModel_missing (n := 1) (by rfl)

#qsym_check_axioms kernel_continuous
#qsym_check_axioms reachWeight_prod
#qsym_check_axioms kernel_lfp_weight
#qsym_check_axioms kernel_lfp_visits
#qsym_check_axioms kernelModelAt_on
#qsym_check_axioms walk_limit
#qsym_check_axioms walk_weight
#qsym_check_axioms walk_visits
#qsym_check_axioms zero_weight_continuation
#qsym_check_axioms partial_walk_positive
#qsym_check_axioms partial_walk_zero
end AtomicKernelTest
