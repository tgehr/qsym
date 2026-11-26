import QSym.DistributionAtomicOrbit
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

private def emission (i : ℕ) := scaleValue (some (1/2)) (diracValue (some i))

-- This checks the signed scalar series of the actual recursive source, beyond
-- the weight of each atom considered separately.
theorem walk_all_probes (t : ℕ → Option ℝ) :
    probe (kernelSeriesAt walk 0) t = QSym.Summation.value norm
      (some (fun n : ℕ => QSym.Value.mul (some ((1/2 : ℝ)^(n+1))) (t n))) := by
  have h := probe_kernel_orbit (b := emission) (r := fun _ => 1/2) (next := Nat.succ) (walk_limit 0) t
  change probe (kernelSeriesAt (orbitBody emission (fun _ => 1/2) Nat.succ) 0) t = _
  rw [h, orbitSeries, probe_nat_sum]
  congr 1
  congr 1
  funext n
  rw [probe_scale, reachWeight_const, succ_iterate_zero, emission, probe_scale, pow_succ]
  change QSym.Value.mul _ (QSym.Value.mul _ (t n)) = _
  cases t n <;> simp [QSym.Value.mul, mul_assoc]

private theorem half_geometric (r : ℝ) (hr : ‖r‖ < 1) :
    QSym.Summation.value norm (some (fun n : ℕ => some ((1/2 : ℝ)*r^n))) = some ((1/2)*(1-r)⁻¹) := by
  have h := (hasSum_geometric_of_norm_lt_one hr).mul_left (1/2 : ℝ)
  exact QSym.Summation.of_hasSum norm _ _ _ (fun _ => rfl) h.summable.norm h

theorem walk_mass : massValue (kernelSeriesAt walk 0) = some 1 := by
  change probe _ (fun _ => some 1) = _
  rw [walk_all_probes]
  have row (n : ℕ) : QSym.Value.mul (some ((1/2 : ℝ)^(n+1))) (some 1) = some ((1/2)*(1/2)^n) := by
    simp [QSym.Value.mul, pow_succ, mul_comm]
  simp only [row]
  rw [half_geometric _ (by norm_num [Real.norm_eq_abs])]
  norm_num

theorem walk_alternating : probe (kernelSeriesAt walk 0) (fun n => some ((-1 : ℝ)^n)) = some (1/3) := by
  rw [walk_all_probes]
  have row (n : ℕ) : QSym.Value.mul (some ((1/2 : ℝ)^(n+1))) (some ((-1 : ℝ)^n)) =
      some ((1/2)*(-1/2)^n) := by
    rw [show (-1/2 : ℝ) = (1/2)*(-1) by norm_num, mul_pow, pow_succ]
    simp [QSym.Value.mul, mul_comm, mul_left_comm, mul_assoc]
  simp only [row]
  rw [half_geometric _ (by norm_num [Real.norm_eq_abs])]
  norm_num

private theorem emission_limit (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) :
    kernelModelAt (orbitBody emission r Nat.succ) 0 =
      some ((kernelStep seed (fun n => ENNReal.ofReal (r n)) Nat.succ).lfp 0) := by
  apply orbit_limit_on emission r Nat.succ seed Set.univ (fun _ _ => Set.mem_univ _) _ (fun i _ => hr i) (Set.mem_univ _)
  intro i _
  exact ⟨_, rfl, (Represents.dirac i).scale (r := 1/2) (by norm_num), by simp [seed]⟩

theorem missing_after_zero :
    probe (kernelSeriesAt (orbitBody emission (fun _ => 0) Nat.succ) 0) (fun n => if n=1 then none else some 0) = none := by
  rw [probe_kernel_orbit (emission_limit _ (fun _ => le_rfl)), orbitSeries, probe_nat_sum]
  apply QSym.Summation.undefined_term norm _ 1
  rfl

theorem changing_rates :
    let r : ℕ → ℝ := fun i => if i=0 then 1/2 else 1/3
    probe (kernelSeriesAt (orbitBody emission r Nat.succ) 0) (fun n => some (if n=2 then 1 else 0)) = some (1/12) := by
  intro r
  have hr (i : ℕ) : 0 ≤ r i := by dsimp [r]; split <;> norm_num
  rw [probe_kernel_orbit (emission_limit r hr), orbitSeries, probe_nat_sum]
  have row (n : ℕ) : probe (scaleValue (some (reachWeight r Nat.succ n 0)) (emission (Nat.succ^[n] 0)))
      (fun i => some (if i=2 then 1 else 0)) = (if n=2 then some (1/12) else some 0) := by
    rw [probe_scale, succ_iterate_zero, emission, probe_scale]
    by_cases h : n=2
    · subst n; norm_num [reachWeight, r, probe, diracValue, integrate, QSym.Value.mul]
    · simp [h, probe, diracValue, integrate, QSym.Value.mul]
  simp_rw [row]
  exact QSym.Summation.delta norm norm_zero _ _

#qsym_check_axioms orbit_limit_on
#qsym_check_axioms probe_kernel_orbit
#qsym_check_axioms walk_all_probes
#qsym_check_axioms walk_mass
#qsym_check_axioms walk_alternating
#qsym_check_axioms missing_after_zero
#qsym_check_axioms changing_rates
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
