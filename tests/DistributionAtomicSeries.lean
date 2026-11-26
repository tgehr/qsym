import QSym.DistributionAtomicSeries
import QSym.AxiomCheck

noncomputable section
open scoped ENNReal
open QSym.Distribution QSym.Distribution.Atomic

namespace AtomicSeriesTest

-- Each round emits both atoms before recursively starting another round.
private def seed : D ℝ := .add (.dirac 0) (.dirac 2)
private def model : Model ℝ := (fun x => atom 0 x + atom 2 x, {0} ∪ {2})
private theorem seed_presents : Presents seed model :=
  ⟨(Represents.dirac 0).add (Represents.dirac 2), by simp [seed, model]⟩

private def body (k : Unit → Option (D ℝ)) (_ : Unit) := addValue (some seed) (scaleValue (some 1) (k ()))
private def step := kernelStep (fun _ : Unit => model) (fun _ => 1) id

private theorem source_limit : kernelModelAt body () = some (step.lfp ()) := by
  apply kernelModelAt_on body (fun _ => model) (fun _ => 1) id Set.univ
    (fun _ _ => Set.mem_univ _) _ (Set.mem_univ ())
  rintro ⟨⟩ _ k d m hk hd
  refine ⟨.add seed (.scale 1 d), by simp [body, id] at hk ⊢; rw [hk]; rfl, ?_, ?_⟩
  · simpa only [ENNReal.ofReal_one] using seed_presents.1.add (hd.1.scale zero_le_one)
  · simp [strictRetryStep, seed_presents.2, hd.2]

private theorem actual_stages (n : ℕ) : iterateKernel body n () = some (approximate seed 1 n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterateKernel, body, ih, approximate, addValue, scaleValue]

theorem mixed_signed (t : ℝ → Option ℝ) :
    probe (kernelSeriesAt body ()) t = if QSym.Value.add (t 0) (t 2) = some 0 then some 0 else none := by
  rw [kernelSeriesAt_of_limit source_limit, funext actual_stages, probe_retry_one]
  rfl

theorem cancellation :
    probe (kernelSeriesAt body ()) (fun x => some (if x=0 then 1 else -1)) = some 0 := by
  rw [mixed_signed]
  norm_num [QSym.Value.add]

theorem divergent_mass : massValue (kernelSeriesAt body ()) = none := by
  change probe _ (fun _ => some 1) = none
  rw [mixed_signed]
  norm_num [QSym.Value.add]

theorem missing_probe : probe (kernelSeriesAt body ()) (fun x => if x=2 then none else some 0) = none := by
  rw [mixed_signed]
  norm_num [QSym.Value.add]
  simp

theorem density_off_atoms : densityAtValue (kernelSeriesAt body ()) (some 1) = some 0 := by
  rw [kernelSeriesAt_density source_limit, step, kernel_lfp_weight]
  norm_num [reachWeight_const, model, atom]

theorem density_at_atom : densityAtValue (kernelSeriesAt body ()) (some 0) = none := by
  rw [kernelSeriesAt_density source_limit, step, kernel_lfp_weight]
  apply if_neg
  apply ne_of_gt
  apply lt_of_lt_of_le _ (ENNReal.le_tsum 0)
  norm_num [reachWeight, model, atom]

private def direct := fixedValue (some (fun d : D ℝ => addValue (some seed) (some d)))

-- Check the same grouped signed observation through the ordinary distribution
-- fixed point; equality of the two final weights alone cannot establish it.
theorem direct_agrees (t : ℝ → Option ℝ) : probe direct t = probe (kernelSeriesAt body ()) t := by
  have admissible : Admissible (some seed) := fun _ h => by cases h; exact ⟨model, seed_presents⟩
  have loop : direct = retryValue (some 1) (some seed) :=
    fixed_add_tail false 1 (by norm_num) admissible Tail.self (fun _ => rfl)
  let g := strictRetryStep model (ENNReal.ofReal (1 : ℝ))
  have missing : realize g.lfp = none := by
    apply realize_eq_none_of_infinite_visits (a := (0 : ℝ)) (b := 0) (c := 2)
    · simp [g, strictRetry_lfp, lfp_retry, model, atom]
    · simp [g, strictRetry_lfp, model]
    · simp [g, strictRetry_lfp, model]
    · norm_num
  rw [loop, retry_eq_chain seed_presents zero_le_one,
    probe_realizeChain missing (seed_presents.approximates_retry zero_le_one), probe_retry_one, mixed_signed]
  rfl

theorem direct_cancellation : probe direct (fun x => some (if x=0 then 1 else -1)) = some 0 :=
  (direct_agrees _).trans cancellation

theorem direct_mass : massValue direct = none := (direct_agrees _).trans divergent_mass

#qsym_check_axioms density_realizeChain
#qsym_check_axioms density_retry_seed
#qsym_check_axioms retry_isSome
#qsym_check_axioms probe_retry_of_series
#qsym_check_axioms direct_agrees
#qsym_check_axioms direct_cancellation
#qsym_check_axioms direct_mass
#qsym_check_axioms probe_incrementSeries_congr
#qsym_check_axioms visited_incrementSeries
#qsym_check_axioms density_incrementSeries
#qsym_check_axioms kernelSeriesAt_density
#qsym_check_axioms kernelSeriesAt_visited
#qsym_check_axioms probe_retry_increments
#qsym_check_axioms mixed_signed
#qsym_check_axioms cancellation
#qsym_check_axioms divergent_mass
#qsym_check_axioms missing_probe
#qsym_check_axioms density_off_atoms
#qsym_check_axioms density_at_atom
end AtomicSeriesTest
