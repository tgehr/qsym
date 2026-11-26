import QSym.DistributionAtomicSeries

/-! A state-dependent retry emits at the current state, then continues with
a state-dependent weight. A signed probe of its limit is the ordinary
absolutely convergent sum over that orbit. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal Classical
variable {ι α : Type}

def orbitBody (b : ι → Option (D α)) (r : ι → ℝ) (next : ι → ι)
    (k : ι → Option (D α)) (x : ι) : Option (D α) :=
  addValue (b x) (scaleValue (some (r x)) (k (next x)))

def orbitSeries (b : ι → Option (D α)) (r : ι → ℝ) (next : ι → ι) (x : ι) : Option (D α) :=
  sumNatValue (some (fun n => scaleValue (some (reachWeight r next n x)) (b (next^[n] x))))

private theorem stage_probe (b : ι → Option (D α)) (r : ι → ℝ) (next : ι → ι)
    (t : α → Option ℝ) (n : ℕ) (x : ι)
    (ok : ∀ i < n, (probe (b (next^[i] x)) t).isSome = true) :
    probe (iterateKernel (orbitBody b r next) n x) t =
      some (∑ i ∈ Finset.range n, reachWeight r next i x * (probe (b (next^[i] x)) t).getD 0) := by
  induction n generalizing x with
  | zero => simp [iterateKernel, probe, integrate]
  | succ n ih =>
    have first : probe (b x) t = some ((probe (b x) t).getD 0) := by
      have h := ok 0 (Nat.zero_lt_succ n)
      change (probe (b x) t).isSome = true at h
      cases e : probe (b x) t <;> simp_all
    have tail (i : ℕ) (hi : i<n) : (probe (b (next^[i] (next x))) t).isSome = true := by
      simpa only [Function.iterate_succ_apply] using ok (i+1) (Nat.succ_lt_succ hi)
    rw [iterateKernel, orbitBody, probe_add, probe_scale, ih (next x) tail, first, Finset.sum_range_succ']
    simp [Value.add, Value.mul, reachWeight, Function.iterate_succ_apply, Finset.mul_sum, mul_assoc, add_comm]

private theorem missing_stage (b : ι → Option (D α)) (r : ι → ℝ) (next : ι → ι)
    (t : α → Option ℝ) (n : ℕ) (x : ι) (missing : probe (b (next^[n] x)) t = none) :
    probe (iterateKernel (orbitBody b r next) (n+1) x) t = none := by
  induction n generalizing x with
  | zero =>
    change probe (b x) t = none at missing
    rw [iterateKernel, orbitBody, probe_add, missing]
    rfl
  | succ n ih =>
    rw [iterateKernel, orbitBody, probe_add, probe_scale, ih (next x) (by simpa only [Function.iterate_succ_apply] using missing)]
    cases probe (b x) t <;> rfl

theorem probe_orbit_increments (b : ι → Option (D α)) (r : ι → ℝ) (next : ι → ι) (x : ι) (t : α → Option ℝ) :
    probe (incrementSeries (fun n => iterateKernel (orbitBody b r next) n x)) t = probe (orbitSeries b r next x) t := by
  rw [probe_incrementSeries, orbitSeries, probe_nat_sum]
  by_cases defined : ∀ n : ℕ, (probe (b (next^[n] x)) t).isSome = true
  · congr 1
    congr 1
    funext n
    have stage (i : ℕ) := stage_probe b r next t i x (fun j _ => defined j)
    have leaf : probe (b (next^[n] x)) t = some ((probe (b (next^[n] x)) t).getD 0) := by
      have h := defined n
      cases e : probe (b (next^[n] x)) t <;> simp_all
    rw [stage, stage, Finset.sum_range_succ, probe_scale, leaf]
    simp only [Value.add, Value.mul, Option.getD_some, Option.some.injEq]
    ring
  · push_neg at defined
    obtain ⟨n, hn⟩ := defined
    have missing : probe (b (next^[n] x)) t = none := by simpa using hn
    trans none
    · apply Summation.undefined_term norm _ n
      rw [missing_stage b r next t n x missing]
      rfl
    · symm
      apply Summation.undefined_term norm _ n
      rw [probe_scale, missing]
      rfl

/-- A finite nonnegative seed at every reachable state certifies the source
fixed point. Only the reached seeds must be present and the reached rates nonnegative. -/
theorem orbit_limit_on (b : ι → Option (D α)) (r : ι → ℝ) (next : ι → ι) (m : Kernel ι α) (states : Set ι)
    (closed : Set.MapsTo next states states) (seed : ∀ x ∈ states, ∃ d, b x = some d ∧ Presents d (m x))
    (rate : ∀ x ∈ states, 0 ≤ r x) {x : ι} (hx : x ∈ states) :
    kernelModelAt (orbitBody b r next) x = some ((kernelStep m (fun a => ENNReal.ofReal (r a)) next).lfp x) := by
  apply kernelModelAt_on _ m _ next states closed _ hx
  intro a ha k d v hk hd
  obtain ⟨e, he, hp⟩ := seed a ha
  refine ⟨.add e (.scale (r a) d), by rw [orbitBody, he, hk]; rfl, hp.1.add (hd.1.scale (rate a ha)), ?_⟩
  exact (visited_add _ _).trans (congrArg₂ (· ∪ ·) hp.2 ((visited_scale _ _).trans hd.2))

theorem probe_kernel_orbit {b : ι → Option (D α)} {r : ι → ℝ} {next : ι → ι} {x : ι} {m : Model α}
    (h : kernelModelAt (orbitBody b r next) x = some m) (t : α → Option ℝ) :
    probe (kernelSeriesAt (orbitBody b r next) x) t = probe (orbitSeries b r next x) t := by
  rw [kernelSeriesAt_of_limit h, probe_orbit_increments]

end QSym.Distribution.Atomic
