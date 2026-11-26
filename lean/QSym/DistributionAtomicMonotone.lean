import QSym.DistributionAtomicSeries
import Mathlib.Data.ENNReal.BigOperators

/-! Monotone convergence for nonnegative tests on increasing atomic source
approximants. Missing values are observed at every visited atom, including
atoms of zero limiting weight. A finite answer is returned exactly when the
integral with respect to the limiting weights is finite. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal Classical

def finiteReal (m : ℝ≥0∞) : Option ℝ := if m = ∞ then none else some m.toReal

private theorem positive_increments (u : ℕ → ℝ) (mono : Monotone u) (zero : u 0 = 0) :
    Summation.value norm (some (fun n : ℕ => some (u (n+1) - u n))) =
      finiteReal (⨆ n, ENNReal.ofReal (u n)) := by
  let d := fun n => u (n+1)-u n
  have pos (n) : 0 ≤ d n := sub_nonneg.mpr (mono (Nat.le_succ n))
  have nn (n) : 0 ≤ u n := zero ▸ mono (Nat.zero_le n)
  have total : ∑' n, ENNReal.ofReal (d n) = ⨆ n, ENNReal.ofReal (u n) := by
    rw [ENNReal.tsum_eq_iSup_nat]
    congr 1
    funext n
    induction n with
    | zero => simp [zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, ← ENNReal.ofReal_add (nn n) (pos n)]
      congr 1
      dsimp [d]; ring
  rw [← total, finiteReal]
  split
  next inf =>
    have no : ¬ Summable d := fun h => ENNReal.ofReal_ne_top
      ((ENNReal.ofReal_tsum_of_nonneg pos h).trans inf)
    simpa [Summation.value, d] using (fun _ => no : (Summable fun n => |d n|) → ¬ Summable d)
  next finite =>
    have hs := ENNReal.hasSum_toReal finite
    rw [← ENNReal.tsum_toReal_eq (f := fun n => ENNReal.ofReal (d n)) (fun _ => ENNReal.ofReal_ne_top)] at hs
    simp only [ENNReal.toReal_ofReal (pos _)] at hs
    apply Summation.of_hasSum norm _ d _ (fun _ => rfl) _ hs
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pos _)] using hs.summable

private theorem tsum_iSup_mono (f : α → ℕ → ℝ≥0∞) (h : ∀ a, Monotone (f a)) :
    ∑' a, ⨆ n, f a n = ⨆ n, ∑' a, f a n := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone h]
  exact iSup_comm

/-- Total nonnegative tests pair with the supremum of the finite source
weights. No assumption about countability of the outcome type is required. -/
theorem probe_increments_nonnegative {v : ℕ → Option (D α)} {s : ℕ → Model α}
    (track : Approximates v s) (zero : v 0 = some .zero) (t : α → ℝ) (ht : ∀ a, 0 ≤ t a) :
    probe (incrementSeries v) (fun a => some (t a)) =
      finiteReal (∑' a, (⨆ n, (s n).1 a) * ENNReal.ofReal (t a)) := by
  choose ds hd hm using track.2
  choose u hu positive charge using fun n => (hm n).1.pairing t ht
  have stage (n) : probe (v n) (fun a => some (t a)) = some (u n) := by rw [hd]; exact hu n
  have initial : u 0 = 0 := Option.some.inj (by simpa [zero, probe, integrate] using (stage 0).symm)
  have mono : Monotone u := by
    intro i j hij
    apply (ENNReal.ofReal_le_ofReal_iff (positive j)).mp
    rw [← charge i, ← charge j]
    exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right' ((track.1 hij).1 a) _
  have total : (∑' a, (⨆ n, (s n).1 a) * ENNReal.ofReal (t a)) = ⨆ n, ENNReal.ofReal (u n) := by
    simp_rw [ENNReal.iSup_mul]
    rw [tsum_iSup_mono (fun a n => (s n).1 a * ENNReal.ofReal (t a))
      (fun a i j hij => mul_le_mul_right' ((track.1 hij).1 a) _)]
    simp_rw [charge]
  rw [probe_incrementSeries, total, ← positive_increments u mono initial]
  congr 2
  funext n
  simp [stage, Value.mul, Value.add, sub_eq_add_neg]

theorem kernel_nonnegative {body : (ι → Option (D α)) → ι → Option (D α)} {x : ι} {m : Model α}
    (limit : kernelModelAt body x = some m) (t : α → ℝ) (ht : ∀ a, 0 ≤ t a) :
    probe (kernelSeriesAt body x) (fun a => some (t a)) = finiteReal (∑' a, m.1 a * ENNReal.ofReal (t a)) := by
  obtain ⟨s, track, sup⟩ := limitModel_eq_some_iff.mp limit
  rw [kernelSeriesAt_of_limit limit, probe_increments_nonnegative track rfl _ ht, ← sup, Prod.fst_iSup]
  simp_rw [iSup_apply]

/-- Every visit must have a value, even in a zero-weight branch. On that
domain filling the test elsewhere gives the same signed observation. -/
theorem probe_increments_fill {v : ℕ → Option (D α)} {s : ℕ → Model α}
    (track : Approximates v s) (t : α → Option ℝ) :
    probe (incrementSeries v) t = if ∀ n a, a ∈ (s n).2 → (t a).isSome = true
      then probe (incrementSeries v) (fun a => some ((t a).getD 0)) else none := by
  choose ds hd hm using track.2
  split
  next ok =>
    rw [probe_incrementSeries, probe_incrementSeries]
    have stage (n) : probe (v n) t = probe (v n) (fun a => some ((t a).getD 0)) := by
      rw [hd]; apply (hm n).1.fill
      intro a ha
      exact ok n a ((hm n).2 ▸ ha)
    simp_rw [stage]
  next bad =>
    rw [probe_incrementSeries]
    push_neg at bad
    obtain ⟨n, a, visited, missing⟩ := bad
    have no : probe (v n) t = none := by
      rw [hd]
      change integrate (ds n) t = none
      cases e : integrate (ds n) t with
      | none => rfl
      | some z => exact False.elim (missing (((hm n).1.defined_probe t).mp (by simp [e]) a ((hm n).2.symm ▸ visited)))
    apply Summation.undefined_term norm _ n
    rw [no]
    cases probe (v (n+1)) t <;> rfl

theorem kernel_fill {body : (ι → Option (D α)) → ι → Option (D α)} {x : ι} {m : Model α}
    (limit : kernelModelAt body x = some m) (t : α → Option ℝ) :
    probe (kernelSeriesAt body x) t = if ∀ a ∈ m.2, (t a).isSome = true
      then probe (kernelSeriesAt body x) (fun a => some ((t a).getD 0)) else none := by
  obtain ⟨s, track, sup⟩ := limitModel_eq_some_iff.mp limit
  have visits : m.2 = ⋃ n, (s n).2 := by rw [← sup, Prod.snd_iSup, Set.iSup_eq_iUnion]
  rw [kernelSeriesAt_of_limit limit, probe_increments_fill track t, visits]
  congr 1
  ext
  simp only [Set.mem_iUnion, forall_exists_index]
  exact ⟨fun h a n => h n a, fun h n a => h a n⟩

theorem kernel_partial_nonnegative {body : (ι → Option (D α)) → ι → Option (D α)} {x : ι} {m : Model α}
    (limit : kernelModelAt body x = some m) (t : α → Option ℝ) (ht : ∀ a, 0 ≤ (t a).getD 0) :
    probe (kernelSeriesAt body x) t = if ∀ a ∈ m.2, (t a).isSome = true
      then finiteReal (∑' a, m.1 a * ENNReal.ofReal ((t a).getD 0)) else none := by
  rw [kernel_fill limit t, kernel_nonnegative limit _ ht]

theorem kernel_mass {body : (ι → Option (D α)) → ι → Option (D α)} {x : ι} {m : Model α}
    (limit : kernelModelAt body x = some m) :
    massValue (kernelSeriesAt body x) = finiteReal (∑' a, m.1 a) := by
  simpa [massValue, probe] using kernel_nonnegative limit (fun _ => 1) (fun _ => zero_le_one)

end QSym.Distribution.Atomic
