import QSym.DistributionAtomicMonotone
import QSym.SummationLinearity

/-! Signed observations of increasing atomic approximants. A finite positive
or negative part suffices to split a signed series. If both are infinite,
emissions in the same round can cancel, so the source grouping matters. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal Classical

/-- Total charge of the positive part of a real test. -/
def positiveCharge (k : Weights α) (t : α → ℝ) : ℝ≥0∞ :=
  ∑' a, k a * ENNReal.ofReal (t a)

private theorem ofReal_max_zero (r : ℝ) : ENNReal.ofReal (max r 0) = ENNReal.ofReal r := by
  rcases le_total 0 r with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]

private theorem probe_positivePart {v : ℕ → Option (D α)} {s : ℕ → Model α} {m : Model α}
    (track : Approximates v s) (zero : v 0 = some .zero) (sup : ⨆ n, s n = m) (t : α → ℝ) :
    probe (incrementSeries v) (fun a => some (max (t a) 0)) = finiteReal (positiveCharge m.1 t) := by
  rw [probe_increments_nonnegative track zero _ (fun _ => le_max_right _ _), ← sup, positiveCharge, Prod.fst_iSup]
  simp only [iSup_apply, ofReal_max_zero]

/-- Absolute summation commutes with subtracting two sequences of increments
when at least one sequence has a finite absolute sum. -/
private theorem sum_difference (u w : ℕ → ℝ)
    (finite : (Summation.value norm (some fun n => some (u n))).isSome = true ∨
      (Summation.value norm (some fun n => some (w n))).isSome = true) :
    Summation.value norm (some fun n => some (u n - w n)) =
      Value.add (Summation.value norm (some fun n => some (u n)))
        (Value.mul (some (-1)) (Summation.value norm (some fun n => some (w n)))) := by
  let f (n : ℕ) := some (u n)
  let g (n : ℕ) := some (w n)
  let h (n : ℕ) := Value.mul (some (-1)) (g n)
  have scale : Summation.value norm (some h) = Value.mul (some (-1)) (Summation.value norm (some g)) :=
    SummationLinearity.scale_nonzero (-1 : ℝ) (by norm_num) g
  have rows (n) : some (u n - w n) = Value.add (f n) (h n) := by simp [f, h, g, sub_eq_add_neg, Value.add, Value.mul]
  simp_rw [rows]
  rw [← scale]
  rcases finite with hf | hg
  · exact SummationLinearity.add_known _ Summation.add f h hf
  · apply SummationLinearity.add_known_right _ Summation.add f h
    rw [scale]
    change (Summation.value norm (some g)).isSome = true at hg
    cases e : Summation.value norm (some g) <;> simp_all [Value.mul]

theorem probe_increments_signed {v : ℕ → Option (D α)} {s : ℕ → Model α} {m : Model α}
    (track : Approximates v s) (zero : v 0 = some .zero) (sup : ⨆ n, s n = m) (t : α → ℝ)
    (finite : positiveCharge m.1 t ≠ ∞ ∨ positiveCharge m.1 (fun a => -t a) ≠ ∞) :
    probe (incrementSeries v) (fun a => some (t a)) =
      Value.add (finiteReal (positiveCharge m.1 t))
        (Value.mul (some (-1)) (finiteReal (positiveCharge m.1 (fun a => -t a)))) := by
  choose ds hd hm using track.2
  choose u hu _ _ using fun n => (hm n).1.pairing _ (fun a => le_max_right (t a) 0)
  choose w hw _ _ using fun n => (hm n).1.pairing _ (fun a => le_max_right (-t a) 0)
  have summation (g : α → ℝ) (z : ℕ → ℝ) (hz : ∀ n, integrate (ds n) (fun a => some (g a)) = some (z n)) :
      probe (incrementSeries v) (fun a => some (g a)) =
        Summation.value norm (some fun n => some (z (n+1) - z n)) := by
    have stage (n) : probe (v n) (fun a => some (g a)) = some (z n) := by rw [hd]; exact hz n
    rw [probe_incrementSeries]
    simp only [stage, Value.add, Value.mul, neg_one_mul, sub_eq_add_neg]
  have pos := (summation _ _ hu).symm.trans (probe_positivePart track zero sup t)
  have neg := (summation _ _ hw).symm.trans (probe_positivePart track zero sup (fun a => -t a))
  have split := summation t (fun n => u n - w n) (fun n => (hm n).1.split t (hu n) (hw n))
  have rearrange (n : ℕ) : u (n+1) - w (n+1) - (u n - w n) = (u (n+1) - u n) - (w (n+1) - w n) := by ring
  simp only [rearrange] at split
  rw [split, ← pos, ← neg]
  apply sum_difference
  rw [pos, neg]
  exact finite.imp (fun h => by simp [finiteReal, h]) (fun h => by simp [finiteReal, h])

/-- For a partial signed test, first check every visit. A single infinite
part makes the scalar result undefined, while two finite parts subtract. -/
theorem kernel_partial_signed {body : (ι → Option (D α)) → ι → Option (D α)} {x : ι} {m : Model α}
    (limit : kernelModelAt body x = some m) (t : α → Option ℝ)
    (finite : positiveCharge m.1 (fun a => (t a).getD 0) ≠ ∞ ∨
      positiveCharge m.1 (fun a => -(t a).getD 0) ≠ ∞) :
    probe (kernelSeriesAt body x) t = if ∀ a ∈ m.2, (t a).isSome = true then
      Value.add (finiteReal (positiveCharge m.1 (fun a => (t a).getD 0)))
        (Value.mul (some (-1)) (finiteReal (positiveCharge m.1 (fun a => -(t a).getD 0)))) else none := by
  obtain ⟨s, track, sup⟩ := limitModel_eq_some_iff.mp limit
  rw [kernel_fill limit t, kernelSeriesAt_of_limit limit, probe_increments_signed track rfl sup _ finite]

private theorem stage_visits {s : ℕ → Model α} {m : Model α} (sup : ⨆ n, s n = m) (t : α → Option ℝ) :
    (∀ n a, a ∈ (s n).2 → (t a).isSome = true) ↔ ∀ a ∈ m.2, (t a).isSome = true := by
  rw [← sup, Prod.snd_iSup, Set.iSup_eq_iUnion]
  simp only [Set.mem_iUnion, forall_exists_index]
  exact ⟨fun h a n => h n a, fun h n a => h a n⟩

/-- If the supremum has a finite atomic presentation, it and the series of
source increments agree for every partial signed test. -/
theorem probe_increments_presents {v : ℕ → Option (D α)} {s : ℕ → Model α} {m : Model α} {d : D α}
    (track : Approximates v s) (zero : v 0 = some .zero) (sup : ⨆ n, s n = m) (hd : Presents d m)
    (t : α → Option ℝ) : probe (incrementSeries v) t = integrate d t := by
  rw [probe_increments_fill track t, if_congr (stage_visits sup t) rfl rfl, ← hd.2]
  split
  next present =>
    let g (a : α) := (t a).getD 0
    obtain ⟨p, hp, p0, kp⟩ := hd.1.pairing _ (fun x => le_max_right (g x) 0)
    obtain ⟨q, hq, q0, kq⟩ := hd.1.pairing _ (fun x => le_max_right (-g x) 0)
    simp only [ofReal_max_zero] at kp kq
    change positiveCharge m.1 g = _ at kp
    change positiveCharge m.1 (fun a => -g a) = _ at kq
    rw [hd.1.fill t present, hd.1.split g hp hq, probe_increments_signed track zero sup g (Or.inl (kp ▸ ENNReal.ofReal_ne_top)), kp, kq]
    simp [finiteReal, ENNReal.toReal_ofReal p0, ENNReal.toReal_ofReal q0, Value.add, Value.mul, sub_eq_add_neg]
  next absent =>
    cases eq : integrate d t with
    | none => rfl
    | some z => exact False.elim (absent ((hd.1.defined_probe t).mp (by simp [eq])))

end QSym.Distribution.Atomic
