import QSym.DistributionAtomicKernel
import QSym.DistributionSumFibre

/-! Countable observations of Kleene approximants. Keep the change between two
successive depths in the same summand. For a signed probe, this records which
emissions were combined in each round before absolute summability is tested. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal Classical

def probe (v : Option (D α)) (t : α → Option ℝ) : Option ℝ :=
  v.bind (fun d => integrate d t)

theorem probe_nat_sum (v : ℕ → Option (D α)) (t : α → Option ℝ) :
    probe (sumNatValue (some v)) t = Summation.value norm (some (fun n => probe (v n) t)) := by
  rw [← partialSum_nat]
  change partialSum (fun i : ℤ => integrate (if 0 ≤ i then (v i.toNat).getD .invalid else .zero) t) = _
  congr 1
  funext i
  by_cases hi : 0 ≤ i
  · rw [if_pos hi, if_pos hi]
    cases v i.toNat <;> rfl
  · rw [if_neg hi, if_neg hi]
    rfl

private theorem probe_difference (a b : Option (D α)) (t : α → Option ℝ) :
    probe (addValue b (scaleValue (some (-1)) a)) t =
      Value.add (probe b t) (Value.mul (some (-1)) (probe a t)) := by
  cases b with
  | none => rfl
  | some b =>
    cases a with
    | none =>
      change none = Value.add (integrate b t) none
      cases integrate b t <;> rfl
    | some a => rfl

theorem probe_incrementSeries (v : ℕ → Option (D α)) (t : α → Option ℝ) :
    probe (incrementSeries v) t = Summation.value norm (some (fun n =>
      Value.add (probe (v (n+1)) t) (Value.mul (some (-1)) (probe (v n) t)))) := by
  simp only [incrementSeries, probe_nat_sum, probe_difference]

/-- Replacing any finite stage by a presentation of the same model preserves
every partial signed observation of the countable result. -/
theorem probe_incrementSeries_congr {v w : ℕ → Option (D α)} {s : ℕ → Model α}
    (hv : Approximates v s) (hw : Approximates w s) (t : α → Option ℝ) :
    probe (incrementSeries v) t = probe (incrementSeries w) t := by
  have h (i : ℕ) : probe (v i) t = probe (w i) t := by
    obtain ⟨a, ha, pa⟩ := hv.2 i
    obtain ⟨b, hb, pb⟩ := hw.2 i
    rw [ha, hb]
    exact (pa.eq_iff pb).mp rfl t
  simp only [probe_incrementSeries, h]

theorem Approximates.realize {v : ℕ → Option (D α)} {s : ℕ → Model α} (h : Approximates v s) :
    Approximates (fun n => realize (s n)) s := by
  refine ⟨h.1, fun n => ?_⟩
  obtain ⟨_, _, hd⟩ := h.2 n
  exact realize_presents hd

/-- In the fallback case, every signed observation can use the actual source
approximants, even when their canonical finite representatives are different. -/
theorem probe_realizeChain {m : Model α} {s : ℕ → Model α} {v : ℕ → Option (D α)}
    (hm : realize m = none) (hv : Approximates v s) (t : α → Option ℝ) :
    probe (realizeChain m s) t = probe (incrementSeries v) t := by
  rw [realizeChain, hm]
  exact probe_incrementSeries_congr hv.realize hv t

/-- An atomic function query is defined as a distribution exactly when its
actual finite approximants track an increasing sequence of finite models. -/
def kernelSeriesAt (body : (ι → Option (D α)) → ι → Option (D α)) (x : ι) : Option (D α) :=
  (kernelModelAt body x).bind fun _ => incrementSeries (fun n => iterateKernel body n x)

theorem kernelSeriesAt_of_limit {body : (ι → Option (D α)) → ι → Option (D α)} {x : ι} {m : Model α}
    (h : kernelModelAt body x = some m) :
    kernelSeriesAt body x = incrementSeries (fun n => iterateKernel body n x) := by
  rw [kernelSeriesAt, h, Option.some_bind]

theorem kernelSeriesAt_missing {body : (ι → Option (D α)) → ι → Option (D α)} {x : ι}
    (h : kernelModelAt body x = none) : kernelSeriesAt body x = none := by
  rw [kernelSeriesAt, h, Option.none_bind]

private theorem Represents.puncture {d : D α} {k : Weights α} (h : Represents d k) (a : α) :
    integrate d (fun x => if x = a then none else some 0) =
      if a ∈ visited d then none else some 0 := by
  classical
  induction h with
  | zero => simp [integrate]
  | dirac b => by_cases hb : a=b <;> simp [integrate, hb, eq_comm]
  | @add d _ e _ _ _ ih jh =>
    by_cases hd : a ∈ visited d <;> by_cases he : a ∈ visited e <;> simp [integrate, ih, jh, hd, he, Value.add]
  | @scale r d _ _ _ ih =>
    by_cases hd : a ∈ visited d <;> simp [integrate, ih, hd, Value.mul]

/-- The countable series visits exactly the union of the finite-stage visits.
A zero coefficient never hides an undefined query at a visited outcome. -/
theorem visited_incrementSeries {v : ℕ → Option (D α)} {s : ℕ → Model α} (h : Approximates v s) (a : α) :
    a ∈ visited ((incrementSeries v).getD .invalid) ↔ ∃ n, a ∈ (s n).2 := by
  classical
  let t : α → Option ℝ := fun x => if x = a then none else some 0
  have stage (n : ℕ) : probe (v n) t = if a ∈ (s n).2 then none else some 0 := by
    obtain ⟨d, hd, hm, hv⟩ := h.2 n
    rw [hd, ← hv]
    exact hm.puncture a
  change probe (incrementSeries v) t = none ↔ _
  rw [probe_incrementSeries]
  constructor
  · intro hn
    by_contra missing
    push_neg at missing
    have hz : (fun n : ℕ => Value.add (probe (v (n+1)) t) (Value.mul (some (-1)) (probe (v n) t))) =
        fun _ => some 0 := by funext n; simp [stage, missing, Value.add, Value.mul]
    rw [hz, Summation.zero norm norm_zero] at hn
    contradiction
  · rintro ⟨n, hn⟩
    apply Summation.undefined_term norm _ n
    rw [stage n, if_pos hn, stage (n+1), if_pos (h.1 (Nat.le_succ n) |>.2 hn)]
    rfl

private theorem nonnegative_sum_zero (a : ℕ → ℝ) (hn : ∀ n, 0 ≤ a n) :
    Summation.value norm (some (fun i => some (a i))) = some 0 ↔ ∀ n, a n = 0 := by
  classical
  constructor
  · intro h
    simp only [Summation.value, Option.some_bind, Option.isSome_some, forall_const, true_and, Option.getD_some] at h
    split at h
    next hs =>
      have hz := Option.some.inj h
      intro n
      exact le_antisymm (hz ▸ hs.2.le_tsum n (fun i _ => hn i)) (hn n)
    next => contradiction
  · intro h
    simpa only [h] using (Summation.zero (ι := ℕ) (α := ℝ) norm norm_zero)

private theorem guard_zero (c : Option ℝ) :
    Binding.guardValue (Value.not (Value.nonzero c)) (some (0 : ℝ)) = if c = some 0 then some 0 else none := by
  classical
  cases c with
  | none => rfl
  | some z => by_cases hz : z=0 <;> simp [hz, Binding.guardValue, Value.not, Value.nonzero]

/-- On real outcomes the pointwise density sees exactly the positive limiting
charge. This includes divergent charges and zero-weight visits. -/
theorem density_incrementSeries {v : ℕ → Option (D ℝ)} {s : ℕ → Model ℝ} (h : Approximates v s)
    (x : ℝ) (h0 : (s 0).1 x = 0) :
    densityAtValue (incrementSeries v) (some x) = if (⨆ n, (s n).1 x) = 0 then some 0 else none := by
  classical
  choose d hd hm using h.2
  choose c hc hk hf using fun n => (hm n).1.realFibreAt x
  have mono (n : ℕ) : c n ≤ c (n+1) := by
    apply (ENNReal.ofReal_le_ofReal_iff (hc _)).mp
    rw [← hk, ← hk]
    exact (h.1 (Nat.le_succ n)).1 x
  have row (n : ℕ) : FibreCertificate (addValue (v (n+1)) (scaleValue (some (-1)) (v n))) (some x)
      (some (c (n+1) - c n)) (some 0) := by
    simp [hd, FibreCertificate, addValue, scaleValue, realFibre, hf, RealDensityFibre.add,
      RealDensityFibre.scale, Value.add, Value.mul, sub_eq_add_neg]
  have cz (n : ℕ) : (s n).1 x = 0 ↔ c n = 0 := by
    rw [hk, ENNReal.ofReal_eq_zero]
    exact ⟨fun he => le_antisymm he (hc _), fun he => he.le⟩
  have allZero : (∀ n, c (n+1) - c n = 0) ↔ (⨆ n, (s n).1 x) = 0 := by
    constructor
    · intro same
      apply le_antisymm (iSup_le fun n => ?_) (zero_le _)
      have cn : c n = 0 := by
        induction n with
        | zero => exact (cz 0).mp h0
        | succ n ih => exact (sub_eq_zero.mp (same n)).trans ih
      exact ((cz n).mpr cn).le
    · intro hs n
      have at_zero (i : ℕ) := (cz i).mp (le_antisymm (le_iSup (fun j => (s j).1 x) i |>.trans hs.le) (zero_le _))
      rw [at_zero, at_zero, sub_self]
  rw [incrementSeries, FibreCertificate.extract_nat_sum row, Summation.zero norm norm_zero, guard_zero]
  have law := (nonnegative_sum_zero _ (fun n => sub_nonneg.mpr (mono n))).trans allZero
  by_cases hz : (⨆ n, (s n).1 x) = 0
  · rw [if_pos (law.mpr hz), if_pos hz]
  · rw [if_neg (mt law.mp hz), if_neg hz]

theorem kernelSeriesAt_density {body : (ι → Option (D ℝ)) → ι → Option (D ℝ)} {x : ι} {m : Model ℝ}
    (h : kernelModelAt body x = some m) (y : ℝ) :
    densityAtValue (kernelSeriesAt body x) (some y) = if m.1 y = 0 then some 0 else none := by
  obtain ⟨s, hs, hm⟩ := limitModel_eq_some_iff.mp h
  obtain ⟨d, hd, hp⟩ := hs.2 0
  have e : (Presentation.zero : D ℝ) = d := Option.some.inj hd
  have bot : Presents (.zero : D ℝ) (⊥ : Model ℝ) := ⟨Represents.zero, visited_zero⟩
  have z : s 0 = ⊥ := (hp.eq_iff bot).mpr (fun _ => e ▸ rfl)
  rw [kernelSeriesAt_of_limit h, density_incrementSeries hs y (by rw [z]; rfl), ← hm, Prod.fst_iSup, iSup_apply]

theorem kernelSeriesAt_visited {body : (ι → Option (D α)) → ι → Option (D α)} {x : ι} {m : Model α}
    (h : kernelModelAt body x = some m) :
    visited ((kernelSeriesAt body x).getD .invalid) = m.2 := by
  obtain ⟨s, hs, hm⟩ := limitModel_eq_some_iff.mp h
  ext y
  rw [kernelSeriesAt_of_limit h, visited_incrementSeries hs, ← hm, Prod.snd_iSup, Set.iSup_eq_iUnion,
    Set.mem_iUnion]

theorem Presents.approximates_retry {d : D α} {m : Model α} (hd : Presents d m) {r : ℝ} (hr : 0 ≤ r) :
    Approximates (fun n => some (approximate d r n)) (fun n => (strictRetryStep m (ENNReal.ofReal r))^[n] ⊥) := by
  let g := strictRetryStep m (ENNReal.ofReal r)
  refine ⟨g.monotone.monotone_iterate_of_le_map bot_le, fun n => ⟨_, rfl, ?_⟩⟩
  induction n with
  | zero => exact ⟨Represents.zero, visited_zero⟩
  | succ n ih =>
    change Presents (approximate d r (n+1)) (g^[n+1] ⊥)
    rw [Function.iterate_succ_apply']
    exact ⟨hd.1.add (ih.1.scale hr),
      (visited_add _ _).trans (congrArg₂ (· ∪ ·) hd.2 ((visited_scale _ _).trans ih.2))⟩

/-- For a retry, the per-depth differences recover the ordinary weighted series
of seed observations. This also holds for negative and missing observations. -/
theorem probe_retry_increments (d : D α) (r : ℝ) (t : α → Option ℝ) :
    probe (incrementSeries (fun n => some (approximate d r n))) t =
      Summation.value norm (some (fun n : ℕ => Value.mul (some (r^n)) (integrate d t))) := by
  rw [probe_incrementSeries]
  congr 1
  congr 1
  funext n
  simp only [probe, Option.some_bind, integrate_approximate]
  cases hv : integrate d t with
  | none => rfl
  | some v =>
    cases n with
    | zero => simp [approximate, integrate, Value.add, Value.mul]
    | succ n =>
      rw [integrate_approximate, hv, Finset.sum_range_succ _ (n+1)]
      simp only [Value.add, Value.mul, Option.some.injEq]
      ring

theorem probe_retry_of_series {d : D α} {m : Model α} (hd : Presents d m) {r : ℝ} (hr : 0 ≤ r)
    (h : realize (strictRetryStep m (ENNReal.ofReal r)).lfp = none) (t : α → Option ℝ) :
    probe (retryValue (some r) (some d)) t =
      Summation.value norm (some (fun n : ℕ => Value.mul (some (r^n)) (integrate d t))) := by
  rw [retry_eq_chain hd hr, probe_realizeChain h (hd.approximates_retry hr), probe_retry_increments]

theorem probe_retry_one (d : D α) (t : α → Option ℝ) :
    probe (incrementSeries (fun n => some (approximate d 1 n))) t =
      if integrate d t = some 0 then some 0 else none := by
  classical
  rw [probe_retry_increments]
  cases hv : integrate d t with
  | none => simp [Summation.value, Value.mul]
  | some v => by_cases z : v=0 <;> simp [Summation.value, Value.mul, z, summable_const_iff]

end QSym.Distribution.Atomic
