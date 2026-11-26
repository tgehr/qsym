import QSym.DistributionAtomicSeries
import QSym.DistributionAtomicObservation

/-! A noncontracting retry has a finite signed observation exactly when one
entire round has a defined observation of zero. Different outcomes emitted
in the same round can cancel. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal Classical

private theorem geometric_noncontracting (v : Option ℝ) {r : ℝ} (hr : 1 ≤ r) :
    Summation.value norm (some (fun n : ℕ => Value.mul (some (r^n)) v)) =
      if v = some 0 then some 0 else none := by
  cases v with
  | none => simp [Summation.value, Value.mul]
  | some v =>
    by_cases hv : v = 0
    · simp [hv, Summation.value, Value.mul, summable_zero]
    · have diverges : ¬ Summable (fun n : ℕ => r^n * v) := by
        rw [summable_mul_right_iff hv, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
          abs_of_nonneg (le_trans zero_le_one hr)]
        exact not_lt_of_ge hr
      simp [Summation.value, Value.mul, hv, diverges]

private theorem infinite_retry_weight (m : Model α) {r : ℝ} (hr : 1 ≤ r) (a : α) :
    (strictRetryStep m (ENNReal.ofReal r)).lfp.1 a = ⊤ * m.1 a := by
  have h : 1 ≤ ENNReal.ofReal r := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
  simp [strictRetry_lfp, lfp_retry, tsub_eq_zero_of_le h]

private theorem zero_weights_probe {d : D α} {m : Model α} (hd : Presents d m) (hz : ∀ a, m.1 a = 0)
    (t : α → Option ℝ) : integrate d t = if integrate d t = some 0 then some 0 else none := by
  have scaled : Presents (.scale 0 d) m := by
    refine ⟨?_, (visited_scale _ _).trans hd.2⟩
    simpa [funext hz] using hd.1.scale (r := 0) le_rfl
  have e := (hd.eq_iff scaled).mp rfl t
  change integrate d t = Value.mul (some 0) (integrate d t) at e
  cases h : integrate d t with
  | none => rfl
  | some v => rw [h] at e; simpa [Value.mul] using e

private theorem singleton_retry_probe {d : D α} {m : Model α} (hd : Presents d m) {r : ℝ} (hr : 1 ≤ r)
    {a : α} (hs : (strictRetryStep m (ENNReal.ofReal r)).lfp = infiniteModel a) (t : α → Option ℝ) :
    integrate (infiniteAtom a) t = if integrate d t = some 0 then some 0 else none := by
  have weight (x : α) : ⊤ * m.1 x = ⊤ * atom a x :=
    (infinite_retry_weight m hr x).symm.trans (congrArg (fun m : Model α => m.1 x) hs)
  have pos : m.1 a ≠ 0 := by intro h; simpa [h, atom] using weight a
  have off (x : α) (hx : x ≠ a) : m.1 x = 0 := by
    by_contra h
    simpa [h, hx, atom] using weight x
  let w := (m.1 a).toReal
  have w0 : 0 < w := ENNReal.toReal_pos pos (hd.1.finite_weight a)
  have weights : (fun x => ENNReal.ofReal w * atom a x) = m.1 := by
    funext x
    by_cases hx : x=a
    · subst x; simp [atom, w, ENNReal.ofReal_toReal (hd.1.finite_weight a)]
    · simp [atom, hx, off x hx]
  have hsnd : m.2 = {a} := by simpa [strictRetry_lfp, infiniteModel] using congrArg Prod.snd hs
  have single : Presents (.scale w (.dirac a)) m :=
    ⟨weights ▸ (Represents.dirac a).scale w0.le, by simp [hsnd]⟩
  rw [(hd.eq_iff single).mp rfl t, integrate_infiniteAtom]
  change _ = if Value.mul (some w) (t a) = some 0 then some 0 else none
  cases t a with
  | none => rfl
  | some v => simp [Value.mul, w0.ne']

theorem probe_retry_noncontracting {d : D α} {m : Model α} (hd : Presents d m) {r : ℝ} (hr : 1 ≤ r)
    (t : α → Option ℝ) :
    probe (retryValue (some r) (some d)) t = if integrate d t = some 0 then some 0 else none := by
  let g := strictRetryStep m (ENNReal.ofReal r)
  have r0 := le_trans zero_le_one hr
  rcases realize_cases g.lfp with ⟨e, he, hp⟩ | ⟨a, ha, he⟩ | h
  · have zero (a : α) : m.1 a = 0 := by
      by_contra hn
      exact hp.1.finite_weight a ((infinite_retry_weight m hr a).trans (ENNReal.top_mul hn))
    have same : g.lfp = m := by
      refine Prod.ext ?_ (by simp [g, strictRetry_lfp])
      funext a
      rw [infinite_retry_weight m hr a, zero a, mul_zero]
    rw [retry_eq_chain hd r0, realizeChain_of_some he]
    exact ((hp.eq_iff hd).mp same t).trans (zero_weights_probe hd zero t)
  · rw [retry_eq_chain hd r0, realizeChain_of_some he]
    exact singleton_retry_probe hd hr ha t
  · rw [probe_retry_of_series hd r0 h, geometric_noncontracting _ hr]

/-- A scalar observer that also respects the grouping of countable sums.
Finite linearity alone does not imply this law for a signed series. -/
structure CountableObservation (o : Option (D α) → Option ℝ) : Prop where
  finite : Observation o
  intSum (k : ℤ → Option (D α)) : o (sumValue (some k)) = Summation.value norm (some (fun i => o (k i)))

theorem CountableObservation.mass : CountableObservation (massValue (α := α)) :=
  ⟨Observation.mass, mass_sumValue⟩

private theorem CountableObservation.natSum {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    (k : ℕ → Option (D α)) : o (sumNatValue (some k)) = Summation.value norm (some (fun n => o (k n))) := by
  cases h.finite with
  | absent absent => simp [absent, Summation.value]
  | linear p =>
    have rows : sumNatValue (some k) = sumValue (some (fun i : ℤ => if 0 ≤ i then k i.toNat else zeroValue)) := by
      change some (Presentation.sum (fun i : ℤ => if 0 ≤ i then (k i.toNat).getD .invalid else .zero)) =
        some (.sum (fun i : ℤ => (if 0 ≤ i then k i.toNat else zeroValue).getD .invalid))
      congr 2
      funext i
      split <;> rfl
    rw [rows, h.intSum, ← partialSum_eq_value, ← partialSum_nat]
    congr 1
    funext i
    by_cases hi : 0 ≤ i <;> simp [hi, p.zero]

private theorem CountableObservation.absent {o : Option (D α) → Option ℝ} (h : ∀ d, o d = none) :
    CountableObservation o :=
  ⟨.absent h, fun _ => by simp [h, Summation.value]⟩

private theorem CountableObservation.through {o : Option (D β) → Option ℝ} (h : CountableObservation o)
    (g : Option (D α) → Option (D β)) (finite : Observation (fun d => o (g d)))
    (rows : ∀ k : ℤ → Option (D α), g (sumValue (some k)) = sumValue (some (fun i => g (k i)))) :
    CountableObservation (fun d => o (g d)) :=
  ⟨finite, fun k => (congrArg o (rows k)).trans (h.intSum _)⟩


theorem CountableObservation.weight {o : Option (D α) → Option ℝ} (h : CountableObservation o) (f : Option (α → Option ℝ)) :
    CountableObservation (fun d => o (weightValue f d)) := by
  cases f with
  | none => exact CountableObservation.absent (fun _ => h.finite.missing)
  | some f =>
    exact h.through _ (h.finite.weight (some f)) (fun k => weight_sumValue (some f) _ k (fun _ => rfl))

theorem CountableObservation.bind {o : Option (D β) → Option ℝ} (h : CountableObservation o) (k : Option (α → Option (D β))) :
    CountableObservation (fun d => o (bindValue d k)) := by
  cases k with
  | none => exact CountableObservation.absent (fun d => by cases d <;> exact h.finite.missing)
  | some k =>
    exact h.through _ (h.finite.bind (some k)) (fun f => bind_sumValue f (some k) _ (fun _ => rfl))

theorem CountableObservation.realBind {o : Option (D ℝ) → Option ℝ} (h : CountableObservation o) (k : Option (α → Option (D ℝ))) :
    CountableObservation (fun d => o (GraphFibre.realBindValue d k)) := by
  cases k with
  | none => exact CountableObservation.absent (fun d => by cases d <;> exact h.finite.missing)
  | some k =>
    exact h.through _ (h.finite.realBind (some k)) (fun f => GraphFibre.realBind_sumValue f (some k) _ (fun _ => rfl))

private theorem CountableObservation.at_chain {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    (p : LinearObservation o) (m : Model α) {s : ℕ → Model α} {v : ℕ → Option (D α)} (hs : Approximates v s) :
    o (realizeChain m s) = probe (realizeChain m s) (fun a => o (some (.dirac a))) := by
  rcases realize_cases m with ⟨d, he, hd⟩ | ⟨a, _, ha⟩ | he
  · rw [realizeChain_of_some he]
    exact p.atoms hd.1
  · rw [realizeChain_of_some ha]
    change o (sumValue (some (fun _ : ℤ => some (.dirac a)))) = _
    rw [h.intSum, ← partialSum_eq_value]
    rfl
  · rw [realizeChain, he]
    let t := fun a => o (some (.dirac a))
    let k := fun n => realize (s n)
    change o (incrementSeries k) = probe (incrementSeries k) t
    have stages (n : ℕ) : o (k n) = probe (k n) t := by
      obtain ⟨d, hd, hp⟩ := hs.realize.2 n
      change realize (s n) = some d at hd
      change o (realize (s n)) = probe (realize (s n)) t
      rw [hd]
      exact p.atoms hp.1
    rw [probe_incrementSeries, incrementSeries, h.natSum]
    simp only [p.add, p.scale, stages]

theorem CountableObservation.retry_noncontracting {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {r : Option ℝ} (q : ℚ) (hq : 1 ≤ q) (hr : r = some (q : ℝ)) {seed : Option (D α)} (hs : Admissible seed) :
    o (retryValue r seed) = Binding.guardValue (Value.not (Value.nonzero (o seed))) (some ((0 : ℤ) : ℝ)) := by
  rw [Int.cast_zero, guard_zero]
  cases h.finite with
  | absent absent => rw [absent, absent]; rfl
  | linear p =>
    subst r
    cases seed with
    | none => rw [retry_missing, p.missing]; rfl
    | some d =>
      obtain ⟨m, hd⟩ := hs d rfl
      have q1 : 1 ≤ (q : ℝ) := by exact_mod_cast hq
      have q0 := le_trans zero_le_one q1
      have e := retry_eq_chain hd q0
      rw [e, h.at_chain p _ (hd.approximates_retry q0), ← e, probe_retry_noncontracting hd q1, p.atoms hd.1]

end QSym.Distribution.Atomic
