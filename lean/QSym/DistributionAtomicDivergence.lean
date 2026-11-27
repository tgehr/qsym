import QSym.DistributionAtomicSeries
import QSym.DistributionAtomicObservation

/-! A noncontracting retry has a finite signed observation exactly when one
entire round has a defined observation of zero. Different outcomes emitted
in the same round can cancel. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal Classical

theorem geometric_noncontracting (v : Option ℝ) {r : ℝ} (hr : 1 ≤ r) :
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

/-- The total mass of a direct retry at any real rate. At a noncontracting
rate a zero-mass round still has a finite sum. -/
theorem mass_retry_cases (r : ℝ) {seed : Option (D α)} (hs : Admissible seed) :
    massValue (retryValue (some r) seed) = if 0 ≤ r then
      if r < 1 then Value.mul (some (1-r)⁻¹) (massValue seed)
      else if massValue seed = some 0 then some 0 else none
    else none := by
  by_cases h0 : 0 ≤ r
  · rw [if_pos h0]
    by_cases h1 : r < 1
    · rw [if_pos h1, ← mass_scaleValue]
      exact observe_retry_real (fun d => integrate d (fun _ => some 1))
        (fun hd he => (hd.eq_iff he).mp rfl _) h0 h1 hs
    · rw [if_neg h1]
      cases seed with
      | none => rfl
      | some d =>
        obtain ⟨m, hd⟩ := hs d rfl
        exact probe_retry_noncontracting hd (le_of_not_gt h1) (fun _ => some 1)
  · rw [if_neg h0, retry_negative (lt_of_not_ge h0)]
    rfl

theorem mass_retry_parameter_dirac (r : Option ℝ) (p : Option α) :
    massValue (retryValue r (diracValue p)) =
      Binding.guardValue (Value.and (Value.le (some ((0 : ℚ) : ℝ)) r)
        (Value.lt r (some ((1 : ℚ) : ℝ))))
        (p.bind fun _ => Value.inv (Value.add (some ((1 : ℚ) : ℝ))
          (Value.mul (some ((-1 : ℚ) : ℝ)) r))) := by
  cases r with
  | none => rfl
  | some r =>
    rw [mass_retry_cases r (admissible_dirac p), mass_diracValue]
    by_cases h0 : 0 ≤ r
    · by_cases h1 : r < 1
      · have nz : 1 + -r ≠ 0 := by linarith
        cases p <;> simp [h0, h1, nz, sub_eq_add_neg, Binding.guardValue, Value.le, Value.lt,
          Value.and, Value.inv, Value.add, Value.mul]
      · cases p <;> simp [h0, h1, Binding.guardValue, Value.le, Value.lt, Value.and]
    · simp [h0, Binding.guardValue, Value.le, Value.and]

/-- A scalar observer that also respects the grouping of countable sums.
Finite linearity alone does not imply this law for a signed series. -/
structure CountableObservation (o : Option (D α) → Option ℝ) : Prop where
  finite : Observation o
  intSum (k : ℤ → Option (D α)) : o (sumValue (some k)) = Summation.value norm (some (fun i => o (k i)))

theorem CountableObservation.mass : CountableObservation (massValue (α := α)) :=
  ⟨Observation.mass, mass_sumValue⟩

theorem CountableObservation.natSum {o : Option (D α) → Option ℝ} (h : CountableObservation o)
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

theorem CountableObservation.at_chain {o : Option (D α) → Option ℝ} (h : CountableObservation o)
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

theorem CountableObservation.retry_noncontracting_real {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {r : ℝ} (h1 : 1 ≤ r) {seed : Option (D α)} (hs : Admissible seed) :
    o (retryValue (some r) seed) = if o seed = some 0 then some 0 else none := by
  cases h.finite with
  | absent absent => rw [absent, absent]; rfl
  | linear p =>
    cases seed with
    | none => rw [retry_missing, p.missing]; rfl
    | some d =>
      obtain ⟨m, hd⟩ := hs d rfl
      have q0 := le_trans zero_le_one h1
      have e := retry_eq_chain hd q0
      rw [e, h.at_chain p _ (hd.approximates_retry q0), ← e, probe_retry_noncontracting hd h1, p.atoms hd.1]

theorem CountableObservation.retry_noncontracting {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {r : Option ℝ} (q : ℚ) (hq : 1 ≤ q) (hr : r = some (q : ℝ)) {seed : Option (D α)} (hs : Admissible seed) :
    o (retryValue r seed) = Binding.guardValue (Value.not (Value.nonzero (o seed))) (some ((0 : ℤ) : ℝ)) := by
  subst r
  rw [Int.cast_zero, guard_zero]
  exact h.retry_noncontracting_real (by exact_mod_cast hq) hs

/-- A zero observation in a single round makes every partial sum zero. Only a
nonzero observation needs the geometric denominator and the contracting bound. -/
theorem CountableObservation.retry_parameter {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    (r : Option ℝ) {seed : Option (D α)} (hs : Admissible seed) :
    o (retryValue r seed) = Binding.guardValue (Value.le (some ((0 : ℚ) : ℝ)) r)
      (Value.mask (Value.nonzero (o seed)) (Binding.guardValue (Value.lt r (some ((1 : ℚ) : ℝ)))
        (Value.mul (Value.inv (Value.add (some ((1 : ℚ) : ℝ)) (Value.mul (some ((-1 : ℚ) : ℝ)) r))) (o seed)))) := by
  cases r with
  | none => exact h.finite.missing
  | some r =>
    by_cases h0 : 0 ≤ r
    · by_cases h1 : r < 1
      · rw [h.finite.retry_real h0 h1 hs, h.finite.scale]
        have nz : 1 + -r ≠ 0 := by linarith
        cases ho : o seed with
        | none => simp [h0, h1, Binding.guardValue, Value.le, Value.nonzero, Value.mask, Value.mul]
        | some v =>
          by_cases hz : v = 0 <;>
            simp [hz, h0, h1, nz, sub_eq_add_neg, Binding.guardValue, Value.le, Value.lt,
              Value.nonzero, Value.mask, Value.inv, Value.add, Value.mul]
      · rw [h.retry_noncontracting_real (le_of_not_gt h1) hs]
        cases ho : o seed with
        | none => simp [h0, Binding.guardValue, Value.le, Value.mask, Value.nonzero]
        | some v =>
          by_cases hz : v = 0 <;>
            simp [hz, h0, h1, Binding.guardValue, Value.le, Value.lt, Value.mask, Value.nonzero]
    · rw [retry_negative (lt_of_not_ge h0), h.finite.missing]
      simp [h0, Binding.guardValue, Value.le]

theorem complement_weight (oneFirst minusFirst : Bool) (r : Option ℝ) {one minus : Option ℝ}
    (h1 : one = some ((1 : ℚ) : ℝ)) (hm : minus = some ((-1 : ℚ) : ℝ)) :
    (let neg := if minusFirst then Value.mul minus r else Value.mul r minus
     if oneFirst then Value.add one neg else Value.add neg one) = r.map (fun x => 1-x) := by
  subst one minus
  cases r <;> cases oneFirst <;> cases minusFirst <;> simp [Value.mul, Value.add, sub_eq_add_neg, add_comm]

/-- With complementary emission and retry coefficients, a contracting retry
returns the observation of one seed. At unit retry probability the coefficient
of every emitted row is zero, but a missing seed observation is still missing. -/
theorem CountableObservation.fixed_normalized {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    (swap : Bool) (r : Option ℝ) {w : Option ℝ} (hw : w = r.map (fun x => 1-x))
    {seed : Option (D α)} (hs : Admissible seed) {f : D α → Option (D α)}
    (body : ∀ d, f d = retryBody swap false r (scaleValue w seed) d) :
    o (fixedValue (some f)) = Binding.guardValue
      (Value.and (Value.le (some ((0 : ℚ) : ℝ)) r) (Value.le r (some ((1 : ℚ) : ℝ))))
      (Value.mul (Value.mask (Value.lt r (some ((1 : ℚ) : ℝ))) (some ((1 : ℚ) : ℝ))) (o seed)) := by
  subst w
  rw [fixed_weighted_emission swap r _ seed body]
  cases r with
  | none => exact h.finite.missing
  | some r =>
    by_cases hi : r ≤ 1
    · have emission : 0 ≤ 1-r := sub_nonneg.mpr hi
      have hseed : Admissible (scaleValue (some (1-r)) seed) :=
        admissible_scale_lower false (fun v hv => (Option.some.inj hv) ▸ emission) hs
      have checked : Binding.guardValue (Value.le (some ((0 : ℚ) : ℝ)) ((some r).map (fun x => 1-x)))
          (retryValue (some r) (scaleValue (Value.abs ((some r).map (fun x => 1-x))) seed)) =
          retryValue (some r) (scaleValue (some (1-r)) seed) := by
        simp [Binding.guardValue, Value.le, Value.abs, emission, abs_of_nonneg emission]
      rw [checked]
      by_cases lo : 0 ≤ r
      · rcases lt_or_eq_of_le hi with lt | rfl
        · rw [h.finite.retry_real lo lt hseed, h.finite.scale, h.finite.scale]
          have nz : 1-r ≠ 0 := sub_ne_zero.mpr (ne_of_gt lt)
          cases o seed <;> simp [lo, hi, lt, Binding.guardValue, Value.le, Value.lt, Value.and, Value.mul, Value.mask, ← mul_assoc, nz]
        · rw [h.retry_noncontracting_real le_rfl hseed, h.finite.scale]
          cases o seed <;> simp [Binding.guardValue, Value.le, Value.lt, Value.and, Value.mul, Value.mask]
      · rw [retry_negative (lt_of_not_ge lo), h.finite.missing]
        simp [lo, Binding.guardValue, Value.le, Value.and]
    · have emission : ¬ 0 ≤ 1-r := by linarith
      have lo : 0 ≤ r := le_trans zero_le_one (le_of_not_ge hi)
      simp [emission, hi, lo, Binding.guardValue, Value.le, Value.and, h.finite.missing]

end QSym.Distribution.Atomic
