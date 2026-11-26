import QSym.DistributionAtomicTransport
/-! A contracting atomic loop that transports its recursive output along an
involution. Its even and odd rounds form two geometric series. Both visits
remain observable when a coefficient vanishes. -/
noncomputable section
namespace QSym.Distribution.Atomic
variable {ι α : Type}

private theorem alternating_geometric {next : ι → ι} (inv : Function.Involutive next) (x : ι) (t : ι → Option ℝ)
    {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summation.value norm (some fun n : ℕ => Value.mul (some (r^n)) (t (next^[n] x))) =
      Value.add (Value.mul (some ((1-r^2)⁻¹)) (t x))
        (Value.mul (some (r*(1-r^2)⁻¹)) (t (next x))) := by
  cases ha : t x with
  | none =>
    rw [Summation.undefined_term norm _ 0 (by change Value.mul _ (t x) = none; rw [ha]; rfl)]
    rfl
  | some a =>
    cases hb : t (next x) with
    | none =>
      rw [Summation.undefined_term norm _ 1 (by change Value.mul _ (t (next x)) = none; rw [hb]; rfl)]
      rfl
    | some b =>
      let u (n : ℕ) := r^n * (t (next^[n] x)).getD 0
      have even (k : ℕ) : u (2*k) = (r^2)^k * a := by simp [u, inv.iterate_two_mul, ha, pow_mul]
      have odd (k : ℕ) : u (2*k+1) = (r^2)^k * (r*b) := by
        simp only [u, inv.iterate_bit1, hb, Option.getD_some, pow_succ, pow_mul, mul_assoc]
      have geo := hasSum_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]; nlinarith : ‖r^2‖ < 1)
      have sum : HasSum u (((1-r^2)⁻¹)*a + (1-r^2)⁻¹*(r*b)) := by
        apply HasSum.even_add_odd
        · simpa only [even] using (geo.mul_right a)
        · simpa only [odd] using (geo.mul_right (r*b))
      have defined (n) : Value.mul (some (r^n)) (t (next^[n] x)) = some (u n) := by
        obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
        · simp [u, inv.iterate_two_mul, ha, Value.mul]
        · simp only [u, inv.iterate_bit1, hb, Option.getD_some, Value.mul]
      rw [Summation.of_hasSum norm _ u _ defined sum.summable.norm sum]
      simp [Value.add, Value.mul, mul_left_comm, mul_assoc]

/-- The two parity classes may be grouped for a contracting return. A missing
test in either class is still observed when its numeric coefficient is zero. -/
theorem CountableObservation.orbit_pair {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    (b : ι → Option (D α)) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) {next : ι → ι} (inv : Function.Involutive next) (x : ι) :
    o (orbitSeries b (fun _ => r) next x) =
      o (addValue (scaleValue (some ((1-r^2)⁻¹)) (b x)) (scaleValue (some (r*(1-r^2)⁻¹)) (b (next x)))) := by
  cases h.finite with
  | absent absent => rw [absent, absent]
  | linear p =>
    rw [orbitSeries, h.natSum, p.add]
    simp only [reachWeight_const, p.scale]
    exact alternating_geometric inv x (fun i => o (b i)) h0 h1

private theorem Transport.involutive_seed {push : Option (D α) → Option (D α)} (tr : Transport push)
    {next : α → α} (inv : Function.Involutive next)
    (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a))) {d : D α} {k : Weights α} (hd : Represents d k) :
    ∃ e m, push (some d) = some e ∧ Presents e m ∧ push (some e) = some d := by
  induction hd with
  | zero => exact ⟨.zero, (fun _ => 0, ∅), tr.zero, ⟨Represents.zero, visited_zero⟩, tr.zero⟩
  | dirac a => exact ⟨.dirac (next a), (atom (next a), {next a}), point a, ⟨Represents.dirac _, visited_dirac _⟩, by rw [point, inv]⟩
  | add _ _ ih jh =>
    obtain ⟨e, m, he, pe, back⟩ := ih
    obtain ⟨g, n, hg, pg, rev⟩ := jh
    refine ⟨.add e g, _, ?_, presents_sum pe pg, ?_⟩
    · change push (addValue (some _) (some _)) = _
      rw [tr.add, he, hg]; rfl
    · change push (addValue (some e) (some g)) = _
      rw [tr.add, back, rev]; rfl
  | scale hr _ ih =>
    obtain ⟨e, m, he, pe, back⟩ := ih
    refine ⟨.scale _ e, _, ?_, presents_scale pe hr, ?_⟩
    · change push (scaleValue (some _) (some _)) = _
      rw [tr.scale, he]; rfl
    · change push (scaleValue (some _) (some e)) = _
      rw [tr.scale, back]; rfl

theorem CountableObservation.fixed_involution {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {push : Option (D α) → Option (D α)} (tr : Transport push) {next : α → α} (inv : Function.Involutive next)
    (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a))) {s : Option (D α)} (seed : Admissible s)
    {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) {f : D α → Option (D α)}
    (body : ∀ d, f d = addValue s (scaleValue (some r) (push (some d)))) :
    o (fixedValue (some f)) =
      o (addValue (scaleValue (some ((1-r^2)⁻¹)) s) (scaleValue (some (r*(1-r^2)⁻¹)) (push s))) := by
  cases s with
  | none =>
    have missing : iterateBody f 1 = none := body .zero
    rw [fixed_missing missing]
    rfl
  | some d =>
    obtain ⟨m, pres⟩ := seed d rfl
    obtain ⟨e, n, he, pe, back⟩ := tr.involutive_seed inv point pres.1
    let b (j : Bool) : Option (D α) := if j then some e else some d
    let models (j : Bool) : Model α := if j then n else m
    have lift (j : Bool) (_ : j ∈ (Set.univ : Set Bool)) : ∃ u, b j = some u ∧ Presents u (models j) := by
      cases j
      · exact ⟨d, rfl, pres⟩
      · exact ⟨e, rfl, pe⟩
    have move (j : Bool) (_ : j ∈ (Set.univ : Set Bool)) : push (b j) = b (!j) := by
      cases j
      · exact he
      · exact back
    rw [h.forward_orbit_on tr b r h0 Bool.not models Set.univ (fun _ _ => Set.mem_univ _)
      lift move (Set.mem_univ false) body, h.orbit_pair b h0 h1 (fun j : Bool => Bool.not_not j) false, he]
    rfl

theorem CountableObservation.fixed_involution_q {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {push : Option (D α) → Option (D α)} (tr : Transport push) {next : α → α} (inv : Function.Involutive next)
    (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a))) {s : Option (D α)} (seed : Admissible s)
    (q a b : ℚ) (h0 : 0 ≤ q) (h1 : q < 1) (ha : a = (1-q^2)⁻¹) (hb : b = q*a)
    {r u v : Option ℝ} (hr : r = some (q : ℝ)) (hu : u = some (a : ℝ)) (hv : v = some (b : ℝ))
    {f : D α → Option (D α)} (body : ∀ d, f d = addValue s (scaleValue r (push (some d)))) :
    o (fixedValue (some f)) = o (addValue (scaleValue u s) (scaleValue v (push s))) := by
  subst r u v b a
  simpa only [Rat.cast_mul, Rat.cast_inv, Rat.cast_sub, Rat.cast_one, Rat.cast_pow] using
    h.fixed_involution tr inv point seed (by exact_mod_cast h0) (by exact_mod_cast h1) body

theorem dirac_neg (left : Bool) {r : Option ℝ} (hr : r = some ((-1 : ℚ) : ℝ)) (x : ℝ) :
    diracValue (if left then Value.mul r (some x) else Value.mul (some x) r) = some (.dirac (-x)) := by
  cases left <;> simp [hr, Value.mul, diracValue]

end QSym.Distribution.Atomic
