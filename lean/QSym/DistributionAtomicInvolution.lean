import QSym.DistributionAtomicTransport
import QSym.SummationParity
/-! Atomic loops that transport recursive outcomes along an involution. Even
and odd rounds can be summed separately. A noncontracting series converges
only when both rounds have zero signed observation. -/
noncomputable section
namespace QSym.Distribution.Atomic
open OmegaCompletePartialOrder
open scoped ENNReal
variable {ι α : Type}

private theorem geometric_phases {next : ι → ι} (inv : Function.Involutive next) (x : ι) (t : ι → Option ℝ) (r : ℝ) :
    Summation.value norm (some fun n : ℕ => Value.mul (some (r^n)) (t (next^[n] x))) =
      Value.add (Summation.value norm (some fun n : ℕ => Value.mul (some ((r^2)^n)) (t x)))
        (Summation.value norm (some fun n : ℕ => Value.mul (some ((r^2)^n)) (Value.mul (some r) (t (next x))))) := by
  rw [Summation.even_odd]
  have even (k : ℕ) : Value.mul (some (r^(2*k))) (t (next^[2*k] x)) =
      Value.mul (some ((r^2)^k)) (t x) := by rw [inv.iterate_two_mul, pow_mul]; rfl
  have odd (k : ℕ) : Value.mul (some (r^(2*k+1))) (t (next^[2*k+1] x)) =
      Value.mul (some ((r^2)^k)) (Value.mul (some r) (t (next x))) := by
    rw [inv.iterate_bit1, pow_succ, pow_mul]
    cases t (next x) <;> simp [Value.mul, mul_assoc]
  simp_rw [even, odd]

private theorem weighted_geometric {q : ℝ} (hq : ‖q‖ < 1) (v : Option ℝ) :
    Summation.value norm (some fun n : ℕ => Value.mul (some (q^n)) v) = Value.mul (some (1-q)⁻¹) v := by
  cases v with
  | none => exact Summation.undefined_term norm _ 0 rfl
  | some a =>
    have hs := (hasSum_geometric_of_norm_lt_one hq).mul_right a
    exact Summation.of_hasSum norm _ _ _ (fun _ => rfl) hs.summable.norm hs

private theorem alternating_geometric {next : ι → ι} (inv : Function.Involutive next) (x : ι) (t : ι → Option ℝ)
    {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summation.value norm (some fun n : ℕ => Value.mul (some (r^n)) (t (next^[n] x))) =
      Value.add (Value.mul (some ((1-r^2)⁻¹)) (t x))
        (Value.mul (some (r*(1-r^2)⁻¹)) (t (next x))) := by
  have hq : ‖r^2‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]; nlinarith
  rw [geometric_phases inv x t r, weighted_geometric hq, weighted_geometric hq]
  cases t (next x) <;> simp [Value.mul, mul_left_comm, mul_assoc]

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

/-- Precompose the weights and the visited set with the inverse map on outcomes. -/
def reindexModel (next : α → α) : Model α →o Model α where
  toFun m := (fun a => m.1 (next a), next ⁻¹' m.2)
  monotone' _ _ h := ⟨fun a => h.1 (next a), Set.preimage_mono h.2⟩

theorem reindexModel_continuous (next : α → α) : ωScottContinuous (reindexModel next) := by
  apply ωScottContinuous_iff_map_ωSup_of_orderHom.mpr
  intro c
  apply Prod.ext
  · rfl
  · ext y
    change next y ∈ (⨆ n : ℕ, (c n).2) ↔ y ∈ (⨆ n : ℕ, next ⁻¹' (c n).2)
    simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_preimage]

theorem Transport.relabel {push : Option (D α) → Option (D α)} (tr : Transport push)
    {next : α → α} (inv : Function.Involutive next) (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a)))
    {d : D α} {m : Model α} (pres : Presents d m) : ∃ e, push (some d) = some e ∧ Presents e (reindexModel next m) := by
  classical
  obtain ⟨data, visits⟩ := pres
  obtain ⟨k, v⟩ := m
  dsimp only at data visits
  subst v
  induction data with
  | zero => exact ⟨.zero, tr.zero, Represents.zero, by simp [reindexModel]⟩
  | dirac a =>
    have back (y : α) : y = next a ↔ next y = a := ⟨fun e => e ▸ inv a, fun e => (inv y).symm.trans (congrArg next e)⟩
    have w : (fun y => atom a (next y)) = atom (next a) := by ext y; simp [atom, back]
    refine ⟨.dirac (next a), point a, ?_, ?_⟩
    · change Represents _ (fun y => atom a (next y))
      rw [w]; exact Represents.dirac _
    · ext y; simp [reindexModel, back]
  | @add d k e l _ _ ih jh =>
    obtain ⟨u, hu, pu⟩ := ih
    obtain ⟨v, hv, pv⟩ := jh
    refine ⟨.add u v, ?_, pu.1.add pv.1, ?_⟩
    · change push (addValue (some d) (some e)) = _
      rw [tr.add, hu, hv]; rfl
    · simp only [reindexModel, OrderHom.coe_mk, visited_add, Set.preimage_union]
      exact congrArg₂ (· ∪ ·) pu.2 pv.2
  | @scale r d k hr _ ih =>
    obtain ⟨u, hu, pu⟩ := ih
    refine ⟨.scale r u, ?_, pu.1.scale hr, ?_⟩
    · change push (scaleValue (some r) (some d)) = _
      rw [tr.scale, hu]; rfl
    · simpa [reindexModel, visited_scale] using pu.2

private theorem fixed_unscaled_involution {push : Option (D α) → Option (D α)} (tr : Transport push)
    {next : α → α} (inv : Function.Involutive next) (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a)))
    {s : Option (D α)} (seed : Admissible s) {f : D α → Option (D α)}
    (body : ∀ d, f d = addValue s (push (some d))) :
    fixedValue (some f) = fixedValue (some fun d => addValue s (scaleValue (some 1) (push (some d)))) := by
  cases s with
  | none => rw [fixed_missing (n := 1) (body .zero), fixed_missing (n := 1) (by rfl)]
  | some d =>
    obtain ⟨m, hd⟩ := seed d rfl
    let g := (strictRetryStep m 1).comp (reindexModel next)
    have continuous : ωScottContinuous g := (strictRetry_continuous m 1).comp (reindexModel_continuous next)
    have bare (k : Model α) : g k = sumModel m (reindexModel next k) := by
      exact Prod.ext (funext fun a => congrArg (fun y => m.1 a + y) (one_mul _)) rfl
    have unit (k : Model α) : scaleModel (ENNReal.ofReal 1) k = k := by ext a <;> simp [scaleModel]
    rw [fixed_of_step f g continuous, fixed_of_step _ g continuous]
    · intro e k he
      obtain ⟨u, hu, pu⟩ := tr.relabel inv point he
      refine ⟨.add d (.scale 1 u), by rw [hu]; rfl, ?_⟩
      rw [bare, ← unit (reindexModel next k)]
      exact presents_sum hd (presents_scale pu (zero_le_one : (0:ℝ) ≤ 1))
    · intro e k he
      obtain ⟨u, hu, pu⟩ := tr.relabel inv point he
      exact ⟨.add d u, by rw [body, hu]; rfl, bare k ▸ presents_sum hd pu⟩

private theorem Transport.twice_atom {push : Option (D α) → Option (D α)} (tr : Transport push)
    {next : α → α} (inv : Function.Involutive next) (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a)))
    {d k} (present : Represents d k) : push (push (some d)) = some d := by
  have twice : Transport (fun v => push (push v)) :=
    ⟨by simp only [tr.missing], by simp only [tr.zero], fun a b => by simp only [tr.add],
      fun r a => by simp only [tr.scale]⟩
  exact twice.reemit (fun a => by rw [point, point, inv]) present

theorem CountableObservation.fixed_involution_orbit {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {push : Option (D α) → Option (D α)} (tr : Transport push) {next : α → α} (inv : Function.Involutive next)
    (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a))) {s : Option (D α)} (seed : Admissible s)
    {r : ℝ} (h0 : 0 ≤ r) {f : D α → Option (D α)}
    (body : ∀ d, f d = addValue s (scaleValue (some r) (push (some d)))) :
    o (fixedValue (some f)) = o (orbitSeries (fun j : Bool => if j then push s else s) (fun _ => r) Bool.not false) := by
  cases s with
  | none =>
    have missing : iterateBody f 1 = none := body .zero
    rw [fixed_missing missing, h.finite.missing, orbitSeries, h.natSum]
    symm
    exact Summation.undefined_term norm _ 0 h.finite.missing
  | some d =>
    obtain ⟨m, pres⟩ := seed d rfl
    obtain ⟨e, he, pe⟩ := tr.relabel inv point pres
    let b (j : Bool) : Option (D α) := if j then push (some d) else some d
    let models (j : Bool) : Model α := if j then reindexModel next m else m
    have lift (j : Bool) (_ : j ∈ (Set.univ : Set Bool)) : ∃ u, b j = some u ∧ Presents u (models j) := by
      cases j
      · exact ⟨d, rfl, pres⟩
      · exact ⟨e, he, pe⟩
    have move (j : Bool) (_ : j ∈ (Set.univ : Set Bool)) : push (b j) = b (!j) := by
      cases j
      · rfl
      · change push (push (some d)) = some d
        exact tr.twice_atom inv point pres.1
    exact h.forward_orbit_on tr b r h0 Bool.not models Set.univ (fun _ _ => Set.mem_univ _)
      lift move (Set.mem_univ false) body

theorem CountableObservation.fixed_involution {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {push : Option (D α) → Option (D α)} (tr : Transport push) {next : α → α} (inv : Function.Involutive next)
    (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a))) {s : Option (D α)} (seed : Admissible s)
    {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) {f : D α → Option (D α)}
    (body : ∀ d, f d = addValue s (scaleValue (some r) (push (some d)))) :
    o (fixedValue (some f)) =
      o (addValue (scaleValue (some ((1-r^2)⁻¹)) s) (scaleValue (some (r*(1-r^2)⁻¹)) (push s))) := by
  rw [h.fixed_involution_orbit tr inv point seed h0 body, h.orbit_pair _ h0 h1 (fun j : Bool => Bool.not_not j) false]
  rfl

/-- At a noncontracting two-cycle, each parity class must separately have
zero signed observation. Cancellation within one emission remains available. -/
theorem CountableObservation.orbit_pair_noncontracting {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    (b : ι → Option (D α)) {r : ℝ} (hr : 1 ≤ r) {next : ι → ι} (inv : Function.Involutive next) (x : ι) :
    o (orbitSeries b (fun _ => r) next x) = Value.add
      (Binding.guardValue (Value.not (Value.nonzero (o (b x)))) (some (0 : ℝ)))
      (Binding.guardValue (Value.not (Value.nonzero (o (b (next x))))) (some (0 : ℝ))) := by
  rw [guard_zero, guard_zero]
  cases h.finite with
  | absent absent => simp [absent, Value.add]
  | linear p =>
    rw [orbitSeries, h.natSum]
    simp only [p.scale, reachWeight_const]
    rw [geometric_phases inv x (fun i => o (b i))]
    have sq : 1 ≤ r^2 := by nlinarith
    rw [geometric_noncontracting _ sq, geometric_noncontracting _ sq]
    have test : Value.mul (some r) (o (b (next x))) = some 0 ↔ o (b (next x)) = some 0 := by
      have nz : r ≠ 0 := by linarith
      cases o (b (next x)) <;> simp [Value.mul, nz]
    rw [if_congr test rfl rfl]

theorem CountableObservation.fixed_involution_noncontracting {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {push : Option (D α) → Option (D α)} (tr : Transport push) {next : α → α} (inv : Function.Involutive next)
    (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a))) {s : Option (D α)} (seed : Admissible s)
    (q : ℚ) (hq : 1 ≤ q) {r : Option ℝ} (hr : r = some (q : ℝ)) {f : D α → Option (D α)}
    (body : ∀ d, f d = addValue s (scaleValue r (push (some d)))) :
    o (fixedValue (some f)) = Value.add
      (Binding.guardValue (Value.not (Value.nonzero (o s))) (some ((0 : ℤ) : ℝ)))
      (Binding.guardValue (Value.not (Value.nonzero (o (push s)))) (some ((0 : ℤ) : ℝ))) := by
  subst r
  have h1 : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  rw [Int.cast_zero, h.fixed_involution_orbit tr inv point seed (zero_le_one.trans h1) body,
    h.orbit_pair_noncontracting _ h1 (fun j : Bool => Bool.not_not j) false]
  rfl

theorem CountableObservation.fixed_involution_unscaled {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {push : Option (D α) → Option (D α)} (tr : Transport push) {next : α → α} (inv : Function.Involutive next)
    (point : ∀ a, push (some (.dirac a)) = some (.dirac (next a))) {s : Option (D α)} (seed : Admissible s)
    {f : D α → Option (D α)} (body : ∀ d, f d = addValue s (push (some d))) :
    o (fixedValue (some f)) = Value.add
      (Binding.guardValue (Value.not (Value.nonzero (o s))) (some ((0 : ℤ) : ℝ)))
      (Binding.guardValue (Value.not (Value.nonzero (o (push s)))) (some ((0 : ℤ) : ℝ))) := by
  rw [fixed_unscaled_involution tr inv point seed body]
  exact h.fixed_involution_noncontracting tr inv point seed 1 le_rfl (by norm_num) (fun _ => rfl)

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
