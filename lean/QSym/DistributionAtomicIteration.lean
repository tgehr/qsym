import QSym.DistributionAtomicValue

/-! Distribution fixed points use the evaluated source body at every finite
depth. The limit retains both the weights and the set of visited outcomes. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal
open OmegaCompletePartialOrder

def iterateBody (f : D α → Option (D α)) : ℕ → Option (D α)
  | 0 => some .zero
  | n+1 => (iterateBody f n).bind f

def Approximates (values : ℕ → Option (D α)) (s : ℕ → Model α) : Prop :=
  Monotone s ∧ ∀ n, ∃ d, values n = some d ∧ Presents d (s n)

abbrev Tracks (f : D α → Option (D α)) (s : ℕ → Model α) := Approximates (iterateBody f) s

private theorem Approximates.unique {v : ℕ → Option (D α)} {s t : ℕ → Model α}
    (hs : Approximates v s) (ht : Approximates v t) : s = t := by
  funext n
  obtain ⟨d, hd, hm⟩ := hs.2 n
  obtain ⟨e, he, hk⟩ := ht.2 n
  cases Option.some.inj (hd.symm.trans he)
  exact (hm.eq_iff hk).mpr (fun _ => rfl)

private def trackedChain (v : ℕ → Option (D α)) : Option (ℕ → Model α) := by
  classical exact if h : ∃ s, Approximates v s then some h.choose else none

private theorem trackedChain_eq {v : ℕ → Option (D α)} {s : ℕ → Model α} (h : Approximates v s) :
    trackedChain v = some s := by
  classical
  have ex : ∃ t, Approximates v t := ⟨s, h⟩
  rw [trackedChain, dif_pos ex, ex.choose_spec.unique h]

/-- The semantic limit exists even when its support has no finite presentation. -/
def limitModel (v : ℕ → Option (D α)) : Option (Model α) :=
  (trackedChain v).map (fun s => ⨆ n, s n)

theorem limitModel_eq {v : ℕ → Option (D α)} {s : ℕ → Model α} (h : Approximates v s) :
    limitModel v = some (⨆ n, s n) := by rw [limitModel, trackedChain_eq h]; rfl

theorem limitModel_eq_some_iff {v : ℕ → Option (D α)} {m : Model α} :
    limitModel v = some m ↔ ∃ s, Approximates v s ∧ (⨆ n, s n) = m := by
  classical
  constructor
  · intro h
    by_cases ex : ∃ s, Approximates v s
    · exact ⟨ex.choose, ex.choose_spec, Option.some.inj ((limitModel_eq ex.choose_spec).symm.trans h)⟩
    · simp [limitModel, trackedChain, ex] at h
  · rintro ⟨s, hs, rfl⟩
    exact limitModel_eq hs

private theorem trackedChain_missing {v : ℕ → Option (D α)} {n : ℕ} (h : v n = none) : trackedChain v = none := by
  classical
  have missing : ¬ ∃ s, Approximates v s := by
    rintro ⟨s, hs⟩
    obtain ⟨d, hd, _⟩ := hs.2 n
    rw [h] at hd
    contradiction
  simp [trackedChain, missing]

theorem limitModel_missing {v : ℕ → Option (D α)} {n : ℕ} (h : v n = none) : limitModel v = none := by
  rw [limitModel, trackedChain_missing h]; rfl

/-- A partial fixed point from the source body's actual finite approximants.
Retain their order when the set of visits and limiting weights alone do not
determine how a signed observation of an infinite result converges. -/
def fixedValue (body : Option (D α → Option (D α))) : Option (D α) :=
  body.bind fun f => (trackedChain (iterateBody f)).bind fun s => realizeChain (⨆ n, s n) s

theorem fixed_chain {f : D α → Option (D α)} {s : ℕ → Model α} (h : Tracks f s) :
    fixedValue (some f) = realizeChain (⨆ n, s n) s := by
  simp only [fixedValue, Option.some_bind, trackedChain_eq h]

theorem fixed_missing {f : D α → Option (D α)} {n : ℕ} (h : iterateBody f n = none) :
    fixedValue (some f) = none := by
  simp only [fixedValue, Option.some_bind, trackedChain_missing h, Option.none_bind]

/-- A compositional certificate for the source body suffices to compute its
least fixed point in the atomic model. -/
theorem fixed_of_step_on (f : D α → Option (D α)) (g : Model α →o Model α) (hg : ωScottContinuous g)
    (P : Model α → Prop) (initial : P ⊥) (keep : ∀ m, P m → P (g m))
    (lift : ∀ d m, P m → Presents d m → ∃ e, f d = some e ∧ Presents e (g m)) :
    fixedValue (some f) = realizeChain g.lfp (fun n => g^[n] ⊥) := by
  let s := fun n : ℕ => g^[n] ⊥
  have invariant : ∀ n, P (s n) := by
    intro n
    induction n with
    | zero => exact initial
    | succ n ih => simpa only [s, Function.iterate_succ_apply'] using keep (s n) ih
  have data : ∀ n, ∃ d, iterateBody f n = some d ∧ Presents d (s n) := by
    intro n
    induction n with
    | zero => exact ⟨.zero, rfl, Represents.zero, visited_zero⟩
    | succ n ih =>
      obtain ⟨d, hd, hm⟩ := ih
      obtain ⟨e, he, hk⟩ := lift d _ (invariant n) hm
      exact ⟨e, by simpa [iterateBody, hd] using he, by simpa [s, Function.iterate_succ_apply'] using hk⟩
  rw [fixed_chain (⟨g.monotone.monotone_iterate_of_le_map bot_le, data⟩ : Tracks f s), fixedPoints.lfp_eq_sSup_iterate _ hg]

theorem fixed_of_step (f : D α → Option (D α)) (g : Model α →o Model α) (hg : ωScottContinuous g)
    (lift : ∀ d m, Presents d m → ∃ e, f d = some e ∧ Presents e (g m)) :
    fixedValue (some f) = realizeChain g.lfp (fun n => g^[n] ⊥) :=
  fixed_of_step_on f g hg (fun _ => True) trivial (fun _ _ => trivial) (fun d m _ => lift d m)

theorem strictRetry_continuous (b : Model α) (r : ℝ≥0∞) : ωScottContinuous (strictRetryStep b r) := by
  apply ωScottContinuous_iff_map_ωSup_of_orderHom.mpr
  intro c
  apply Prod.ext
  · funext x
    change b.1 x + r * (⨆ n : ℕ, (c n).1 x) = ⨆ n : ℕ, b.1 x + r * (c n).1 x
    rw [ENNReal.mul_iSup, ENNReal.add_iSup]
  · ext x
    change x ∈ b.2 ∪ (⨆ n : ℕ, (c n).2) ↔ x ∈ (⨆ n : ℕ, b.2 ∪ (c n).2)
    simp only [Set.iSup_eq_iUnion, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hx | ⟨n, hx⟩)
      · exact ⟨0, Or.inl hx⟩
      · exact ⟨n, Or.inr hx⟩
    · rintro ⟨n, hx | hx⟩
      · exact Or.inl hx
      · exact Or.inr ⟨n, hx⟩

private theorem weight_constant {d : D α} {k : Weights α} (h : Represents d k) {r : ℝ} (hr : 0 ≤ r) :
    ∃ e, weight (fun _ => some r) d = some e ∧ Represents e (fun x => ENNReal.ofReal r * k x) ∧ visited e = visited d := by
  induction h with
  | zero => exact ⟨_, rfl, by simpa using (Represents.zero (α := α)), rfl⟩
  | dirac a => exact ⟨_, rfl, (Represents.dirac a).scale hr, visited_scale _ _⟩
  | add hd he ih jh =>
    obtain ⟨a, ha, ka, va⟩ := ih
    obtain ⟨b, hb, kb, vb⟩ := jh
    exact ⟨.add a b, by simp [weight, ha, hb, addValue], by simpa [mul_add] using ka.add kb,
      by simp [va, vb]⟩
  | @scale c _ _ hc hd ih =>
    obtain ⟨a, ha, ka, va⟩ := ih
    exact ⟨.scale c a, by simp [weight, ha, scaleValue], by simpa [mul_left_comm] using ka.scale hc,
      by simp [va]⟩

def scaleTerm (weighted : Bool) (r : Option ℝ) (v : Option (D α)) : Option (D α) :=
  if weighted then weightValue (some (fun _ => r)) v else scaleValue r v

def retryTail (weighted : Bool) (r : Option ℝ) (d : D α) := scaleTerm weighted r (some d)

theorem tail_step (weighted : Bool) {d : D α} {k : Model α} (hd : Presents d k) {r : ℝ} (hr : 0 ≤ r) :
    ∃ e, retryTail weighted (some r) d = some e ∧ Represents e (fun x => ENNReal.ofReal r * k.1 x) ∧ visited e = k.2 := by
  cases weighted with
  | false => exact ⟨_, rfl, hd.1.scale hr, (visited_scale _ _).trans hd.2⟩
  | true =>
    obtain ⟨e, he, hm, hv⟩ := weight_constant hd.1 hr
    exact ⟨e, he, hm, hv.trans hd.2⟩

/-- Either order of addition represents the same model step. -/
def retryBody (swap weighted : Bool) (r : Option ℝ) (seed : Option (D α)) (d : D α) :=
  let tail := retryTail weighted r d
  if swap then addValue tail seed else addValue seed tail

/-- A homogeneous recursive expression scales every outcome weight by the
same nonnegative factor and preserves every visit, including when it scales by zero. -/
structure Tail (g : D α → Option (D α)) (q : ℚ) : Prop where
  nonneg : 0 ≤ q
  step : ∀ d m, Presents d m → ∃ e, g d = some e ∧
    Represents e (fun x => ENNReal.ofReal (q : ℝ) * m.1 x) ∧ visited e = m.2

theorem Tail.self : Tail (fun d : D α => some d) 1 :=
  ⟨zero_le_one, fun d _ hd => ⟨d, rfl, by simpa using hd.1, hd.2⟩⟩

theorem Tail.scale {g : D α → Option (D α)} {q : ℚ} (weighted : Bool) {r : Option ℝ}
    (c z : ℚ) (hc : 0 ≤ c) (hz : z = c*q) (hr : r = some (c : ℝ)) (h : Tail g q) :
    Tail (fun d => scaleTerm weighted r (g d)) z := by
  subst r z
  refine ⟨mul_nonneg hc h.nonneg, ?_⟩
  intro d m hd
  obtain ⟨a, ha, ka, va⟩ := h.step d m hd
  have ca : 0 ≤ (c : ℝ) := by exact_mod_cast hc
  obtain ⟨e, he, ke, ve⟩ := tail_step weighted
    (k := (fun x => ENNReal.ofReal (q : ℝ) * m.1 x, m.2)) ⟨ka, va⟩ ca
  exact ⟨e, ha ▸ he, by simpa [ENNReal.ofReal_mul ca, mul_assoc] using ke, ve⟩

theorem Tail.add {f g : D α → Option (D α)} {a b : ℚ}
    (z : ℚ) (hz : z = a+b) (hf : Tail f a) (hg : Tail g b) :
    Tail (fun d => addValue (f d) (g d)) z := by
  subst z
  refine ⟨add_nonneg hf.nonneg hg.nonneg, ?_⟩
  intro d m hd
  obtain ⟨x, hx, kx, vx⟩ := hf.step d m hd
  obtain ⟨y, hy, ky, vy⟩ := hg.step d m hd
  have ha : 0 ≤ (a : ℝ) := by exact_mod_cast hf.nonneg
  have hb : 0 ≤ (b : ℝ) := by exact_mod_cast hg.nonneg
  exact ⟨.add x y, by rw [hx, hy]; rfl, by simpa [ENNReal.ofReal_add ha hb, add_mul] using kx.add ky,
    by simp [vx, vy]⟩

theorem fixed_add_tail (swap : Bool) {r : Option ℝ} (q : ℚ) (hr : r = some (q : ℝ))
    {seed : Option (D α)} (hs : Admissible seed) {g f : D α → Option (D α)} (tail : Tail g q)
    (body : ∀ d, f d = if swap then addValue (g d) seed else addValue seed (g d)) :
    fixedValue (some f) = retryValue r seed := by
  subst r
  cases seed with
  | none =>
    change fixedValue (some f) = none
    apply fixed_missing (n := 1)
    change f .zero = none
    rw [body]
    cases swap <;> cases g .zero <;> rfl
  | some b =>
    obtain ⟨m, hb⟩ := hs b rfl
    have r0 : 0 ≤ (q : ℝ) := by exact_mod_cast tail.nonneg
    rw [retry_eq_chain hb r0]
    apply fixed_of_step _ _ (strictRetry_continuous _ _)
    intro d k hd
    obtain ⟨e, he, htail, hvis⟩ := tail.step d k hd
    cases swap with
    | false =>
      refine ⟨.add b e, by simp [body, he, addValue], hb.1.add htail, ?_⟩
      exact (visited_add _ _).trans (congrArg₂ (· ∪ ·) hb.2 hvis)
    | true =>
      refine ⟨.add e b, by simp [body, he, addValue], ?_, ?_⟩
      · simpa [strictRetryStep, retryStep, add_comm] using htail.add hb.1
      · exact (visited_add _ _).trans ((congrArg₂ (· ∪ ·) hvis hb.2).trans (Set.union_comm _ _))

theorem fixed_retry (swap weighted : Bool) {r : Option ℝ} (q : ℚ) (h0 : 0 ≤ q) (hr : r = some (q : ℝ))
    {seed : Option (D α)} (hs : Admissible seed) {f : D α → Option (D α)}
    (body : ∀ d, f d = retryBody swap weighted r seed d) : fixedValue (some f) = retryValue r seed := by
  apply fixed_add_tail swap q hr hs (g := retryTail weighted r) _ body
  subst r
  exact ⟨h0, fun _ _ hd => tail_step weighted hd (by exact_mod_cast h0)⟩

/-- With no emission the empty distribution is already a fixed point, even if
one step duplicates the continuation or multiplies its weight by more than one. -/
theorem fixed_tail {f g : D α → Option (D α)} {q : ℚ} (tail : Tail g q)
    (body : ∀ d, f d = g d) : fixedValue (some f) = zeroValue := by
  let m : Model α := (fun _ => 0, ∅)
  have h : Presents (.zero : D α) m := ⟨Represents.zero, visited_zero⟩
  have h0 : 0 ≤ (q : ℝ) := by exact_mod_cast tail.nonneg
  rw [← retry_zero q tail.nonneg (r := some (q : ℝ)) rfl, zeroValue, retry_eq_chain h h0]
  apply fixed_of_step _ _ (strictRetry_continuous _ _)
  intro d k hd
  obtain ⟨e, he, hk, hv⟩ := tail.step d k hd
  exact ⟨e, (body d).trans he, by simpa [strictRetryStep, retryStep, m] using hk,
    by simpa [strictRetryStep, m] using hv⟩

end QSym.Distribution.Atomic
