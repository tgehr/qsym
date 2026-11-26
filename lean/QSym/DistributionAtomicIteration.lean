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

def Tracks (f : D α → Option (D α)) (s : ℕ → Model α) : Prop :=
  Monotone s ∧ ∀ n, ∃ d, iterateBody f n = some d ∧ Presents d (s n)

private theorem tracks_unique {f : D α → Option (D α)} {s t : ℕ → Model α}
    (hs : Tracks f s) (ht : Tracks f t) : s = t := by
  funext n
  obtain ⟨d, hd, hm⟩ := hs.2 n
  obtain ⟨e, he, hk⟩ := ht.2 n
  cases Option.some.inj (hd.symm.trans he)
  exact (hm.eq_iff hk).mpr (fun _ => rfl)

/-- A missing approximant or a limit without a finite atomic presentation
gives a partial value. Zero approximants are genuine distributions. -/
def fixedValue (body : Option (D α → Option (D α))) : Option (D α) := by
  classical
  exact body.bind fun f =>
    if h : ∃ s, Tracks f s then realize (⨆ n, h.choose n) else none

theorem fixed_chain {f : D α → Option (D α)} {s : ℕ → Model α} (h : Tracks f s) :
    fixedValue (some f) = realize (⨆ n, s n) := by
  classical
  have hex : ∃ t, Tracks f t := ⟨s, h⟩
  simp only [fixedValue, Option.some_bind, dif_pos hex, tracks_unique hex.choose_spec h]

theorem fixed_missing {f : D α → Option (D α)} {n : ℕ} (h : iterateBody f n = none) :
    fixedValue (some f) = none := by
  classical
  have missing : ¬ ∃ s, Tracks f s := by
    rintro ⟨s, hs⟩
    obtain ⟨d, hd, _⟩ := hs.2 n
    rw [h] at hd
    contradiction
  simp [fixedValue, missing]

/-- A compositional certificate for the source body suffices to compute its
least fixed point in the atomic model. -/
theorem fixed_of_step (f : D α → Option (D α)) (g : Model α →o Model α) (hg : ωScottContinuous g)
    (lift : ∀ d m, Presents d m → ∃ e, f d = some e ∧ Presents e (g m)) :
    fixedValue (some f) = realize g.lfp := by
  let s := fun n : ℕ => g^[n] ⊥
  have steps : ∀ n, s n ≤ s (n+1) := by
    intro n
    induction n with
    | zero => exact bot_le
    | succ n ih => simpa only [s, Function.iterate_succ_apply'] using g.monotone ih
  have data : ∀ n, ∃ d, iterateBody f n = some d ∧ Presents d (s n) := by
    intro n
    induction n with
    | zero => exact ⟨.zero, rfl, Represents.zero, visited_zero⟩
    | succ n ih =>
      obtain ⟨d, hd, hm⟩ := ih
      obtain ⟨e, he, hk⟩ := lift d _ hm
      exact ⟨e, by simpa [iterateBody, hd] using he, by simpa [s, Function.iterate_succ_apply'] using hk⟩
  rw [fixed_chain (⟨monotone_nat_of_le_succ steps, data⟩ : Tracks f s), fixedPoints.lfp_eq_sSup_iterate _ hg]

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

def retryTail (weighted : Bool) (r : Option ℝ) (d : D α) : Option (D α) :=
  if weighted then weightValue (some (fun _ => r)) (some d) else scaleValue r (some d)

private theorem tail_step (weighted : Bool) {d : D α} {k : Model α} (hd : Presents d k) {r : ℝ} (hr : 0 ≤ r) :
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

theorem fixed_retry (swap weighted : Bool) {r : Option ℝ} (q : ℚ) (h0 : 0 ≤ q) (hr : r = some (q : ℝ))
    {seed : Option (D α)} (hs : Admissible seed) {f : D α → Option (D α)}
    (body : ∀ d, f d = retryBody swap weighted r seed d) : fixedValue (some f) = retryValue r seed := by
  subst r
  cases seed with
  | none =>
    change fixedValue (some f) = none
    apply fixed_missing (n := 1)
    cases swap <;> cases weighted <;> simp [iterateBody, body, retryBody, retryTail, addValue, scaleValue, weightValue, weight]
  | some b =>
    obtain ⟨m, hb⟩ := hs b rfl
    have r0 : 0 ≤ (q : ℝ) := by exact_mod_cast h0
    rw [retry_eq_realize hb r0]
    apply fixed_of_step _ _ (strictRetry_continuous _ _)
    intro d k hd
    obtain ⟨e, he, htail, hvis⟩ := tail_step weighted hd r0
    cases swap with
    | false =>
      refine ⟨.add b e, by simp [body, retryBody, he, addValue], hb.1.add htail, ?_⟩
      exact (visited_add _ _).trans (congrArg₂ (· ∪ ·) hb.2 hvis)
    | true =>
      refine ⟨.add e b, by simp [body, retryBody, he, addValue], ?_, ?_⟩
      · simpa [strictRetryStep, retryStep, add_comm] using htail.add hb.1
      · exact (visited_add _ _).trans ((congrArg₂ (· ∪ ·) hvis hb.2).trans (Set.union_comm _ _))
end QSym.Distribution.Atomic
