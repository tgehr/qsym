import QSym.DistributionAtomicFixed

/-! The atomic weights alone forget a zero-weight visit, which qsym's strict
scalar pairing can observe. Record the visited outcomes as a second component. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal

/-- Detect a visit with a probe that is undefined at one outcome. -/
def visited (d : D α) : Set α := by
  classical exact {a | integrate d (fun x => if x = a then none else some 0) = none}

@[simp] theorem visited_zero : visited (.zero : D α) = ∅ := by ext x; simp [visited, integrate]
@[simp] theorem visited_dirac (x : α) : visited (.dirac x) = {x} := by
  classical
  ext y
  by_cases h : x = y <;> simp [visited, integrate, h, eq_comm]
@[simp] theorem visited_add (d e : D α) : visited (.add d e) = visited d ∪ visited e := by
  classical
  ext a
  let t : α → Option ℝ := fun x => if x = a then none else some 0
  change Value.add (integrate d t) (integrate e t) = none ↔ integrate d t = none ∨ integrate e t = none
  cases integrate d t <;> cases integrate e t <;> simp [Value.add]
@[simp] theorem visited_scale (r : ℝ) (d : D α) : visited (.scale r d) = visited d := by
  classical
  ext a
  let t : α → Option ℝ := fun x => if x = a then none else some 0
  change Value.mul (some r) (integrate d t) = none ↔ integrate d t = none
  cases integrate d t <;> simp [Value.mul]

private theorem test_union {a b : Set α} {p : α → Prop} :
    (∀ x ∈ a ∪ b, p x) ↔ (∀ x ∈ a, p x) ∧ (∀ x ∈ b, p x) :=
  ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun ⟨ha, hb⟩ x hx => hx.elim (ha x) (hb x)⟩

theorem Represents.defined_probe {d : D α} {k : Weights α} (h : Represents d k) (t : α → Option ℝ) :
    (integrate d t).isSome = true ↔ ∀ x ∈ visited d, (t x).isSome = true := by
  induction h with
  | zero => simp [integrate]
  | dirac a => simp [integrate]
  | add hd he ih jh =>
    rw [visited_add, test_union, ← ih, ← jh]
    change (Value.add _ _).isSome = true ↔ _
    cases integrate _ t <;> cases integrate _ t <;> simp [Value.add]
  | scale hr hd ih =>
    rw [visited_scale, ← ih]
    change (Value.mul _ _).isSome = true ↔ _
    cases integrate _ t <;> simp [Value.mul]

private theorem Represents.fill {d : D α} {k : Weights α} (h : Represents d k) (t : α → Option ℝ)
    (ht : ∀ x ∈ visited d, (t x).isSome = true) :
    integrate d t = integrate d (fun x => some ((t x).getD 0)) := by
  induction h with
  | zero => rfl
  | dirac a =>
    have ha := ht a (by simp)
    cases eq : t a <;> simp [integrate, eq] at ha ⊢
  | add hd he ih jh =>
    rw [visited_add, test_union] at ht
    simp only [integrate, ih ht.1, jh ht.2]
  | scale hr hd ih => simp only [integrate, ih (visited_scale _ _ ▸ ht)]

/-- A signed test is the difference of two total nonnegative tests. -/
private theorem Represents.split {d : D α} {k : Weights α} (h : Represents d k) (t : α → ℝ)
    {a b : ℝ} (ha : integrate d (fun x => some (max (t x) 0)) = some a)
    (hb : integrate d (fun x => some (max (-t x) 0)) = some b) :
    integrate d (fun x => some (t x)) = some (a-b) := by
  induction h generalizing a b with
  | zero =>
    simp only [integrate, Option.some.injEq] at ha hb ⊢
    linarith
  | dirac x =>
    simp only [integrate, Option.some.injEq] at ha hb ⊢
    rw [← ha, ← hb]
    rcases le_total 0 (t x) with hx | hx <;> simp [max_eq_left, max_eq_right, hx, neg_nonpos, neg_nonneg]
  | add hd he ih jh =>
    obtain ⟨v, hv, _, _⟩ := hd.pairing _ (fun x => le_max_right (t x) 0)
    obtain ⟨w, hw, _, _⟩ := hd.pairing _ (fun x => le_max_right (-t x) 0)
    obtain ⟨v', hv', _, _⟩ := he.pairing _ (fun x => le_max_right (t x) 0)
    obtain ⟨w', hw', _, _⟩ := he.pairing _ (fun x => le_max_right (-t x) 0)
    simp only [integrate, hv, hw, hv', hw', Value.add, Option.some.injEq] at ha hb
    simp only [integrate, ih hv hw, jh hv' hw', Value.add, Option.some.injEq]
    linarith
  | scale hr hd ih =>
    obtain ⟨v, hv, _, _⟩ := hd.pairing _ (fun x => le_max_right (t x) 0)
    obtain ⟨w, hw, _, _⟩ := hd.pairing _ (fun x => le_max_right (-t x) 0)
    simp only [integrate, hv, hw, Value.mul, Option.some.injEq] at ha hb
    simp only [integrate, ih hv hw, Value.mul, Option.some.injEq, mul_sub, ha, hb]

/-- Equality of the weights and visited sets suffices for every partial signed
scalar test of finite nonnegative atomic presentations. -/
theorem Represents.probe_eq {d e : D α} {k : Weights α} (hd : Represents d k) (he : Represents e k)
    (hvis : visited d = visited e) (t : α → Option ℝ) : integrate d t = integrate e t := by
  classical
  by_cases ht : ∀ x ∈ visited d, (t x).isSome = true
  · rw [hd.fill t ht, he.fill t (hvis ▸ ht)]
    let u := fun x => (t x).getD 0
    have same (v : α → ℝ) (hv : ∀ x, 0 ≤ v x) :
        ∃ m, integrate d (fun x => some (v x)) = some m ∧ integrate e (fun x => some (v x)) = some m := by
      obtain ⟨a, da, a0, ka⟩ := hd.pairing v hv
      obtain ⟨b, eb, b0, kb⟩ := he.pairing v hv
      have eq : a = b := by
        simpa [ENNReal.toReal_ofReal, a0, b0] using congrArg ENNReal.toReal (ka.symm.trans kb)
      exact ⟨a, da, eq ▸ eb⟩
    obtain ⟨a, da, ea⟩ := same _ (fun x => le_max_right (u x) 0)
    obtain ⟨b, db, eb⟩ := same _ (fun x => le_max_right (-u x) 0)
    exact (hd.split u da db).trans (he.split u ea eb).symm
  · have de := mt (hd.defined_probe t).mp ht
    have ee := mt (he.defined_probe t).mp (hvis ▸ ht)
    simp at de ee
    exact de.trans ee.symm

abbrev Model (α : Type) := Weights α × Set α

def Presents (d : D α) (m : Model α) := Represents d m.1 ∧ visited d = m.2

private theorem Represents.at_point {d : D α} {k : Weights α} (hd : Represents d k) (x : α)
    [DecidableEq α] :
    ∃ v : ℝ, integrate d (fun a => some (if a=x then 1 else 0)) = some v ∧ ENNReal.ofReal v = k x := by
  let t := fun a : α => if a=x then (1 : ℝ) else 0
  obtain ⟨v, hv, _, w⟩ := hd.pairing t (fun a => by dsimp [t]; split <;> norm_num)
  refine ⟨v, hv, w.symm.trans ?_⟩
  rw [tsum_eq_single x (fun a ha => by simp [t, ha])]
  simp [t]

/-- On finite nonnegative atomic presentations the model captures exactly
equality of all partial signed scalar observations. -/
theorem Presents.eq_iff {d e : D α} {m n : Model α} (hd : Presents d m) (he : Presents e n) :
    m = n ↔ ∀ t : α → Option ℝ, integrate d t = integrate e t := by
  classical
  constructor
  · rintro rfl
    exact hd.1.probe_eq he.1 (hd.2.trans he.2.symm)
  · intro obs
    refine Prod.ext (funext fun x => ?_) ?_
    · obtain ⟨v, hv, kv⟩ := hd.1.at_point x
      obtain ⟨w, hw, kw⟩ := he.1.at_point x
      have eq := (hv.symm.trans (obs _)).trans hw
      exact (kv.symm.trans (congrArg ENNReal.ofReal (Option.some.inj eq))).trans kw
    · rw [← hd.2, ← he.2]
      ext x
      exact Iff.of_eq (congrArg (· = none) (obs _))

/-- The recursive branch visits its continuation even with coefficient zero,
because multiplication of scalar observations is strict. -/
def strictRetryStep (b : Model α) (r : ℝ≥0∞) : Model α →o Model α where
  toFun k := (retryStep b.1 r k.1, b.2 ∪ k.2)
  monotone' _ _ h := ⟨(retryStep b.1 r).monotone h.1, Set.union_subset_union_right _ h.2⟩

theorem strictRetry_lfp (b : Model α) (r : ℝ≥0∞) :
    (strictRetryStep b r).lfp = ((retryStep b.1 r).lfp, b.2) := by
  apply le_antisymm
  · apply OrderHom.lfp_le_fixed
    exact Prod.ext (OrderHom.map_lfp _) (Set.union_self _)
  · apply OrderHom.le_lfp
    intro k hk
    exact ⟨(retryStep b.1 r).lfp_le hk.1, fun _ hx => hk.2 (Or.inl hx)⟩

/-- A single scaled copy of the seed presents the least fixed point, with
both outcome weights and the domains of partial probes. -/
theorem Presents.retry {d : D α} {m : Model α} (hd : Presents d m) {r : ℝ}
    (h0 : 0 ≤ r) (h1 : r < 1) :
    Presents (.scale (1-r)⁻¹ d) (strictRetryStep m (ENNReal.ofReal r)).lfp := by
  rw [strictRetry_lfp]
  exact ⟨hd.1.retry h0 h1, (visited_scale _ _).trans hd.2⟩

theorem Presents.unfold_retry {d : D α} {m : Model α} (hd : Presents d m) {r : ℝ}
    (h0 : 0 ≤ r) (h1 : r < 1) (t : α → Option ℝ) :
    let result := Presentation.scale (1-r)⁻¹ d
    integrate result t = integrate (.add d (.scale r result)) t := by
  let step := strictRetryStep m (ENNReal.ofReal r)
  have hr : Presents (.scale (1-r)⁻¹ d) step.lfp := hd.retry h0 h1
  have hu : Presents (.add d (.scale r (.scale (1-r)⁻¹ d))) (step step.lfp) :=
    ⟨hd.1.add (hr.1.scale h0), by
      change visited (.add d _) = m.2 ∪ step.lfp.2
      rw [visited_add, visited_scale r, hd.2, hr.2]⟩
  rw [step.map_lfp] at hu
  exact (hr.eq_iff hu).mp rfl t

end QSym.Distribution.Atomic
