import QSym.DistributionAtomicInfinite

/-! Interpretation of an atomic retry as a least fixed point. A model with a
single visited point has a unique weighted-atom normal form, including at
weight zero. More general finite models use a representative of their complete
partial-probe semantics. When the limit has several visits and unbounded mass,
keep the countable series of increments of the finite approximants. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal

private def point (c : ℝ) (a : α) : D α := if c = 1 then .dirac a else .scale c (.dirac a)

private inductive Simple : D α → Prop where
  | zero : Simple .zero
  | point (c : ℝ) (a : α) : Simple (Atomic.point c a)

private theorem point_visited (w : ℝ) (a : α) : visited (point w a) = {a} := by
  by_cases h : w = 1 <;> simp [point, h]

private theorem point_mass (w : ℝ) (a : α) : integrate (point w a) (fun _ => some 1) = some w := by
  by_cases h : w = 1 <;> simp [point, h, integrate, Value.mul]

private theorem simple_unique {d e : D α} {m : Model α} (hd : Presents d m) (he : Presents e m)
    (sd : Simple d) (se : Simple e) : d = e := by
  have hv := hd.2.trans he.2.symm
  have hm := (hd.eq_iff he).mp rfl (fun _ => some 1)
  cases sd <;> cases se
  · rfl
  · rw [visited_zero, point_visited] at hv
    exact False.elim ((Set.singleton_ne_empty _) hv.symm)
  · simp [visited_zero, point_visited] at hv
  · simp only [point_visited, Set.singleton_eq_singleton_iff] at hv
    simp only [point_mass, Option.some.injEq] at hm
    rw [hv, hm]

/-- The result depends only on the outcome weights and the visited set. -/
def realize (m : Model α) : Option (D α) := by
  classical
  exact if s : ∃ d, Presents d m ∧ Simple d then some s.choose else
    if h : ∃ d, Presents d m then some h.choose else
    if i : ∃ a, m = infiniteModel a then some (infiniteAtom i.choose) else none

theorem realize_presents {d : D α} {m : Model α} (hd : Presents d m) :
    ∃ e, realize m = some e ∧ Presents e m := by
  classical
  unfold realize
  split
  next h => exact ⟨_, rfl, h.choose_spec.1⟩
  next =>
    have h : ∃ d, Presents d m := ⟨d, hd⟩
    rw [dif_pos h]
    exact ⟨_, rfl, h.choose_spec⟩

private theorem realize_simple {d : D α} {m : Model α} (hd : Presents d m) (sd : Simple d) :
    realize m = some d := by
  classical
  have h : ∃ e, Presents e m ∧ Simple e := ⟨d, hd, sd⟩
  rw [realize, dif_pos h, simple_unique h.choose_spec.1 hd h.choose_spec.2 sd]

theorem realize_eq_none_of_infinite_visits {m : Model α} {a b c : α}
    (ha : m.1 a = ⊤) (hb : b ∈ m.2) (hc : c ∈ m.2) (hne : b ≠ c) : realize m = none := by
  classical
  have finite : ¬ ∃ d, Presents d m := fun ⟨_, hd⟩ => hd.1.finite_weight a ha
  have simple : ¬ ∃ d, Presents d m ∧ Simple d := fun ⟨d, hd, _⟩ => finite ⟨d, hd⟩
  have singleton : ¬ ∃ x, m = infiniteModel x := by
    rintro ⟨x, rfl⟩
    exact hne ((Set.mem_singleton_iff.mp hb).trans (Set.mem_singleton_iff.mp hc).symm)
  simp [realize, simple, finite, singleton]

private theorem realize_infinite (a : α) : realize (infiniteModel a) = some (infiniteAtom a) := by
  classical
  have h : ¬ ∃ d, Presents d (infiniteModel a) := by
    rintro ⟨d, hd⟩
    simpa [infiniteModel, atom] using hd.1.finite_weight a
  have hs : ¬ ∃ d, Presents d (infiniteModel a) ∧ Simple d := fun ⟨d, hd, _⟩ => h ⟨d, hd⟩
  have i : ∃ b, infiniteModel a = infiniteModel b := ⟨a, rfl⟩
  have eq : a = i.choose := Set.singleton_eq_singleton_iff.mp (congrArg Prod.snd i.choose_spec)
  simp [realize, hs, h, i, ← eq]

theorem realize_cases (m : Model α) :
    (∃ d, realize m = some d ∧ Presents d m) ∨
    (∃ a, m = infiniteModel a ∧ realize m = some (infiniteAtom a)) ∨ realize m = none := by
  classical
  by_cases finite : ∃ d, Presents d m
  · exact Or.inl (realize_presents finite.choose_spec)
  · by_cases single : ∃ a, m = infiniteModel a
    · obtain ⟨a, rfl⟩ := single
      exact Or.inr (Or.inl ⟨a, rfl, realize_infinite a⟩)
    · have simple : ¬ ∃ d, Presents d m ∧ Simple d := fun ⟨d, hd, _⟩ => finite ⟨d, hd⟩
      exact Or.inr (Or.inr (by simp [realize, simple, finite, single]))

def incrementSeries (v : ℕ → Option (D α)) : Option (D α) :=
  sumNatValue (some (fun n => addValue (v (n+1)) (scaleValue (some (-1)) (v n))))

/-- Finite models and infinite singletons have direct presentations. For other
limits, keep the change in weights and visits at each depth together. -/
def realizeChain (m : Model α) (s : ℕ → Model α) : Option (D α) :=
  (realize m).orElse fun _ => incrementSeries (fun n => realize (s n))

theorem realizeChain_of_some {m : Model α} {d : D α} (h : realize m = some d) (s : ℕ → Model α) :
    realizeChain m s = some d := by rw [realizeChain, h]; rfl

theorem realizeChain_defined (m : Model α) (s : ℕ → Model α) : (realizeChain m s).isSome = true := by
  cases h : realize m <;> rw [realizeChain, h] <;> rfl

private def modelOf (d : D α) : Option (Model α) := by
  classical exact if h : ∃ m, Presents d m then some h.choose else none

private theorem modelOf_eq {d : D α} {m : Model α} (hd : Presents d m) : modelOf d = some m := by
  classical
  have h : ∃ m, Presents d m := ⟨m, hd⟩
  rw [modelOf, dif_pos h, (h.choose_spec.eq_iff hd).mpr (fun _ => rfl)]

/-- Denotation of the source fragment `μ X. seed + r · X`. -/
def retryValue (ratio : Option ℝ) (seed : Option (D α)) : Option (D α) := do
  let r ← ratio
  let d ← seed
  let m ← modelOf d
  let g := strictRetryStep m (ENNReal.ofReal r)
  if 0 ≤ r then realizeChain g.lfp (fun n => g^[n] ⊥) else none

theorem retry_eq_chain {d : D α} {m : Model α} (hd : Presents d m) {r : ℝ} (h0 : 0 ≤ r) :
    let g := strictRetryStep m (ENNReal.ofReal r)
    retryValue (some r) (some d) = realizeChain g.lfp (fun n => g^[n] ⊥) := by
  simp [retryValue, modelOf_eq hd, h0]

/-- Every successful evaluation of this source term yields finite nonnegative
atomic data. A Dirac point may itself be a function, a type, or a distribution. -/
def Admissible (v : Option (D α)) := ∀ d, v = some d → ∃ m, Presents d m

private theorem represented {d : D α} {k : Weights α} (h : Represents d k) : ∃ m, Presents d m :=
  ⟨(k, visited d), h, rfl⟩

theorem admissible_none : Admissible (none : Option (D α)) := by simp [Admissible]
theorem retry_missing (r : Option ℝ) : retryValue r (none : Option (D α)) = none := by cases r <;> rfl

theorem admissible_zero : Admissible (zeroValue (α := α)) := by
  rintro _ ⟨⟩
  exact represented Represents.zero

theorem admissible_dirac (v : Option α) : Admissible (diracValue v) := by
  cases v with
  | none => simp [Admissible, diracValue]
  | some a =>
    rintro _ ⟨⟩
    exact represented (Represents.dirac a)

theorem admissible_add {x y : Option (D α)} (hx : Admissible x) (hy : Admissible y) : Admissible (addValue x y) := by
  cases x with
  | none => simp [Admissible, addValue]
  | some a =>
    cases y with
    | none => simp [Admissible, addValue]
    | some b =>
      rintro _ ⟨⟩
      obtain ⟨k, ha⟩ := hx a rfl
      obtain ⟨l, hb⟩ := hy b rfl
      exact represented (ha.1.add hb.1)

theorem admissible_scale {x : Option (D α)} {w : Option ℝ} (c : ℚ) (hc : 0 ≤ c)
    (hw : w = some (c : ℝ)) (hx : Admissible x) : Admissible (scaleValue w x) := by
  subst w
  cases x with
  | none => simp [Admissible, scaleValue]
  | some a =>
    rintro _ ⟨⟩
    obtain ⟨k, ha⟩ := hx a rfl
    exact represented (ha.1.scale (r := (c : ℝ)) (by exact_mod_cast hc))

theorem retry_isSome {r : Option ℝ} (q : ℚ) (h0 : 0 ≤ q) (hr : r = some (q : ℝ))
    {seed : Option (D α)} (hs : Admissible seed) :
    (retryValue r seed).isSome = seed.isSome := by
  subst r
  cases seed with
  | none => rfl
  | some d =>
    obtain ⟨m, hm⟩ := hs d rfl
    rw [retry_eq_chain hm (by exact_mod_cast h0)]
    exact realizeChain_defined _ _

theorem observe_retry (observe : D α → Option β)
    (invariant : ∀ {d e : D α} {m : Model α}, Presents d m → Presents e m → observe d = observe e)
    {ratio gain : Option ℝ} (r c : ℚ) (h0 : 0 ≤ r) (h1 : r < 1) (hc : c = (1-r)⁻¹)
    (hr : ratio = some (r : ℝ)) (hk : gain = some (c : ℝ)) {seed : Option (D α)} (hs : Admissible seed) :
    (retryValue ratio seed).bind observe = (scaleValue gain seed).bind observe := by
  subst ratio gain c
  cases seed with
  | none => rfl
  | some d =>
    obtain ⟨m, hd⟩ := hs d rfl
    have r0 : 0 ≤ (r : ℝ) := by exact_mod_cast h0
    have result := hd.retry r0 (by exact_mod_cast h1)
    obtain ⟨e, eq, he⟩ := realize_presents result
    rw [retry_eq_chain hd r0, realizeChain_of_some eq]
    simpa [scaleValue] using invariant he result

theorem mass_retry {r g : Option ℝ} (q c : ℚ) (h0 : 0 ≤ q) (h1 : q < 1) (hc : c = (1-q)⁻¹)
    (hr : r = some (q : ℝ)) (hg : g = some (c : ℝ)) {s : Option (D α)} (hs : Admissible s) :
    massValue (retryValue r s) = massValue (scaleValue g s) :=
  observe_retry (fun d => integrate d (fun _ => some 1))
    (fun hd he => (hd.eq_iff he).mp rfl _) q c h0 h1 hc hr hg hs

theorem density_retry {r g : Option ℝ} (q c : ℚ) (h0 : 0 ≤ q) (h1 : q < 1) (hc : c = (1-q)⁻¹)
    (hr : r = some (q : ℝ)) (hg : g = some (c : ℝ)) {s : Option (D ℝ)} (hs : Admissible s) (x : Option ℝ) :
    densityAtValue (retryValue r s) x = densityAtValue (scaleValue g s) x :=
  observe_retry (fun d => x.bind (densityAt d)) (fun hd he => by
    cases x with
    | none => rfl
    | some p => exact (hd.1.density p).trans (he.1.density p).symm) q c h0 h1 hc hr hg hs

private def pointModel (w : ℝ) (a : α) : Model α := (fun x => ENNReal.ofReal w * atom a x, {a})

private theorem point_presents {w : ℝ} (hw : 0 ≤ w) (a : α) : Presents (point w a) (pointModel w a) := by
  refine ⟨?_, point_visited w a⟩
  by_cases h : w=1
  · simpa [point, pointModel, h] using Represents.dirac a
  · simpa [point, pointModel, h] using (Represents.dirac a).scale hw

/-- A certificate for all visits to the same source point. The outcome can
be undefined, in which case constructing its seed also fails. -/
def PointSeed (s : Option (D α)) (w : ℚ) (p : Option α) : Prop :=
  match p with
  | none => s = none
  | some a => ∃ d, s = some d ∧ Presents d (pointModel w a)

theorem point_dirac (p : Option α) : PointSeed (diracValue p) 1 p := by
  cases p with
  | none => rfl
  | some a => exact ⟨_, rfl, by simpa [point, pointModel] using point_presents zero_le_one a⟩

theorem point_scale {s : Option (D α)} {p : Option α} {w : ℚ} {mass : Option ℝ}
    (c z : ℚ) (hc : 0 ≤ c) (hz : z = c*w) (hm : mass = some (c : ℝ)) (h : PointSeed s w p) :
    PointSeed (scaleValue mass s) z p := by
  subst mass z
  cases p with
  | none => change s = none at h; rw [h]; rfl
  | some a =>
    obtain ⟨d, rfl, hd⟩ := h
    refine ⟨_, rfl, ?_, (visited_scale _ _).trans hd.2⟩
    have hr : 0 ≤ (c : ℝ) := by exact_mod_cast hc
    simpa [pointModel, ENNReal.ofReal_mul hr, mul_assoc] using hd.1.scale hr

theorem one_weight : some (1 : ℝ) = some ((1 : ℚ) : ℝ) := by norm_num

theorem retry_point {s : Option (D α)} {p : Option α} {ratio weight : Option ℝ}
    (q w z : ℚ) (h0 : 0 ≤ q) (h1 : q < 1) (hw : 0 ≤ w) (hz : z = (1-q)⁻¹*w)
    (hr : ratio = some (q : ℝ)) (hv : weight = some (z : ℝ)) (seed : PointSeed s w p) :
    retryValue ratio s = if z=1 then diracValue p else scaleValue weight (diracValue p) := by
  subst ratio weight
  cases p with
  | none =>
    change s = none at seed
    rw [seed]
    split <;> rfl
  | some a =>
    obtain ⟨d, rfl, hd⟩ := seed
    have r0 : 0 ≤ (q : ℝ) := by exact_mod_cast h0
    have r1 : (q : ℝ) < 1 := by exact_mod_cast h1
    have gain : 0 < 1-(q : ℝ) := sub_pos.mpr r1
    have z0 : 0 ≤ z := hz ▸ mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr h1.le)) hw
    have he : (strictRetryStep (pointModel (w : ℝ) a) (ENNReal.ofReal q)).lfp = pointModel (z : ℝ) a := by
      rw [strictRetry_lfp]
      refine Prod.ext (funext fun x => ?_) rfl
      change (retryStep _ _).lfp x = _
      rw [lfp_retry]
      simp [pointModel, hz, ENNReal.ofReal_mul (inv_nonneg.mpr gain.le), ENNReal.ofReal_inv_of_pos gain,
        ENNReal.ofReal_sub _ r0, mul_assoc]
    rw [retry_eq_chain hd r0, he, realizeChain_of_some (realize_simple (point_presents (by exact_mod_cast z0) a) (.point _ _))]
    by_cases h : z=1
    · simp [h, point, diracValue]
    · have h' : (z : ℝ) ≠ 1 := by exact_mod_cast h
      simp [h, h', point, diracValue, scaleValue]

theorem retry_zero {r : Option ℝ} (q : ℚ) (h0 : 0 ≤ q) (hr : r = some (q : ℝ)) :
    retryValue r (zeroValue (α := α)) = zeroValue := by
  subst r
  let m : Model α := (fun _ => 0, ∅)
  have h : Presents (.zero : D α) m := ⟨Represents.zero, visited_zero⟩
  have r0 : 0 ≤ (q : ℝ) := by exact_mod_cast h0
  change retryValue _ (some .zero) = some .zero
  rw [retry_eq_chain h r0]
  have he : (strictRetryStep m (ENNReal.ofReal q)).lfp = m := by
    rw [strictRetry_lfp]; exact Prod.ext (funext fun x => by simp [m, lfp_retry]) rfl
  rw [he, realizeChain_of_some (realize_simple h .zero)]

private abbrev emptyModel (α : Type) : Model α := (fun _ => 0, ∅)

/-- An atomic seed with no visited outcomes. A zero-weight atom still visits
its outcome and therefore cannot supply this certificate. -/
def EmptySeed (s : Option (D α)) := ∃ d, s = some d ∧ Presents d (emptyModel α)

theorem EmptySeed.zero : EmptySeed (zeroValue (α := α)) := ⟨_, rfl, Represents.zero, visited_zero⟩

theorem EmptySeed.add {s t : Option (D α)} (hs : EmptySeed s) (ht : EmptySeed t) : EmptySeed (addValue s t) := by
  obtain ⟨d, rfl, hd⟩ := hs
  obtain ⟨e, rfl, he⟩ := ht
  exact ⟨_, rfl, by simpa [emptyModel] using hd.1.add he.1, by simp [hd.2, he.2, emptyModel]⟩

theorem EmptySeed.scale {s : Option (D α)} {mass : Option ℝ} (c : ℚ) (hc : 0 ≤ c)
    (hm : mass = some (c : ℝ)) (hs : EmptySeed s) : EmptySeed (scaleValue mass s) := by
  subst mass
  obtain ⟨d, rfl, hd⟩ := hs
  have h0 : 0 ≤ (c : ℝ) := by exact_mod_cast hc
  exact ⟨_, rfl, by simpa [emptyModel] using hd.1.scale h0, (visited_scale _ _).trans hd.2⟩

theorem retry_empty {s : Option (D α)} {ratio : Option ℝ} (q : ℚ) (h0 : 0 ≤ q)
    (hr : ratio = some (q : ℝ)) (hs : EmptySeed s) : retryValue ratio s = zeroValue := by
  subst ratio
  obtain ⟨d, rfl, hd⟩ := hs
  have he : Presents (.zero : D α) (emptyModel α) := ⟨Represents.zero, visited_zero⟩
  have qr : 0 ≤ (q : ℝ) := by exact_mod_cast h0
  exact (retry_eq_chain hd qr).trans ((retry_eq_chain he qr).symm.trans (retry_zero q h0 rfl))

theorem point_add_empty {s t : Option (D α)} {p : Option α} {w : ℚ} (swap : Bool)
    (hs : PointSeed s w p) (ht : EmptySeed t) :
    PointSeed (if swap then addValue t s else addValue s t) w p := by
  obtain ⟨e, rfl, he⟩ := ht
  cases p with
  | none =>
    change s = none at hs
    subst s
    cases swap <;> rfl
  | some a =>
    obtain ⟨d, rfl, hd⟩ := hs
    cases swap with
    | false => exact ⟨_, rfl, by simpa [emptyModel, pointModel] using hd.1.add he.1,
        by simp [hd.2, he.2, emptyModel, pointModel]⟩
    | true => exact ⟨_, rfl, by simpa [emptyModel, pointModel] using he.1.add hd.1,
        by simp [hd.2, he.2, emptyModel, pointModel]⟩

theorem point_add {s t : Option (D α)} {p : Option α} {a b : ℚ} (z : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : z = a+b) (hs : PointSeed s a p) (ht : PointSeed t b p) :
    PointSeed (addValue s t) z p := by
  subst z
  cases p with
  | none =>
    change s = none at hs
    subst s
    rfl
  | some x =>
    obtain ⟨d, rfl, hd⟩ := hs
    obtain ⟨e, rfl, he⟩ := ht
    have a0 : 0 ≤ (a : ℝ) := by exact_mod_cast ha
    have b0 : 0 ≤ (b : ℝ) := by exact_mod_cast hb
    exact ⟨_, rfl, by simpa [pointModel, ENNReal.ofReal_add a0 b0, add_mul] using hd.1.add he.1,
      by simp [hd.2, he.2, pointModel]⟩

/-- Even a noncontracting loop has zero weight at a visited atom that never
receives positive mass. The visit remains observable by partial integrands. -/
theorem retry_zero_point {s : Option (D α)} {p : Option α} {r weight : Option ℝ}
    (q : ℚ) (h0 : 0 ≤ q) (hr : r = some (q : ℝ)) (hw : weight = some ((0 : ℚ) : ℝ))
    (hs : PointSeed s 0 p) : retryValue r s = scaleValue weight (diracValue p) := by
  subst r weight
  cases p with
  | none =>
    change s = none at hs
    rw [hs]
    rfl
  | some a =>
    obtain ⟨d, rfl, hd⟩ := hs
    simp only [Rat.cast_zero] at hd ⊢
    have h : (strictRetryStep (pointModel 0 a) (ENNReal.ofReal (q : ℝ))).lfp = pointModel 0 a := by
      rw [strictRetry_lfp]
      refine Prod.ext (funext fun x => ?_) rfl
      change (retryStep _ _).lfp x = _
      rw [lfp_retry]
      simp [pointModel]
    rw [retry_eq_chain hd (by exact_mod_cast h0), h, realizeChain_of_some (realize_simple (point_presents (le_refl 0) a) (.point _ _))]
    simp [point, diracValue, scaleValue]

/-- A positive emission at one point with a noncontracting return produces
infinitely many copies there. Constructing the outcome remains strict. -/
theorem retry_infinite_point {s : Option (D α)} {p : Option α} {ratio : Option ℝ}
    (q w : ℚ) (h1 : 1 ≤ q) (hw : 0 < w) (hr : ratio = some (q : ℝ)) (seed : PointSeed s w p) :
    retryValue ratio s = p.bind (fun _ => sumValue (some (fun _ : ℤ => diracValue p))) := by
  subst ratio
  cases p with
  | none =>
    change s=none at seed
    rw [seed]
    rfl
  | some a =>
    obtain ⟨d, rfl, hd⟩ := seed
    have q1 : (1 : ℝ) ≤ q := by exact_mod_cast h1
    have w0 : 0 < (w : ℝ) := by exact_mod_cast hw
    have r1 : 1 ≤ ENNReal.ofReal (q : ℝ) := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal q1
    have limit : (strictRetryStep (pointModel (w : ℝ) a) (ENNReal.ofReal q)).lfp = infiniteModel a := by
      rw [strictRetry_lfp]
      refine Prod.ext (funext fun x => ?_) rfl
      change (retryStep _ _).lfp x = _
      rw [lfp_retry, tsub_eq_zero_of_le r1, ENNReal.inv_zero]
      classical
      by_cases e : x=a <;> simp [pointModel, infiniteModel, atom, e, ENNReal.ofReal_ne_zero_iff.mpr w0]
    rw [retry_eq_chain hd (le_trans zero_le_one q1), limit, realizeChain_of_some (realize_infinite a)]
    rfl

end QSym.Distribution.Atomic
