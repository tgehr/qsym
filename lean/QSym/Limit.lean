import QSym.Value
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Basic

/-! Limits of partial functions of a real variable along a filter, in
particular at `+∞` and at `-∞`. A limit is a value exactly when the function
is eventually defined and converges. A function that stays undefined
arbitrarily far out, diverges or oscillates has no limit: no conventional
value such as the one of `limUnder` is exposed. -/
namespace QSym.Limit
open Filter Topology

variable {α : Type} [TopologicalSpace α]

section Model
variable [Zero α]

/-- The limit of a partial function along a filter. Values at points where the
function is undefined do not matter once it is eventually defined. -/
noncomputable def along (l : Filter ℝ) (f : ℝ → Option α) : Option α := by
  classical
  exact if (∀ᶠ x in l, (f x).isSome) ∧ ∃ a, Tendsto (fun x => (f x).getD 0) l (𝓝 a)
    then some (limUnder l fun x => (f x).getD 0) else none

/-- The operator on function values: an undefined function has no limit. -/
noncomputable def value (l : Filter ℝ) (f : Option (ℝ → Option α)) : Option α :=
  f.bind (along l)

theorem along_eq_some_iff [T2Space α] {l : Filter ℝ} [l.NeBot] {f : ℝ → Option α} {a : α} :
    along l f = some a ↔
      (∀ᶠ x in l, (f x).isSome) ∧ Tendsto (fun x => (f x).getD 0) l (𝓝 a) := by
  classical
  unfold along
  constructor
  · intro h
    split_ifs at h with hc
    obtain ⟨hd, b, hb⟩ := hc
    rw [hb.limUnder_eq] at h
    cases h
    exact ⟨hd, hb⟩
  · rintro ⟨hd, ha⟩
    rw [if_pos ⟨hd, a, ha⟩, ha.limUnder_eq]

theorem along_eq_some [T2Space α] {l : Filter ℝ} [l.NeBot] {f : ℝ → Option α} {g : ℝ → α}
    {a : α} (h : ∀ᶠ x in l, f x = some (g x)) (hg : Tendsto g l (𝓝 a)) :
    along l f = some a :=
  along_eq_some_iff.2 ⟨h.mono fun x hx => by simp [hx],
    hg.congr' (h.mono fun x hx => by simp [hx])⟩

theorem along_eq_none {l : Filter ℝ} {f : ℝ → Option α} (h : ∃ᶠ x in l, f x = none) :
    along l f = none := by
  classical
  unfold along
  rw [if_neg]
  rintro ⟨hd, -⟩
  exact h (hd.mono fun x hx hn => by simp [hn] at hx)

/-- Only the germ of the function at the filter matters. -/
theorem along_congr {l : Filter ℝ} {f g : ℝ → Option α} (h : ∀ᶠ x in l, f x = g x) :
    along l f = along l g := by
  classical
  have hd : (∀ᶠ x in l, (f x).isSome) ↔ ∀ᶠ x in l, (g x).isSome :=
    eventually_congr (h.mono fun x hx => by rw [hx])
  have hv : (fun x => (f x).getD 0) =ᶠ[l] fun x => (g x).getD 0 := h.mono fun x hx => by
    show (f x).getD 0 = (g x).getD 0
    rw [hx]
  have ht : ∀ a, Tendsto (fun x => (f x).getD 0) l (𝓝 a) ↔
      Tendsto (fun x => (g x).getD 0) l (𝓝 a) := fun a => tendsto_congr' hv
  unfold along
  simp only [hd, ht]
  split_ifs
  · show some (lim (map _ l)) = some (lim (map _ l))
    rw [map_congr hv]
  · rfl

end Model

/-- A limit together with its reason: convergence where the function is
eventually defined, or no value because it is eventually undefined. There is
no such evidence for a function that is defined and has no limit, so rules
built from it never assign a value to a divergent expression. -/
def Exact (l : Filter ℝ) (f : ℝ → Option α) : Option α → Prop
  | some a => ∃ g : ℝ → α, (∀ᶠ x in l, f x = some (g x)) ∧ Tendsto g l (𝓝 a)
  | none => ∀ᶠ x in l, f x = none

theorem Exact.sound [Zero α] [T2Space α] {l : Filter ℝ} [l.NeBot] {f : ℝ → Option α} {out : Option α}
    (h : Exact l f out) : along l f = out := by
  cases out with
  | none => exact along_eq_none (Eventually.frequently h)
  | some a => obtain ⟨g, hg, ht⟩ := h; exact along_eq_some hg ht

/-- A value that does not mention the variable is its own limit, defined or not. -/
theorem Exact.const (l : Filter ℝ) (c : Option α) : Exact l (fun _ => c) c := by
  cases c with
  | none => exact Eventually.of_forall fun _ => rfl
  | some a => exact ⟨fun _ => a, Eventually.of_forall fun _ => rfl, tendsto_const_nhds⟩

theorem Exact.congr {l : Filter ℝ} {f g : ℝ → Option α} {out : Option α}
    (h : Exact l f out) (hg : ∀ᶠ x in l, g x = f x) : Exact l g out := by
  cases out with
  | none => exact (hg.and h).mono fun x hx => hx.1.trans hx.2
  | some a =>
    obtain ⟨u, hu, ht⟩ := h
    exact ⟨u, (hg.and hu).mono fun x hx => hx.1.trans hx.2, ht⟩

theorem Exact.add [Add α] [ContinuousAdd α] {l : Filter ℝ} {f g : ℝ → Option α}
    {a b : Option α} (hf : Exact l f a) (hg : Exact l g b) :
    Exact l (fun x => Value.add (f x) (g x)) (Value.add a b) := by
  cases a with
  | none => exact hf.mono fun x hx => by simp [hx, Value.add]
  | some a =>
    cases b with
    | none => exact hg.mono fun x hx => by cases hfx : f x <;> simp [hx, Value.add]
    | some b =>
      obtain ⟨u, hu, htu⟩ := hf
      obtain ⟨w, hw, htw⟩ := hg
      exact ⟨fun x => u x + w x, (hu.and hw).mono fun x hx => by simp [hx.1, hx.2, Value.add],
        htu.add htw⟩

theorem Exact.mul [Mul α] [ContinuousMul α] {l : Filter ℝ} {f g : ℝ → Option α}
    {a b : Option α} (hf : Exact l f a) (hg : Exact l g b) :
    Exact l (fun x => Value.mul (f x) (g x)) (Value.mul a b) := by
  cases a with
  | none => exact hf.mono fun x hx => by simp [hx, Value.mul]
  | some a =>
    cases b with
    | none => exact hg.mono fun x hx => by cases hfx : f x <;> simp [hx, Value.mul]
    | some b =>
      obtain ⟨u, hu, htu⟩ := hf
      obtain ⟨w, hw, htw⟩ := hg
      exact ⟨fun x => u x * w x, (hu.and hw).mono fun x hx => by simp [hx.1, hx.2, Value.mul],
        htu.mul htw⟩

theorem Exact.pow [Monoid α] [ContinuousMul α] {l : Filter ℝ} {f : ℝ → Option α}
    {a : Option α} (n : ℕ) (hf : Exact l f a) :
    Exact l (fun x => (f x).map (fun y : α => y ^ n)) (a.map (fun y : α => y ^ n)) := by
  cases a with
  | none => exact hf.mono fun x hx => by simp [hx]
  | some a =>
    obtain ⟨u, hu, ht⟩ := hf
    exact ⟨fun x => u x ^ n, hu.mono fun x hx => by simp [hx], ht.pow n⟩

/-- Eventually equal to one value along the filter. Unlike convergence this
is preserved by every operation, so a term whose leaves are eventually
constant is eventually constant. -/
def Eventual {β : Type} (l : Filter ℝ) (p : ℝ → β) (g : β) : Prop := ∀ᶠ x in l, p x = g

theorem Eventual.const {β : Type} (l : Filter ℝ) (g : β) : Eventual l (fun _ => g) g :=
  Eventually.of_forall fun _ => rfl

theorem Eventual.unary {β γ : Type} {l : Filter ℝ} (op : β → γ) {p : ℝ → β} {g : β}
    (h : Eventual l p g) : Eventual l (fun x => op (p x)) (op g) :=
  h.mono fun _ hx => congrArg op hx

theorem Eventual.binary {β γ δ : Type} {l : Filter ℝ} (op : β → γ → δ) {p : ℝ → β}
    {q : ℝ → γ} {g : β} {h : γ} (hp : Eventual l p g) (hq : Eventual l q h) :
    Eventual l (fun x => op (p x) (q x)) (op g h) :=
  (hp.and hq).mono fun _ hx => congrArg₂ op hx.1 hx.2

/-- The limit of an eventually constant term is its eventual value. -/
theorem Exact.of_eventual {l : Filter ℝ} {f : ℝ → Option α} {g : Option α}
    (h : Eventual l f g) : Exact l f g := by
  cases g with
  | none => exact h
  | some a => exact ⟨fun _ => a, h, tendsto_const_nhds⟩

/-- A guard that is eventually decided masks the limit of its value. The mask
is not strict: behind a guard that is eventually false nothing is asked of
the value, and a guard that is eventually undefined leaves no limit. -/
theorem Exact.mask [Zero α] {l : Filter ℝ} {p : ℝ → Option Bool} {g : Option Bool}
    {f : ℝ → Option α} {out : Option α} (hp : Eventual l p g) (hf : Exact l f out) :
    Exact l (fun x => Value.mask (p x) (f x)) (Value.mask g out) := by
  have hm : ∀ᶠ x in l, Value.mask (p x) (f x) = Value.mask g (f x) :=
    hp.mono fun x hx => by rw [hx]
  rcases g with _ | _ | _
  · exact hm
  · exact ⟨fun _ => 0, hm, tendsto_const_nhds⟩
  · exact hf.congr hm

omit [TopologicalSpace α] in
/-- Behind a guard that is eventually never true nothing is asked of the
value: the mask is eventually zero where the guard is false and undefined
where it is. Any value stands for the masked one. -/
theorem Eventual.mask_never [Zero α] {l : Filter ℝ} {p : ℝ → Option Bool} {g : Option Bool}
    (hp : Eventual l p g) (hg : g ≠ some true) (w : ℝ → Option α) (out : Option α) :
    Eventual l (fun x => Value.mask (p x) (w x)) (Value.mask g out) := by
  refine hp.mono fun x hx => ?_
  show Value.mask (p x) (w x) = Value.mask g out
  rw [hx]
  rcases g with _ | _ | _
  · rfl
  · rfl
  · exact absurd rfl hg

theorem never_false {g : Option Bool} (h : g = some false) : g ≠ some true := by
  rw [h]; simp

theorem never_bound {β : Type} (a : Option β) {z : Option Bool} (h : z = some false) :
    (a.bind fun _ => z) ≠ some true := by
  subst h
  cases a <;> simp

/-- Which side of every real number the filter ends up on: `true` above. -/
def Above (l : Filter ℝ) (t : Bool) : Prop :=
  ∀ a : ℝ, ∀ᶠ x in l, decide (a ≤ x) = t ∧ decide (a < x) = t ∧
    decide (x ≤ a) = !t ∧ decide (x < a) = !t

theorem above_atTop : Above atTop true := fun a =>
  (eventually_gt_atTop a).mono fun x hx => by
    simp [hx, hx.le, not_le.2 hx, not_lt.2 hx.le]

theorem above_atBot : Above atBot false := fun a =>
  (eventually_lt_atBot a).mono fun x hx => by
    simp [hx, hx.le, not_le.2 hx, not_lt.2 hx.le]

/-- The variable against a bound that does not mention it: the comparison is
eventually decided wherever the bound is defined, and undefined with it. -/
theorem Eventual.bound_le {l : Filter ℝ} {t : Bool} (h : Above l t) (a : Option ℝ)
    {z : Option Bool} (hz : z = some t) :
    Eventual l (fun x => Value.le a (some x)) (a.bind fun _ => z) := by
  subst hz
  cases a with
  | none => exact Eventually.of_forall fun _ => rfl
  | some a =>
    refine (h a).mono fun x hx => ?_
    show some (decide (a ≤ x)) = some t
    rw [hx.1]

theorem Eventual.bound_lt {l : Filter ℝ} {t : Bool} (h : Above l t) (a : Option ℝ)
    {z : Option Bool} (hz : z = some t) :
    Eventual l (fun x => Value.lt a (some x)) (a.bind fun _ => z) := by
  subst hz
  cases a with
  | none => exact Eventually.of_forall fun _ => rfl
  | some a =>
    refine (h a).mono fun x hx => ?_
    show some (decide (a < x)) = some t
    rw [hx.2.1]

theorem Eventual.le_bound {l : Filter ℝ} {t : Bool} (h : Above l t) (a : Option ℝ)
    {z : Option Bool} (hz : z = some (!t)) :
    Eventual l (fun x => Value.le (some x) a) (a.bind fun _ => z) := by
  subst hz
  cases a with
  | none => exact Eventually.of_forall fun _ => rfl
  | some a =>
    refine (h a).mono fun x hx => ?_
    show some (decide (x ≤ a)) = some (!t)
    rw [hx.2.2.1]

theorem Eventual.lt_bound {l : Filter ℝ} {t : Bool} (h : Above l t) (a : Option ℝ)
    {z : Option Bool} (hz : z = some (!t)) :
    Eventual l (fun x => Value.lt (some x) a) (a.bind fun _ => z) := by
  subst hz
  cases a with
  | none => exact Eventually.of_forall fun _ => rfl
  | some a =>
    refine (h a).mono fun x hx => ?_
    show some (decide (x < a)) = some (!t)
    rw [hx.2.2.2]

end QSym.Limit
