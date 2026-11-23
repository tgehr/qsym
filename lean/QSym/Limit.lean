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

end QSym.Limit
