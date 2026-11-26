import QSym.DistributionInterval

/-! Several bounds of the axis on one side. A guard is a conjunction of
comparisons, evaluated from the left, or as many nested masks: a bound whose
term is missing makes the weight missing only where the comparisons before it
hold. So a bound leaves the guard by a case distinction on the order of the
two terms on its side, and that distinction is under the mask of the bounds
before it wherever those can exclude every point.

Two bounds on one side at the front: a half-line is never empty, and the
observation is the sum of the two cases. A third bound after a lower and an
upper one: the two cases are under the mask of the order of those two. What
the masks hide, the rest of the guard with the value, is arbitrary, and each
case is an observation with one bound less. These are equations of partial
values for every definedness pattern of the terms and of the observations. -/
noncomputable section
namespace QSym.Distribution.StepSource
open MeasureTheory Set

/-- A bound of the axis by a partial value, from below or from above. -/
def axisBound (lower strict : Bool) (t : Option ℝ) (x : ℝ) : Option Bool :=
  match lower with
  | true => compare strict t (some x)
  | false => compare strict (some x) t

/-- Of two bounds on one side, the first implies the second. -/
def boundImplies (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) : Option Bool :=
  match lower with
  | true => compare (!s₁ && s₂) t₂ t₁
  | false => compare (!s₁ && s₂) t₁ t₂

/-- The negation: then the second implies the first. -/
def boundImplied (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) : Option Bool :=
  match lower with
  | true => compare (s₁ || !s₂) t₁ t₂
  | false => compare (s₁ || !s₂) t₂ t₁

/-- A bound and one on the other side leave a point between them. -/
def boundsMeet (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) : Option Bool :=
  match lower with
  | true => compare (s₁ || s₂) t₁ t₂
  | false => compare (s₁ || s₂) t₂ t₁

private def holds (s : Bool) (a b : ℝ) : Prop := if s = true then a < b else a ≤ b

private instance (s : Bool) (a b : ℝ) : Decidable (holds s a b) := by
  unfold holds; infer_instance

private theorem compare_real (s : Bool) (a b : ℝ) :
    compare s (some a) (some b) = some (decide (holds s a b)) := by
  cases s <;> simp [compare, Value.lt, Value.le, holds]

private theorem compare_missing_left (s : Bool) (b : Option ℝ) : compare s none b = none := by
  cases s <;> rfl

private theorem compare_missing_right (s : Bool) (a : Option ℝ) : compare s a none = none := by
  cases s <;> cases a <;> rfl

/-- A point satisfies a bound. -/
private def meets (lower s : Bool) (a x : ℝ) : Prop :=
  if lower = true then holds s a x else holds s x a

private instance (lower s : Bool) (a x : ℝ) : Decidable (meets lower s a x) := by
  unfold meets; infer_instance

private theorem axisBound_real (lower s : Bool) (a x : ℝ) :
    axisBound lower s (some a) x = some (decide (meets lower s a x)) := by
  cases lower <;> simp [axisBound, compare_real, meets]

private theorem axisBound_missing (lower s : Bool) (x : ℝ) : axisBound lower s none x = none := by
  cases lower
  · exact compare_missing_right s _
  · exact compare_missing_left s _

private theorem meets_beyond (lower s : Bool) (a : ℝ) : ∃ x, meets lower s a x := by
  cases lower
  · exact ⟨a - 1, by cases s <;> simp [meets, holds]⟩
  · exact ⟨a + 1, by cases s <;> simp [meets, holds]⟩

private def implies (lower s₁ s₂ : Bool) (a b : ℝ) : Prop :=
  if lower = true then holds (!s₁ && s₂) b a else holds (!s₁ && s₂) a b

private instance (lower s₁ s₂ : Bool) (a b : ℝ) : Decidable (implies lower s₁ s₂ a b) := by
  unfold implies; infer_instance

private theorem boundImplies_real (lower s₁ s₂ : Bool) (a b : ℝ) :
    boundImplies lower s₁ s₂ (some a) (some b) = some (decide (implies lower s₁ s₂ a b)) := by
  cases lower <;> simp [boundImplies, compare_real, implies]

private theorem decide_lt_not_le (a b : ℝ) : decide (b < a) = !decide (a ≤ b) := by
  by_cases h : a ≤ b
  · simp [h, not_lt.2 h]
  · simp [h, not_le.1 h]

private theorem decide_le_not_lt (a b : ℝ) : decide (b ≤ a) = !decide (a < b) := by
  by_cases h : a < b
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

private theorem boundImplied_real (lower s₁ s₂ : Bool) (a b : ℝ) :
    boundImplied lower s₁ s₂ (some a) (some b) = some (!decide (implies lower s₁ s₂ a b)) := by
  cases lower <;> cases s₁ <;> cases s₂ <;> simp [boundImplied, compare_real, implies, holds] <;>
    first | exact decide_lt_not_le _ _ | exact decide_le_not_lt _ _

private theorem boundImplies_missing_left (lower s₁ s₂ : Bool) (t : Option ℝ) :
    boundImplies lower s₁ s₂ none t = none := by
  cases lower
  · exact compare_missing_left _ _
  · exact compare_missing_right _ _

private theorem boundImplies_missing_right (lower s₁ s₂ : Bool) (t : Option ℝ) :
    boundImplies lower s₁ s₂ t none = none := by
  cases lower
  · exact compare_missing_right _ _
  · exact compare_missing_left _ _

private theorem meets_of_implies {lower s₁ s₂ : Bool} {a b x : ℝ}
    (h : implies lower s₁ s₂ a b) (hx : meets lower s₁ a x) : meets lower s₂ b x := by
  revert h hx
  cases lower <;> cases s₁ <;> cases s₂ <;> simp only [implies, meets, holds] <;> intro h hx <;>
    simp at h hx ⊢ <;> linarith

private theorem meets_of_not_implies {lower s₁ s₂ : Bool} {a b x : ℝ}
    (h : ¬ implies lower s₁ s₂ a b) (hx : meets lower s₂ b x) : meets lower s₁ a x := by
  revert h hx
  cases lower <;> cases s₁ <;> cases s₂ <;> simp only [implies, meets, holds] <;> intro h hx <;>
    simp at h hx ⊢ <;> linarith

private def between (lower s₁ s₂ : Bool) (a b : ℝ) : Prop :=
  if lower = true then holds (s₁ || s₂) a b else holds (s₁ || s₂) b a

private instance (lower s₁ s₂ : Bool) (a b : ℝ) : Decidable (between lower s₁ s₂ a b) := by
  unfold between; infer_instance

private theorem boundsMeet_real (lower s₁ s₂ : Bool) (a b : ℝ) :
    boundsMeet lower s₁ s₂ (some a) (some b) = some (decide (between lower s₁ s₂ a b)) := by
  cases lower <;> simp [boundsMeet, compare_real, between]

private theorem boundsMeet_missing_left (lower s₁ s₂ : Bool) (t : Option ℝ) :
    boundsMeet lower s₁ s₂ none t = none := by
  cases lower
  · exact compare_missing_right _ _
  · exact compare_missing_left _ _

private theorem boundsMeet_missing_right (lower s₁ s₂ : Bool) (t : Option ℝ) :
    boundsMeet lower s₁ s₂ t none = none := by
  cases lower
  · exact compare_missing_left _ _
  · exact compare_missing_right _ _

private theorem meets_between {lower s₁ s₂ : Bool} {a b : ℝ} (h : between lower s₁ s₂ a b) :
    meets lower s₁ a ((a + b) / 2) ∧ meets (!lower) s₂ b ((a + b) / 2) := by
  revert h
  cases lower <;> cases s₁ <;> cases s₂ <;> simp only [between, meets, holds] <;> intro h <;>
    simp at h ⊢ <;> constructor <;> linarith

private theorem between_of_meets {lower s₁ s₂ : Bool} {a b x : ℝ}
    (h₁ : meets lower s₁ a x) (h₂ : meets (!lower) s₂ b x) : between lower s₁ s₂ a b := by
  revert h₁ h₂
  cases lower <;> cases s₁ <;> cases s₂ <;> simp only [between, meets, holds] <;> intro h₁ h₂ <;>
    simp at h₁ h₂ ⊢ <;> linarith

private theorem mask_implied {p q : Prop} [Decidable p] [Decidable q] (h : p → q)
    (v : Option ℝ) :
    Value.mask (some (decide p)) (Value.mask (some (decide q)) v) =
      Value.mask (some (decide p)) v := by
  by_cases hp : p
  · simp [hp, h hp, Value.mask]
  · simp [hp, Value.mask]

private theorem mask_implying {p q : Prop} [Decidable p] [Decidable q] (h : q → p)
    (v : Option ℝ) :
    Value.mask (some (decide p)) (Value.mask (some (decide q)) v) =
      Value.mask (some (decide q)) v := by
  by_cases hq : q
  · simp [hq, h hq, Value.mask]
  · by_cases hp : p <;> simp [hp, hq, Value.mask]

private theorem mask_implied_far {p q s : Prop} [Decidable p] [Decidable q] [Decidable s]
    (h : p → s) (v : Option ℝ) :
    Value.mask (some (decide p)) (Value.mask (some (decide q)) (Value.mask (some (decide s)) v)) =
      Value.mask (some (decide p)) (Value.mask (some (decide q)) v) := by
  by_cases hp : p
  · simp [hp, h hp, Value.mask]
  · simp [hp, Value.mask]

private theorem mask_implying_far {p q s : Prop} [Decidable p] [Decidable q] [Decidable s]
    (h : s → p) (v : Option ℝ) :
    Value.mask (some (decide p)) (Value.mask (some (decide q)) (Value.mask (some (decide s)) v)) =
      Value.mask (some (decide s)) (Value.mask (some (decide q)) v) := by
  by_cases hs : s
  · simp [hs, h hs, Value.mask]
  · by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, hs, Value.mask]

/-- A guard as the conjunction of a list of guards, in their order. -/
def Conjunction (g : Option Bool) (ps : List (Option Bool)) : Prop :=
  g = ps.foldr Value.and (some true)

theorem Conjunction.one (p : Option Bool) : Conjunction p [p] := by
  rcases p with _ | _ | _ <;> rfl

theorem Conjunction.cons (p : Option Bool) {g : Option Bool} {ps : List (Option Bool)}
    (h : Conjunction g ps) : Conjunction (Value.and p g) (p :: ps) := by
  unfold Conjunction at h ⊢
  rw [h]
  rfl

/-- A conjunction is associative for every definedness pattern: it is
evaluated from the left however it is nested. -/
theorem Conjunction.and {g h : Option Bool} {ps qs : List (Option Bool)}
    (hg : Conjunction g ps) (hh : Conjunction h qs) :
    Conjunction (Value.and g h) (ps ++ qs) := by
  unfold Conjunction at *
  subst hg hh
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show Value.and (Value.and p (ps.foldr Value.and (some true))) _ =
      Value.and p ((ps ++ qs).foldr Value.and (some true))
    rw [← ih]
    rcases p with _ | _ | _ <;> rfl

/-- The mask of a conjunction is the masks of its guards in their order. -/
theorem Conjunction.mask {α : Type} [Zero α] {g : Option Bool} {ps : List (Option Bool)}
    (h : Conjunction g ps) (v : Option α) : Value.mask g v = ps.foldr Value.mask v := by
  unfold Conjunction at h
  subst h
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show Value.mask (Value.and p _) v = Value.mask p _
    rw [← ih, mask_mask]

/-- A partial value as the masks of a list of guards, in their order, around
what they hide. -/
def Masks (w : Option ℝ) (ps : List (Option Bool)) (r : Option ℝ) : Prop :=
  w = ps.foldr Value.mask r

theorem Masks.value (v : Option ℝ) : Masks v [] v := rfl

/-- A mask of a value that is such masks itself. -/
theorem Masks.mask {g : Option Bool} {ps qs : List (Option Bool)} {v r : Option ℝ}
    (hg : Conjunction g ps) (hv : Masks v qs r) : Masks (Value.mask g v) (ps ++ qs) r := by
  unfold Masks at *
  rw [hg.mask, hv, List.foldr_append]

/-- The cast of a bracket: the masks are around the cast of what it masks. -/
theorem Masks.bracket {g : Option Bool} {ps : List (Option Bool)} (hg : Conjunction g ps)
    (n : Option ℕ) :
    Masks (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply (Value.mask g n))))
      ps (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))) := by
  unfold Masks
  rw [hg.mask]
  clear hg
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply (Value.mask p _))) =
      Value.mask p _
    rw [cast_mask, ih]

/-- The same for the bracket of an integer below two casts and of a rational
below one. -/
theorem Masks.bracket_integer {g : Option Bool} {ps : List (Option Bool)}
    (hg : Conjunction g ps) (z : Option ℤ) :
    Masks (Functions.castQR.apply (Functions.castZQ.apply (Value.mask g z)))
      ps (Functions.castQR.apply (Functions.castZQ.apply z)) := by
  unfold Masks
  rw [hg.mask]
  clear hg
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show Functions.castQR.apply (Functions.castZQ.apply (Value.mask p _)) = Value.mask p _
    rw [cast_mask_integer, ih]

theorem Masks.bracket_rational {g : Option Bool} {ps : List (Option Bool)}
    (hg : Conjunction g ps) (q : Option ℚ) :
    Masks (Functions.castQR.apply (Value.mask g q)) ps (Functions.castQR.apply q) := by
  unfold Masks
  rw [hg.mask]
  clear hg
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show Functions.castQR.apply (Value.mask p _) = Value.mask p _
    rw [cast_mask_rational, ih]

/-- A mask under the guard of its domain: a comparison takes its negation
along, around the mask of the rest under the rest of the domain. -/
theorem Masks.under (s : Bool) (a b : Option ℝ) {g d : Option Bool} {v r : Option ℝ}
    {ps : List (Option Bool)} (h : Masks (Binding.guardValue d (Value.mask g v)) ps r) :
    Masks (Binding.guardValue (Value.or (compare (!s) b a) d)
      (Value.mask (Value.and (compare s a b) g) v)) (compare s a b :: ps) r := by
  unfold Masks at *
  rw [mask_domain_split, h]
  rfl

/-- The last comparison of such a mask: around the value under its domain. -/
theorem Masks.under_last (s : Bool) (a b : Option ℝ) (q : Option Bool) (v : Option ℝ) :
    Masks (Binding.guardValue (Value.or (compare (!s) b a) q) (Value.mask (compare s a b) v))
      [compare s a b] (Binding.guardValue q v) :=
  (MaskDomain.last s a b).mask v

/-- An observation is missing where its weight is missing at a point. -/
theorem partialIntegral_missing {f : ℝ → Option ℝ} {x : ℝ} (h : f x = none) :
    partialIntegral volume f = none := by
  apply if_neg
  intro hd
  obtain ⟨v, hv⟩ := hd.1 x
  rw [h] at hv
  cases hv

private theorem zero_observation (f : ℝ → Option ℝ) (h : ∀ x, f x = some 0) :
    partialIntegral volume f = some 0 := by
  rw [funext h, partialIntegral_valid volume _ (fun _ => ⟨0, rfl⟩) (by simp)]
  simp

/-- A weight by a case distinction that does not mention the axis. Under a
test it is one of two weights, by a second test and its negation. Where the
first test fails it is a zero at every point, and where a test is missing it
is missing at some point. -/
structure Cases (w w₁ w₂ : ℝ → Option ℝ) (n c₁ c₂ : Option Bool) : Prop where
  missing : n = none → ∃ x, w x = none
  empty : n = some false → ∀ x, w x = some 0
  undecided : n = some true → c₁ = none → ∃ x, w x = none
  first : n = some true → c₁ = some true → c₂ = some false ∧ ∀ x, w x = w₁ x
  second : n = some true → c₁ = some false → c₂ = some true ∧ ∀ x, w x = w₂ x

/-- The observation of such a weight is the observations of the two weights
under their tests, whatever those observations are. -/
theorem Cases.integral {w w₁ w₂ : ℝ → Option ℝ} {n c₁ c₂ : Option Bool}
    (h : Cases w w₁ w₂ n c₁ c₂) :
    partialIntegral volume w =
      Value.mask n (Value.add (Value.mask c₁ (partialIntegral volume w₁))
        (Value.mask c₂ (partialIntegral volume w₂))) := by
  rcases n with _ | _ | _
  · obtain ⟨x, hx⟩ := h.missing rfl
    rw [partialIntegral_missing hx]
    rfl
  · rw [zero_observation w (h.empty rfl)]
    rfl
  rcases c₁ with _ | _ | _
  · obtain ⟨x, hx⟩ := h.undecided rfl rfl
    rw [partialIntegral_missing hx]
    rfl
  · obtain ⟨hc, hw⟩ := h.second rfl rfl
    rw [hc, funext hw]
    exact (Value.add_zero_left _).symm
  · obtain ⟨hc, hw⟩ := h.first rfl rfl
    rw [hc, funext hw]
    exact (Value.add_zero_right _).symm

/-- Observations that add stay such under a case distinction: a weight that
is a zero is integrable, and one that is missing somewhere is missing. -/
theorem Cases.piece {w w₁ w₂ : ℝ → Option ℝ} {n c₁ c₂ : Option Bool} {o₁ o₂ : Option ℝ}
    (h : Cases w w₁ w₂ n c₁ c₂) (p₁ : Piece w₁ o₁) (p₂ : Piece w₂ o₂) :
    Piece w (Value.mask n (Value.add (Value.mask c₁ o₁) (Value.mask c₂ o₂))) := by
  rcases n with _ | _ | _
  · exact Or.inr ⟨h.missing rfl, rfl⟩
  · have hw := h.empty rfl
    refine Or.inl ⟨fun x => ⟨0, hw x⟩, ?_, ?_⟩
    · rw [show (fun x => (w x).getD 0) = fun _ => (0 : ℝ) from funext fun x => by rw [hw x]; rfl]
      exact integrable_zero ℝ ℝ volume
    · rw [show (fun x => (w x).getD 0) = fun _ => (0 : ℝ) from funext fun x => by rw [hw x]; rfl]
      simp [Value.mask]
  rcases c₁ with _ | _ | _
  · exact Or.inr ⟨h.undecided rfl rfl, rfl⟩
  · obtain ⟨hc, hw⟩ := h.second rfl rfl
    rw [hc, funext hw]
    show Piece w₂ (Value.add (some 0) o₂)
    rw [Value.add_zero_left]
    exact p₂
  · obtain ⟨hc, hw⟩ := h.first rfl rfl
    rw [hc, funext hw]
    show Piece w₁ (Value.add o₁ (some 0))
    rw [Value.add_zero_right]
    exact p₁

/-- Two bounds on one side at the front of a guard: where the first implies
the second the second leaves, and otherwise the first. A half-line is never
empty, so a missing term makes the weight missing somewhere. -/
theorem same_side_cases (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) {w w₁ w₂ : ℝ → Option ℝ}
    (r : ℝ → Option ℝ)
    (h : ∀ x, w x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound lower s₂ t₂ x) (r x)))
    (h₁ : ∀ x, w₁ x = Value.mask (axisBound lower s₁ t₁ x) (r x))
    (h₂ : ∀ x, w₂ x = Value.mask (axisBound lower s₂ t₂ x) (r x)) :
    Cases w w₁ w₂ (some true) (boundImplies lower s₁ s₂ t₁ t₂)
      (boundImplied lower s₁ s₂ t₁ t₂) := by
  refine ⟨fun hN => (by cases hN), fun hN => (by cases hN), fun _ hc => ?_, fun _ hc => ?_,
    fun _ hc => ?_⟩
  · rcases t₁ with _ | a
    · exact ⟨0, by rw [h, axisBound_missing]; rfl⟩
    rcases t₂ with _ | b
    · obtain ⟨x, hx⟩ := meets_beyond lower s₁ a
      exact ⟨x, by rw [h, axisBound_real, axisBound_missing, decide_eq_true hx]; rfl⟩
    · rw [boundImplies_real] at hc; cases hc
  · rcases t₁ with _ | a
    · rw [boundImplies_missing_left] at hc; cases hc
    rcases t₂ with _ | b
    · rw [boundImplies_missing_right] at hc; cases hc
    rw [boundImplies_real] at hc
    have hi : implies lower s₁ s₂ a b := of_decide_eq_true (Option.some.inj hc)
    refine ⟨by rw [boundImplied_real, decide_eq_true hi]; rfl, fun x => ?_⟩
    rw [h, h₁, axisBound_real, axisBound_real]
    exact mask_implied (meets_of_implies hi) _
  · rcases t₁ with _ | a
    · rw [boundImplies_missing_left] at hc; cases hc
    rcases t₂ with _ | b
    · rw [boundImplies_missing_right] at hc; cases hc
    rw [boundImplies_real] at hc
    have hi : ¬ implies lower s₁ s₂ a b := of_decide_eq_false (Option.some.inj hc)
    refine ⟨by rw [boundImplied_real, decide_eq_false hi]; rfl, fun x => ?_⟩
    rw [h, h₂, axisBound_real, axisBound_real]
    exact mask_implying (meets_of_not_implies hi) _

private theorem meet_missing {lower s₁ s₂ : Bool} {t₁ t₂ : Option ℝ}
    (hN : boundsMeet lower s₁ s₂ t₁ t₂ = none) (z : ℝ → Option ℝ) :
    ∃ x, Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (z x)) =
      none := by
  rcases t₁ with _ | a
  · exact ⟨0, by rw [axisBound_missing]; rfl⟩
  rcases t₂ with _ | b
  · obtain ⟨x, hx⟩ := meets_beyond lower s₁ a
    exact ⟨x, by rw [axisBound_real, axisBound_missing, decide_eq_true hx]; rfl⟩
  · rw [boundsMeet_real] at hN; cases hN

private theorem meet_empty {lower s₁ s₂ : Bool} {t₁ t₂ : Option ℝ}
    (hN : boundsMeet lower s₁ s₂ t₁ t₂ = some false) (z : ℝ → Option ℝ) (x : ℝ) :
    Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (z x)) =
      some 0 := by
  rcases t₁ with _ | a
  · rw [boundsMeet_missing_left] at hN; cases hN
  rcases t₂ with _ | b
  · rw [boundsMeet_missing_right] at hN; cases hN
  rw [boundsMeet_real] at hN
  have hb : ¬ between lower s₁ s₂ a b := of_decide_eq_false (Option.some.inj hN)
  rw [axisBound_real, axisBound_real]
  by_cases h₁ : meets lower s₁ a x
  · have h₂ : ¬ meets (!lower) s₂ b x := fun h₂ => hb (between_of_meets h₁ h₂)
    simp [h₁, h₂, Value.mask]
  · simp [h₁, Value.mask]

private theorem meet_point {lower s₁ s₂ : Bool} {t₁ t₂ : Option ℝ}
    (hN : boundsMeet lower s₁ s₂ t₁ t₂ = some true) :
    ∃ a b x, t₁ = some a ∧ t₂ = some b ∧ meets lower s₁ a x ∧ meets (!lower) s₂ b x := by
  rcases t₁ with _ | a
  · rw [boundsMeet_missing_left] at hN; cases hN
  rcases t₂ with _ | b
  · rw [boundsMeet_missing_right] at hN; cases hN
  rw [boundsMeet_real] at hN
  have hb : between lower s₁ s₂ a b := of_decide_eq_true (Option.some.inj hN)
  exact ⟨a, b, (a + b) / 2, rfl, rfl, (meets_between hb).1, (meets_between hb).2⟩

/-- A third bound on the side of the second of a lower and an upper bound:
where the second implies it it leaves, and otherwise the second. Where no
point is between the first two the weight is a zero whatever the third is. -/
theorem third_second_cases (lower s₁ s₂ s₃ : Bool) (t₁ t₂ t₃ : Option ℝ)
    {w w₁ w₂ : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x) (Value.mask (axisBound (!lower) s₃ t₃ x) (r x))))
    (h₁ : ∀ x, w₁ x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    (h₂ : ∀ x, w₂ x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₃ t₃ x) (r x))) :
    Cases w w₁ w₂ (boundsMeet lower s₁ s₂ t₁ t₂) (boundImplies (!lower) s₂ s₃ t₂ t₃)
      (boundImplied (!lower) s₂ s₃ t₂ t₃) := by
  refine ⟨fun hN => ?_, fun hN x => ?_, fun hN hc => ?_, fun hN hc => ?_, fun hN hc => ?_⟩
  · obtain ⟨x, hx⟩ := meet_missing hN (fun x => Value.mask (axisBound (!lower) s₃ t₃ x) (r x))
    exact ⟨x, by rw [h]; exact hx⟩
  · rw [h]
    exact meet_empty hN (fun x => Value.mask (axisBound (!lower) s₃ t₃ x) (r x)) x
  · obtain ⟨a, b, x, rfl, rfl, hx₁, hx₂⟩ := meet_point hN
    rcases t₃ with _ | c
    · exact ⟨x, by
        rw [h, axisBound_real, axisBound_real, axisBound_missing, decide_eq_true hx₁,
          decide_eq_true hx₂]
        rfl⟩
    · rw [boundImplies_real] at hc; cases hc
  · obtain ⟨a, b, x, rfl, rfl, -, -⟩ := meet_point hN
    rcases t₃ with _ | c
    · rw [boundImplies_missing_right] at hc; cases hc
    rw [boundImplies_real] at hc
    have hi : implies (!lower) s₂ s₃ b c := of_decide_eq_true (Option.some.inj hc)
    refine ⟨by rw [boundImplied_real, decide_eq_true hi]; rfl, fun y => ?_⟩
    rw [h, h₁, axisBound_real (!lower), axisBound_real (!lower)]
    exact congrArg (Value.mask _) (mask_implied (meets_of_implies hi) _)
  · obtain ⟨a, b, x, rfl, rfl, -, -⟩ := meet_point hN
    rcases t₃ with _ | c
    · rw [boundImplies_missing_right] at hc; cases hc
    rw [boundImplies_real] at hc
    have hi : ¬ implies (!lower) s₂ s₃ b c := of_decide_eq_false (Option.some.inj hc)
    refine ⟨by rw [boundImplied_real, decide_eq_false hi]; rfl, fun y => ?_⟩
    rw [h, h₂, axisBound_real (!lower), axisBound_real (!lower)]
    exact congrArg (Value.mask _) (mask_implying (meets_of_not_implies hi) _)

/-- A third bound on the side of the first: where the first implies it it
leaves, and otherwise it takes the place of the first. -/
theorem third_first_cases (lower s₁ s₂ s₃ : Bool) (t₁ t₂ t₃ : Option ℝ)
    {w w₁ w₂ : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x) (Value.mask (axisBound lower s₃ t₃ x) (r x))))
    (h₁ : ∀ x, w₁ x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    (h₂ : ∀ x, w₂ x =
      Value.mask (axisBound lower s₃ t₃ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x))) :
    Cases w w₁ w₂ (boundsMeet lower s₁ s₂ t₁ t₂) (boundImplies lower s₁ s₃ t₁ t₃)
      (boundImplied lower s₁ s₃ t₁ t₃) := by
  refine ⟨fun hN => ?_, fun hN x => ?_, fun hN hc => ?_, fun hN hc => ?_, fun hN hc => ?_⟩
  · obtain ⟨x, hx⟩ := meet_missing hN (fun x => Value.mask (axisBound lower s₃ t₃ x) (r x))
    exact ⟨x, by rw [h]; exact hx⟩
  · rw [h]
    exact meet_empty hN (fun x => Value.mask (axisBound lower s₃ t₃ x) (r x)) x
  · obtain ⟨a, b, x, rfl, rfl, hx₁, hx₂⟩ := meet_point hN
    rcases t₃ with _ | c
    · exact ⟨x, by
        rw [h, axisBound_real, axisBound_real, axisBound_missing, decide_eq_true hx₁,
          decide_eq_true hx₂]
        rfl⟩
    · rw [boundImplies_real] at hc; cases hc
  · obtain ⟨a, b, x, rfl, rfl, -, -⟩ := meet_point hN
    rcases t₃ with _ | c
    · rw [boundImplies_missing_right] at hc; cases hc
    rw [boundImplies_real] at hc
    have hi : implies lower s₁ s₃ a c := of_decide_eq_true (Option.some.inj hc)
    refine ⟨by rw [boundImplied_real, decide_eq_true hi]; rfl, fun y => ?_⟩
    rw [h, h₁, axisBound_real, axisBound_real, axisBound_real]
    exact mask_implied_far (meets_of_implies hi) _
  · obtain ⟨a, b, x, rfl, rfl, -, -⟩ := meet_point hN
    rcases t₃ with _ | c
    · rw [boundImplies_missing_right] at hc; cases hc
    rw [boundImplies_real] at hc
    have hi : ¬ implies lower s₁ s₃ a c := of_decide_eq_false (Option.some.inj hc)
    refine ⟨by rw [boundImplied_real, decide_eq_false hi]; rfl, fun y => ?_⟩
    rw [h, h₂, axisBound_real, axisBound_real, axisBound_real]
    exact mask_implying_far (meets_of_not_implies hi) _

/-- A weight under a condition that does not mention the axis. Under a test
it is another weight where the condition holds and a zero where the condition
fails. Where the test fails it is a zero at every point, and where the test
or the condition is missing it is missing at some point. -/
structure Guarded (w v : ℝ → Option ℝ) (n g : Option Bool) : Prop where
  missing : n = none → ∃ x, w x = none
  empty : n = some false → ∀ x, w x = some 0
  undecided : n = some true → g = none → ∃ x, w x = none
  holds : n = some true → g = some true → ∀ x, w x = v x
  fails : n = some true → g = some false → ∀ x, w x = some 0

/-- The observation of such a weight is that of the other weight under the
condition, under the test. -/
theorem Guarded.integral {w v : ℝ → Option ℝ} {n g : Option Bool} (h : Guarded w v n g) :
    partialIntegral volume w = Value.mask n (Value.mask g (partialIntegral volume v)) := by
  rcases n with _ | _ | _
  · obtain ⟨x, hx⟩ := h.missing rfl
    rw [partialIntegral_missing hx]; rfl
  · rw [zero_observation w (h.empty rfl)]; rfl
  rcases g with _ | _ | _
  · obtain ⟨x, hx⟩ := h.undecided rfl rfl
    rw [partialIntegral_missing hx]; rfl
  · rw [zero_observation w (h.fails rfl rfl)]; rfl
  · rw [funext (h.holds rfl rfl)]; rfl

/-- The same for a summand of a sum of observations. -/
theorem Guarded.piece {w v : ℝ → Option ℝ} {n g : Option Bool} {o : Option ℝ}
    (h : Guarded w v n g) (p : Piece v o) : Piece w (Value.mask n (Value.mask g o)) := by
  have zero : (∀ x, w x = some 0) → Piece w (some 0) := fun hw => by
    refine Or.inl ⟨fun x => ⟨0, hw x⟩, ?_, ?_⟩
    · rw [show (fun x => (w x).getD 0) = fun _ => (0 : ℝ) from funext fun x => by rw [hw x]; rfl]
      exact integrable_zero ℝ ℝ volume
    · rw [show (fun x => (w x).getD 0) = fun _ => (0 : ℝ) from funext fun x => by rw [hw x]; rfl]
      simp
  rcases n with _ | _ | _
  · exact Or.inr ⟨h.missing rfl, rfl⟩
  · exact zero (h.empty rfl)
  rcases g with _ | _ | _
  · exact Or.inr ⟨h.undecided rfl rfl, rfl⟩
  · exact zero (h.fails rfl rfl)
  · rw [funext (h.holds rfl rfl)]; exact p

/-- A condition that does not mention the axis, behind a lower and an upper
bound: it leaves the weight under the test that a point is between the
bounds. Where none is, the weight is a zero whatever the condition is; where
one is, the condition is asked for there. -/
theorem between_guarded (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) (g : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x) (Value.mask g (r x))))
    (hv : ∀ x, v x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x))) :
    Guarded w v (boundsMeet lower s₁ s₂ t₁ t₂) g := by
  refine ⟨fun hN => ?_, fun hN x => ?_, fun hN hg => ?_, fun hN hg x => ?_, fun hN hg x => ?_⟩
  · obtain ⟨x, hx⟩ := meet_missing hN (fun x => Value.mask g (r x))
    exact ⟨x, by rw [h x]; exact hx⟩
  · rw [h x]; exact meet_empty hN (fun x => Value.mask g (r x)) x
  · obtain ⟨a, b, x, rfl, rfl, h₁, h₂⟩ := meet_point hN
    refine ⟨x, ?_⟩
    rw [h x, hg, axisBound_real, axisBound_real, decide_eq_true h₁, decide_eq_true h₂]; rfl
  · rw [h x, hv x, hg]; rfl
  · obtain ⟨a, b, _, rfl, rfl, _, _⟩ := meet_point hN
    rw [h x, hg, axisBound_real, axisBound_real]
    by_cases h₁ : meets lower s₁ a x <;> by_cases h₂ : meets (!lower) s₂ b x <;>
      simp [h₁, h₂, Value.mask]

/-- A condition that does not mention the axis, behind a single bound: a
half-line is never empty, so the test is only that the term of the bound
exists, which `t ≤ t` says. -/
theorem beyond_guarded (lower s : Bool) (t : Option ℝ) (g : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s t x) (Value.mask g (r x)))
    (hv : ∀ x, v x = Value.mask (axisBound lower s t x) (r x)) :
    Guarded w v (Value.le t t) g := by
  rcases t with _ | a
  · refine ⟨fun _ => ⟨0, by rw [h 0, axisBound_missing]; rfl⟩, fun hN => ?_, fun hN => ?_,
      fun hN => ?_, fun hN => ?_⟩ <;> cases hN
  · have hle : Value.le (some a) (some a) = some true := by simp [Value.le]
    refine ⟨fun hN => ?_, fun hN => ?_, fun _ hg => ?_, fun _ hg x => ?_, fun _ hg x => ?_⟩
    · rw [hle] at hN; cases hN
    · rw [hle] at hN; cases hN
    · obtain ⟨x, hx⟩ := meets_beyond lower s a
      exact ⟨x, by rw [h x, hg, axisBound_real, decide_eq_true hx]; rfl⟩
    · rw [h x, hv x, hg]; rfl
    · rw [h x, hg, axisBound_real]
      by_cases h₁ : meets lower s a x <;> simp [h₁, Value.mask]

/-- The negation of a bound is the bound from the other side with the other
strictness. -/
private theorem axisBound_negation (lower s : Bool) (a x : ℝ) :
    axisBound (!lower) (!s) (some a) x = some (!decide (meets lower s a x)) := by
  rw [axisBound_real]
  cases lower <;> cases s <;> simp [meets, holds]
  · exact decide_lt_not_le x a
  · exact decide_le_not_lt x a
  · exact decide_lt_not_le a x
  · exact decide_le_not_lt a x

/-- A weight under the guard of a domain that does not mention the axis.
Under a test it is another weight where the domain holds, and missing at some
point where the domain fails or is missing. Where the test fails it is a zero
at every point, and where the test is missing it is missing at some point. -/
structure Defended (w v : ℝ → Option ℝ) (n d : Option Bool) : Prop where
  missing : n = none → ∃ x, w x = none
  empty : n = some false → ∀ x, w x = some 0
  fails : n = some true → d ≠ some true → ∃ x, w x = none
  holds : n = some true → d = some true → ∀ x, w x = v x

private theorem guard_fails {d : Option Bool} (h : d ≠ some true) (x : Option ℝ) :
    Binding.guardValue d x = none := by
  rcases d with _ | _ | _
  · rfl
  · rfl
  · exact absurd rfl h

/-- The observation of such a weight is that of the other weight under the
guard, under the test. -/
theorem Defended.integral {w v : ℝ → Option ℝ} {n d : Option Bool} (h : Defended w v n d) :
    partialIntegral volume w =
      Value.mask n (Binding.guardValue d (partialIntegral volume v)) := by
  rcases n with _ | _ | _
  · obtain ⟨x, hx⟩ := h.missing rfl
    rw [partialIntegral_missing hx]; rfl
  · rw [zero_observation w (h.empty rfl)]; rfl
  by_cases hd : d = some true
  · rw [funext (h.holds rfl hd), hd]; rfl
  · obtain ⟨x, hx⟩ := h.fails rfl hd
    rw [partialIntegral_missing hx, guard_fails hd]; rfl

/-- The same for a summand of a sum of observations. -/
theorem Defended.piece {w v : ℝ → Option ℝ} {n d : Option Bool} {o : Option ℝ}
    (h : Defended w v n d) (p : Piece v o) :
    Piece w (Value.mask n (Binding.guardValue d o)) := by
  rcases n with _ | _ | _
  · exact Or.inr ⟨h.missing rfl, rfl⟩
  · have hw := h.empty rfl
    refine Or.inl ⟨fun x => ⟨0, hw x⟩, ?_, ?_⟩
    · rw [show (fun x => (w x).getD 0) = fun _ => (0 : ℝ) from funext fun x => by rw [hw x]; rfl]
      exact integrable_zero ℝ ℝ volume
    · rw [show (fun x => (w x).getD 0) = fun _ => (0 : ℝ) from funext fun x => by rw [hw x]; rfl]
      simp [Value.mask]
  by_cases hd : d = some true
  · rw [funext (h.holds rfl hd), hd]; exact p
  · refine Or.inr ⟨h.fails rfl hd, ?_⟩
    rw [guard_fails hd]; rfl

/-- The guard of the domain of a term behind a single bound: the negation of
the bound, or a domain that does not mention the axis. A half-line is never
empty, so the domain is asked for wherever the term of the bound exists. -/
theorem beyond_defended (lower s : Bool) (t : Option ℝ) (d : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Binding.guardValue (Value.or (axisBound (!lower) (!s) t x) d) (v x))
    (hv : ∀ x, v x = Value.mask (axisBound lower s t x) (r x)) :
    Defended w v (Value.le t t) d := by
  rcases t with _ | a
  · refine ⟨fun _ => ⟨0, by rw [h 0, axisBound_missing]; rfl⟩, fun hN => ?_, fun hN => ?_,
      fun hN => ?_⟩ <;> cases hN
  · have hle : Value.le (some a) (some a) = some true := by simp [Value.le]
    refine ⟨fun hN => ?_, fun hN => ?_, fun _ hd => ?_, fun _ hd x => ?_⟩
    · rw [hle] at hN; cases hN
    · rw [hle] at hN; cases hN
    · obtain ⟨x, hx⟩ := meets_beyond lower s a
      refine ⟨x, ?_⟩
      rw [h x, axisBound_negation, decide_eq_true hx]
      exact guard_fails hd _
    · rw [h x, hd, axisBound_negation]
      by_cases h₁ : meets lower s a x <;> simp [h₁, Value.or, Binding.guardValue]

/-- The same behind a lower and an upper bound: the domain is asked for where
a point is between them. -/
theorem between_defended (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) (d : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Binding.guardValue (Value.or (axisBound (!lower) (!s₁) t₁ x)
      (Value.or (axisBound (!(!lower)) (!s₂) t₂ x) d)) (v x))
    (hv : ∀ x, v x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x))) :
    Defended w v (boundsMeet lower s₁ s₂ t₁ t₂) d := by
  rcases t₁ with _ | a
  · refine ⟨fun _ => ⟨0, by rw [h 0, axisBound_missing]; rfl⟩, fun hN => ?_, fun hN => ?_,
      fun hN => ?_⟩ <;> rw [boundsMeet_missing_left] at hN <;> cases hN
  rcases t₂ with _ | b
  · refine ⟨fun _ => ?_, fun hN => ?_, fun hN => ?_, fun hN => ?_⟩
    · obtain ⟨x, hx⟩ := meets_beyond lower s₁ a
      refine ⟨x, ?_⟩
      rw [h x, axisBound_negation, decide_eq_true hx, axisBound_missing]; rfl
    all_goals rw [boundsMeet_missing_right] at hN; cases hN
  refine ⟨fun hN => ?_, fun hN x => ?_, fun hN hd => ?_, fun hN hd x => ?_⟩
  · rw [boundsMeet_real] at hN; cases hN
  · rw [boundsMeet_real] at hN
    have hb : ¬ between lower s₁ s₂ a b := of_decide_eq_false (Option.some.inj hN)
    rw [h x, hv x, axisBound_negation, axisBound_negation, axisBound_real, axisBound_real]
    by_cases h₁ : meets lower s₁ a x
    · have h₂ : ¬ meets (!lower) s₂ b x := fun h₂ => hb (between_of_meets h₁ h₂)
      simp [h₁, h₂, Value.or, Value.mask, Binding.guardValue]
    · simp [h₁, Value.or, Value.mask, Binding.guardValue]
  · obtain ⟨a', b', x, ha, hb, h₁, h₂⟩ := meet_point hN
    cases ha; cases hb
    refine ⟨x, ?_⟩
    rw [h x, axisBound_negation, axisBound_negation, decide_eq_true h₁, decide_eq_true h₂]
    exact guard_fails hd _
  · rw [h x, hd, axisBound_negation, axisBound_negation]
    by_cases h₁ : meets lower s₁ a x <;> by_cases h₂ : meets (!lower) s₂ b x <;>
      simp [h₁, h₂, Value.or, Binding.guardValue]

/-- The same as observations that add: a summand of a sum of observations
with several bounds on one side. -/
theorem same_side_piece (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) {w w₁ w₂ : ℝ → Option ℝ}
    (r : ℝ → Option ℝ)
    (h : ∀ x, w x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound lower s₂ t₂ x) (r x)))
    (h₁ : ∀ x, w₁ x = Value.mask (axisBound lower s₁ t₁ x) (r x))
    (h₂ : ∀ x, w₂ x = Value.mask (axisBound lower s₂ t₂ x) (r x)) {o₁ o₂ : Option ℝ}
    (p₁ : Piece w₁ o₁) (p₂ : Piece w₂ o₂) :
    Piece w (Value.add (Value.mask (boundImplies lower s₁ s₂ t₁ t₂) o₁)
      (Value.mask (boundImplied lower s₁ s₂ t₁ t₂) o₂)) :=
  (same_side_cases lower s₁ s₂ t₁ t₂ r h h₁ h₂).piece p₁ p₂

theorem third_second_piece (lower s₁ s₂ s₃ : Bool) (t₁ t₂ t₃ : Option ℝ)
    {w w₁ w₂ : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x) (Value.mask (axisBound (!lower) s₃ t₃ x) (r x))))
    (h₁ : ∀ x, w₁ x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    (h₂ : ∀ x, w₂ x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₃ t₃ x) (r x)))
    {o₁ o₂ : Option ℝ} (p₁ : Piece w₁ o₁) (p₂ : Piece w₂ o₂) :
    Piece w (Value.mask (boundsMeet lower s₁ s₂ t₁ t₂)
      (Value.add (Value.mask (boundImplies (!lower) s₂ s₃ t₂ t₃) o₁)
        (Value.mask (boundImplied (!lower) s₂ s₃ t₂ t₃) o₂))) :=
  (third_second_cases lower s₁ s₂ s₃ t₁ t₂ t₃ r h h₁ h₂).piece p₁ p₂

theorem third_first_piece (lower s₁ s₂ s₃ : Bool) (t₁ t₂ t₃ : Option ℝ)
    {w w₁ w₂ : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x) (Value.mask (axisBound lower s₃ t₃ x) (r x))))
    (h₁ : ∀ x, w₁ x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    (h₂ : ∀ x, w₂ x =
      Value.mask (axisBound lower s₃ t₃ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    {o₁ o₂ : Option ℝ} (p₁ : Piece w₁ o₁) (p₂ : Piece w₂ o₂) :
    Piece w (Value.mask (boundsMeet lower s₁ s₂ t₁ t₂)
      (Value.add (Value.mask (boundImplies lower s₁ s₃ t₁ t₃) o₁)
        (Value.mask (boundImplied lower s₁ s₃ t₁ t₃) o₂))) :=
  (third_first_cases lower s₁ s₂ s₃ t₁ t₂ t₃ r h h₁ h₂).piece p₁ p₂

/-! A comparison of the axis that is not solved for it. One side is of
degree one in the axis, a rational multiple of the axis plus terms that do
not mention it, and the other side does not mention it: the comparison is a
bound of the axis by the difference of the other side and those terms,
divided by the slope, from the other side where the slope is negative. Both
are missing exactly where a term is, so this is an equation at every point
for every definedness pattern. -/

/-- The same for the guard of the domain of a term behind its bounds. -/
theorem between_domain_piece (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) (d : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Binding.guardValue (Value.or (axisBound (!lower) (!s₁) t₁ x)
      (Value.or (axisBound (!(!lower)) (!s₂) t₂ x) d)) (v x))
    (hv : ∀ x, v x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    {o : Option ℝ} (p : Piece v o) :
    Piece w (Value.mask (boundsMeet lower s₁ s₂ t₁ t₂) (Binding.guardValue d o)) :=
  (between_defended lower s₁ s₂ t₁ t₂ d r h hv).piece p

theorem beyond_domain_piece (lower s : Bool) (t : Option ℝ) (d : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Binding.guardValue (Value.or (axisBound (!lower) (!s) t x) d) (v x))
    (hv : ∀ x, v x = Value.mask (axisBound lower s t x) (r x))
    {o : Option ℝ} (p : Piece v o) :
    Piece w (Value.mask (Value.le t t) (Binding.guardValue d o)) :=
  (beyond_defended lower s t d r h hv).piece p

/-- The same for a condition that does not mention the axis, behind its
bounds. -/
theorem between_guard_piece (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) (g : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x) (Value.mask g (r x))))
    (hv : ∀ x, v x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    {o : Option ℝ} (p : Piece v o) :
    Piece w (Value.mask (boundsMeet lower s₁ s₂ t₁ t₂) (Value.mask g o)) :=
  (between_guarded lower s₁ s₂ t₁ t₂ g r h hv).piece p

theorem beyond_guard_piece (lower s : Bool) (t : Option ℝ) (g : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s t x) (Value.mask g (r x)))
    (hv : ∀ x, v x = Value.mask (axisBound lower s t x) (r x))
    {o : Option ℝ} (p : Piece v o) :
    Piece w (Value.mask (Value.le t t) (Value.mask g o)) :=
  (beyond_guarded lower s t g r h hv).piece p

/-- A function of degree one in the axis: a rational multiple of the axis
plus a partial value that does not mention it. -/
structure Linear (f : ℝ → Option ℝ) (p : ℚ) (s : Option ℝ) : Prop where
  equation : ∀ x, f x = Value.add (some ((p : ℝ) * x)) s

theorem Linear.axis {z : Option ℝ} (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    Linear (fun x => some x) 1 z :=
  ⟨fun x => by subst hz; simp [Value.add, Numeric.denote]⟩

/-- A rational multiple, with the literal on either side. -/
theorem Linear.scale {f : ℝ → Option ℝ} {p : ℚ} {s c : Option ℝ} (q : ℚ)
    (hc : c = some (Numeric.denote (s := .real) q)) (h : Linear f p s) :
    Linear (fun x => Value.mul c (f x)) (q * p) (Value.mul c s) :=
  ⟨fun x => by
    subst hc
    rw [h.equation]
    rcases s with _ | c
    · rfl
    · simp only [Value.add, Value.mul, Numeric.denote, Option.some.injEq]
      push_cast
      ring⟩

theorem Linear.scaled {f : ℝ → Option ℝ} {p : ℚ} {s c : Option ℝ} (q : ℚ)
    (hc : c = some (Numeric.denote (s := .real) q)) (h : Linear f p s) :
    Linear (fun x => Value.mul (f x) c) (p * q) (Value.mul s c) :=
  ⟨fun x => by
    subst hc
    rw [h.equation]
    rcases s with _ | c
    · rfl
    · simp only [Value.add, Value.mul, Numeric.denote, Option.some.injEq]
      push_cast
      ring⟩

/-- A summand that does not mention the axis, on either side. -/
theorem Linear.add_left {f : ℝ → Option ℝ} {p : ℚ} {s : Option ℝ} (h : Linear f p s)
    (t : Option ℝ) : Linear (fun x => Value.add (f x) t) p (Value.add s t) :=
  ⟨fun x => by
    rw [h.equation]
    rcases s with _ | c <;> rcases t with _ | d <;> simp only [Value.add, Option.some.injEq]
    ring⟩

theorem Linear.add_right {f : ℝ → Option ℝ} {p : ℚ} {s : Option ℝ} (t : Option ℝ)
    (h : Linear f p s) : Linear (fun x => Value.add t (f x)) p (Value.add t s) :=
  ⟨fun x => by
    rw [h.equation]
    rcases s with _ | c <;> rcases t with _ | d <;> simp only [Value.add, Option.some.injEq]
    ring⟩

/-- Two summands of degree one. -/
theorem Linear.add {f g : ℝ → Option ℝ} {p q : ℚ} {s t : Option ℝ} (hf : Linear f p s)
    (hg : Linear g q t) : Linear (fun x => Value.add (f x) (g x)) (p + q) (Value.add s t) :=
  ⟨fun x => by
    rw [hf.equation, hg.equation]
    rcases s with _ | c <;> rcases t with _ | d <;> simp only [Value.add, Option.some.injEq]
    push_cast
    ring⟩

/-- A term of degree one in the axis whose slope is not zero vanishes at one
point only: at every other point it is not zero. -/
theorem Linear.nonzero_away {f : ℝ → Option ℝ} {p : ℚ} {s : Option ℝ} (h : Linear f p s)
    (hp : p ≠ 0) {c : ℝ} (hs : s = some c) {x : ℝ} (hx : x ≠ -c / p) :
    Value.nonzero (f x) = some true := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have h0 : (p : ℝ) * x + c ≠ 0 := by
    intro h0
    apply hx
    field_simp
    linarith
  rw [h.equation, hs]
  simp [Value.add, Value.nonzero, h0]

private theorem slope_inverse {p κ : ℚ} (h : p * κ = 1) : ((κ : ℚ) : ℝ) = ((p : ℚ) : ℝ)⁻¹ := by
  have h' : (p : ℝ) * (κ : ℝ) = 1 := by exact_mod_cast h
  exact eq_inv_of_mul_eq_one_right h'

private theorem slope_positive {p κ : ℚ} (h : p * κ = 1) (hκ : 0 < κ) : (0 : ℝ) < (p : ℝ) := by
  have hp : 0 < p := by
    rcases lt_trichotomy p 0 with hn | hz | hp
    · have : p * κ < 0 := mul_neg_of_neg_of_pos hn hκ
      rw [h] at this
      exact absurd this (by norm_num)
    · rw [hz, zero_mul] at h
      exact absurd h (by norm_num)
    · exact hp
  exact_mod_cast hp

private theorem slope_negative {p κ : ℚ} (h : p * κ = 1) (hκ : κ < 0) : (p : ℝ) < 0 := by
  have hp : p < 0 := by
    rcases lt_trichotomy p 0 with hn | hz | hp
    · exact hn
    · rw [hz, zero_mul] at h
      exact absurd h (by norm_num)
    · have : p * κ < 0 := mul_neg_of_pos_of_neg hp hκ
      rw [h] at this
      exact absurd this (by norm_num)
  exact_mod_cast hp

private theorem solved_value (r c : ℝ) (κ : ℚ) :
    Value.mul (Value.add (some r) (Value.mul (some (Numeric.denote (s := .real) (-1 : ℚ))) (some c)))
        (some (Numeric.denote (s := .real) κ)) = some ((r - c) * (κ : ℝ)) := by
  simp only [Value.add, Value.mul, Numeric.denote, Option.some.injEq]
  push_cast
  ring

private theorem solved_missing {r s : Option ℝ} (m k : Option ℝ) (h : r = none ∨ s = none) :
    Value.mul (Value.add r (Value.mul m s)) k = none := by
  rcases h with rfl | rfl
  · rfl
  · rcases r with _ | r <;> rcases m with _ | m <;> rfl

/-- The side of degree one on the left of a comparison, with a positive
slope: an upper bound of the axis. -/
theorem solve_left (σ : Bool) {f : ℝ → Option ℝ} {p : ℚ} {s m k : Option ℝ} (r : Option ℝ) (κ : ℚ)
    (hf : Linear f p s) (hκ : decide (p * κ = 1 ∧ 0 < κ) = true)
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) κ)) (x : ℝ) :
    compare σ (f x) r = compare σ (some x) (Value.mul (Value.add r (Value.mul m s)) k) := by
  obtain ⟨hpk, hpos⟩ := of_decide_eq_true hκ
  subst hm hk
  rw [hf.equation]
  rcases s with _ | c
  · rw [solved_missing _ _ (Or.inr rfl), compare_missing_right]
    exact compare_missing_left σ r
  rcases r with _ | r
  · rw [solved_missing _ _ (Or.inl rfl), compare_missing_right, compare_missing_right]
  rw [solved_value, slope_inverse hpk]
  have hp := slope_positive hpk hpos
  show compare σ (some ((p : ℝ) * x + c)) (some r) = _
  rw [compare_real, compare_real]
  congr 1
  apply decide_eq_decide.2
  cases σ <;> simp only [holds, Bool.false_eq_true, if_false, if_true]
  · rw [← div_eq_mul_inv, le_div_iff₀ hp]
    constructor <;> intro h <;> linarith
  · rw [← div_eq_mul_inv, lt_div_iff₀ hp]
    constructor <;> intro h <;> linarith

/-- With a negative slope: a lower bound. -/
theorem solve_left_neg (σ : Bool) {f : ℝ → Option ℝ} {p : ℚ} {s m k : Option ℝ} (r : Option ℝ)
    (κ : ℚ) (hf : Linear f p s) (hκ : decide (p * κ = 1 ∧ κ < 0) = true)
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) κ)) (x : ℝ) :
    compare σ (f x) r = compare σ (Value.mul (Value.add r (Value.mul m s)) k) (some x) := by
  obtain ⟨hpk, hneg⟩ := of_decide_eq_true hκ
  subst hm hk
  rw [hf.equation]
  rcases s with _ | c
  · rw [solved_missing _ _ (Or.inr rfl), compare_missing_left]
    exact compare_missing_left σ r
  rcases r with _ | r
  · rw [solved_missing _ _ (Or.inl rfl), compare_missing_left, compare_missing_right]
  rw [solved_value, slope_inverse hpk]
  have hp := slope_negative hpk hneg
  show compare σ (some ((p : ℝ) * x + c)) (some r) = _
  rw [compare_real, compare_real]
  congr 1
  apply decide_eq_decide.2
  cases σ <;> simp only [holds, Bool.false_eq_true, if_false, if_true]
  · rw [← div_eq_mul_inv, div_le_iff_of_neg hp]
    constructor <;> intro h <;> linarith
  · rw [← div_eq_mul_inv, div_lt_iff_of_neg hp]
    constructor <;> intro h <;> linarith

/-- The side of degree one on the right, with a positive slope: a lower
bound of the axis. -/
theorem solve_right (σ : Bool) {f : ℝ → Option ℝ} {p : ℚ} {s m k : Option ℝ} (l : Option ℝ) (κ : ℚ)
    (hf : Linear f p s) (hκ : decide (p * κ = 1 ∧ 0 < κ) = true)
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) κ)) (x : ℝ) :
    compare σ l (f x) = compare σ (Value.mul (Value.add l (Value.mul m s)) k) (some x) := by
  obtain ⟨hpk, hpos⟩ := of_decide_eq_true hκ
  subst hm hk
  rw [hf.equation]
  rcases s with _ | c
  · rw [solved_missing _ _ (Or.inr rfl), compare_missing_left]
    exact compare_missing_right σ l
  rcases l with _ | l
  · rw [solved_missing _ _ (Or.inl rfl), compare_missing_left, compare_missing_left]
  rw [solved_value, slope_inverse hpk]
  have hp := slope_positive hpk hpos
  show compare σ (some l) (some ((p : ℝ) * x + c)) = _
  rw [compare_real, compare_real]
  congr 1
  apply decide_eq_decide.2
  cases σ <;> simp only [holds, Bool.false_eq_true, if_false, if_true]
  · rw [← div_eq_mul_inv, div_le_iff₀ hp]
    constructor <;> intro h <;> linarith
  · rw [← div_eq_mul_inv, div_lt_iff₀ hp]
    constructor <;> intro h <;> linarith

/-- With a negative slope: an upper bound. -/
theorem solve_right_neg (σ : Bool) {f : ℝ → Option ℝ} {p : ℚ} {s m k : Option ℝ} (l : Option ℝ)
    (κ : ℚ) (hf : Linear f p s) (hκ : decide (p * κ = 1 ∧ κ < 0) = true)
    (hm : m = some (Numeric.denote (s := .real) (-1 : ℚ)))
    (hk : k = some (Numeric.denote (s := .real) κ)) (x : ℝ) :
    compare σ l (f x) = compare σ (some x) (Value.mul (Value.add l (Value.mul m s)) k) := by
  obtain ⟨hpk, hneg⟩ := of_decide_eq_true hκ
  subst hm hk
  rw [hf.equation]
  rcases s with _ | c
  · rw [solved_missing _ _ (Or.inr rfl), compare_missing_right]
    exact compare_missing_right σ l
  rcases l with _ | l
  · rw [solved_missing _ _ (Or.inl rfl), compare_missing_right, compare_missing_left]
  rw [solved_value, slope_inverse hpk]
  have hp := slope_negative hpk hneg
  show compare σ (some l) (some ((p : ℝ) * x + c)) = _
  rw [compare_real, compare_real]
  congr 1
  apply decide_eq_decide.2
  cases σ <;> simp only [holds, Bool.false_eq_true, if_false, if_true]
  · rw [← div_eq_mul_inv, le_div_iff_of_neg hp]
    constructor <;> intro h <;> linarith
  · rw [← div_eq_mul_inv, lt_div_iff_of_neg hp]
    constructor <;> intro h <;> linarith

/-- At that one point it is zero. -/
theorem Linear.zero_at {f : ℝ → Option ℝ} {p : ℚ} {s : Option ℝ} (h : Linear f p s)
    (hp : p ≠ 0) {c : ℝ} (hs : s = some c) : Value.nonzero (f (-c / p)) = some false := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have h0 : (p : ℝ) * (-c / p) + c = 0 := by field_simp; ring
  rw [h.equation, hs]
  simp [Value.add, Value.nonzero, h0]

/-- Where what the term has beside the axis is missing, the term is missing
at every point. -/
theorem Linear.missing {f : ℝ → Option ℝ} {p : ℚ} (h : Linear f p none) (x : ℝ) :
    Value.nonzero (f x) = none := by
  rw [h.equation]; rfl

/-- A weight that excludes a point of the axis, behind bounds. Under a test,
and where the point exists, it is another weight at every point but that one,
and there the two exist together. Where the test fails it is a zero at every
point, and where the test or the point is missing it is missing at some
point. The point exists where what its term has beside the axis does. -/
structure Excluded (w v : ℝ → Option ℝ) (n : Option Bool) (s : Option ℝ) : Prop where
  missing : n = none → ∃ x, w x = none
  empty : n = some false → ∀ x, w x = some 0
  undecided : n = some true → s = none → ∃ x, w x = none
  holds : n = some true → ∀ c, s = some c →
    ∃ a : ℝ, (∀ x, x ≠ a → w x = v x) ∧ (Value.Defined (w a) ↔ Value.Defined (v a))

/-- Two weights that agree at every point but one, and exist together at that
one, have the same observation. -/
theorem observation_away {w v : ℝ → Option ℝ} {a : ℝ} (away : ∀ x, x ≠ a → w x = v x)
    (point : Value.Defined (w a) ↔ Value.Defined (v a)) :
    partialIntegral volume w = partialIntegral volume v := by
  have missing : ∀ {u : ℝ → Option ℝ} {x : ℝ}, ¬ Value.Defined (u x) → u x = none := by
    intro u x hx
    cases hu : u x with
    | none => rfl
    | some y => exact absurd ⟨y, hu⟩ hx
  by_cases hd : ∀ x, Value.Defined (w x)
  · have hv : ∀ x, Value.Defined (v x) := fun x => by
      by_cases hx : x = a
      · subst hx; exact point.mp (hd x)
      · rw [← away x hx]; exact hd x
    exact partialIntegral_congr_away w v [a] hd hv (fun x hx => away x (hx a (by simp)))
  · obtain ⟨x, hx⟩ := not_forall.mp hd
    have hy : ∃ y, v y = none := by
      by_cases hxa : x = a
      · subst hxa; exact ⟨x, missing (fun h => hx (point.mpr h))⟩
      · exact ⟨x, by rw [← away x hxa]; exact missing hx⟩
    obtain ⟨y, hy⟩ := hy
    rw [partialIntegral_missing (missing hx), partialIntegral_missing hy]

/-- The observation of such a weight is that of the other weight, under the
test and where the point exists, which `s ≤ s` says of the rest of its
term. -/
theorem Excluded.integral {w v : ℝ → Option ℝ} {n : Option Bool} {s : Option ℝ}
    (h : Excluded w v n s) :
    partialIntegral volume w =
      Value.mask n (Value.mask (Value.le s s) (partialIntegral volume v)) := by
  rcases n with _ | _ | _
  · obtain ⟨x, hx⟩ := h.missing rfl
    rw [partialIntegral_missing hx]; rfl
  · rw [zero_observation w (h.empty rfl)]; rfl
  rcases s with _ | c
  · obtain ⟨x, hx⟩ := h.undecided rfl rfl
    rw [partialIntegral_missing hx]; rfl
  · obtain ⟨a, away, point⟩ := h.holds rfl c rfl
    have hle : Value.le (some c) (some c) = some true := by simp [Value.le]
    rw [hle, observation_away away point]; rfl

/-- An excluded point behind a lower and an upper bound: it leaves the weight
under the test that a point is between the bounds. What is behind the
exclusion exists at every point: at the excluded one it is asked for only
without the exclusion. -/
theorem between_excluded (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) {f : ℝ → Option ℝ} {p : ℚ}
    {s : Option ℝ} (hf : Linear f p s) (hp : decide (p ≠ 0) = true) {w v : ℝ → Option ℝ}
    (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x) (Value.mask (Value.nonzero (f x)) (r x))))
    (hv : ∀ x, v x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    (hr : ∀ x, Value.Defined (r x)) :
    Excluded w v (boundsMeet lower s₁ s₂ t₁ t₂) s := by
  refine ⟨fun hN => ?_, fun hN x => ?_, fun hN hs => ?_, fun hN c hs => ?_⟩
  · obtain ⟨x, hx⟩ := meet_missing hN (fun x => Value.mask (Value.nonzero (f x)) (r x))
    exact ⟨x, by rw [h x]; exact hx⟩
  · rw [h x]; exact meet_empty hN (fun x => Value.mask (Value.nonzero (f x)) (r x)) x
  · obtain ⟨a, b, x, rfl, rfl, h₁, h₂⟩ := meet_point hN
    subst hs
    refine ⟨x, ?_⟩
    rw [h x, axisBound_real, axisBound_real, decide_eq_true h₁, decide_eq_true h₂, hf.missing]; rfl
  · obtain ⟨a, b, _, rfl, rfl, _, _⟩ := meet_point hN
    have hp' := of_decide_eq_true hp
    refine ⟨-c / p, fun x hx => ?_, ?_⟩
    · rw [h x, hv x, hf.nonzero_away hp' hs hx]; rfl
    · obtain ⟨y, hy⟩ := hr (-c / p)
      rw [h, hv, axisBound_real, axisBound_real, hf.zero_at hp' hs, hy]
      by_cases h₁ : meets lower s₁ a (-c / p) <;> by_cases h₂ : meets (!lower) s₂ b (-c / p) <;>
        simp [h₁, h₂, Value.mask, Value.Defined]

/-- An excluded point behind a single bound: a half-line is never empty, so
the test is only that the term of the bound exists. -/
theorem beyond_excluded (lower σ : Bool) (t : Option ℝ) {f : ℝ → Option ℝ} {p : ℚ}
    {s : Option ℝ} (hf : Linear f p s) (hp : decide (p ≠ 0) = true) {w v : ℝ → Option ℝ}
    (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower σ t x) (Value.mask (Value.nonzero (f x)) (r x)))
    (hv : ∀ x, v x = Value.mask (axisBound lower σ t x) (r x))
    (hr : ∀ x, Value.Defined (r x)) :
    Excluded w v (Value.le t t) s := by
  rcases t with _ | a
  · refine ⟨fun _ => ⟨0, by rw [h 0, axisBound_missing]; rfl⟩, fun hN => ?_, fun hN => ?_,
      fun hN => ?_⟩ <;> cases hN
  · have hle : Value.le (some a) (some a) = some true := by simp [Value.le]
    have hp' := of_decide_eq_true hp
    refine ⟨fun hN => ?_, fun hN => ?_, fun _ hs => ?_, fun _ c hs => ?_⟩
    · rw [hle] at hN; cases hN
    · rw [hle] at hN; cases hN
    · obtain ⟨x, hx⟩ := meets_beyond lower σ a
      subst hs
      exact ⟨x, by rw [h x, axisBound_real, decide_eq_true hx, hf.missing]; rfl⟩
    · refine ⟨-c / p, fun x hx => ?_, ?_⟩
      · rw [h x, hv x, hf.nonzero_away hp' hs hx]; rfl
      · obtain ⟨y, hy⟩ := hr (-c / p)
        rw [h, hv, axisBound_real, hf.zero_at hp' hs, hy]
        by_cases h₁ : meets lower σ a (-c / p) <;> simp [h₁, Value.mask, Value.Defined]

/-- An excluded point at the front of a weight: there is no test. -/
theorem front_excluded {f : ℝ → Option ℝ} {p : ℚ} {s : Option ℝ} (hf : Linear f p s)
    (hp : decide (p ≠ 0) = true) {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (Value.nonzero (f x)) (r x)) (hv : ∀ x, v x = r x)
    (hr : ∀ x, Value.Defined (r x)) :
    Excluded w v (some true) s := by
  have hp' := of_decide_eq_true hp
  refine ⟨fun hN => ?_, fun hN => ?_, fun _ hs => ?_, fun _ c hs => ?_⟩
  · cases hN
  · cases hN
  · subst hs
    exact ⟨0, by rw [h 0, hf.missing]; rfl⟩
  · refine ⟨-c / p, fun x hx => ?_, ?_⟩
    · rw [h x, hv x, hf.nonzero_away hp' hs hx]; rfl
    · rw [h, hv, hf.zero_at hp' hs]
      exact ⟨fun _ => hr _, fun _ => ⟨0, rfl⟩⟩

/-- A weight on a point only, behind a lower and an upper bound: the negation
of an exclusion. Under the same test, and where the point exists, it is a zero
at every point but that one. -/
theorem between_only (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) {f : ℝ → Option ℝ} {p : ℚ}
    {s : Option ℝ} (hf : Linear f p s) (hp : decide (p ≠ 0) = true) {w : ℝ → Option ℝ}
    (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x)
        (Value.mask (Value.not (Value.nonzero (f x))) (r x))))
    (hr : ∀ x, Value.Defined (r x)) :
    Excluded w (fun _ => some 0) (boundsMeet lower s₁ s₂ t₁ t₂) s := by
  refine ⟨fun hN => ?_, fun hN x => ?_, fun hN hs => ?_, fun hN c hs => ?_⟩
  · obtain ⟨x, hx⟩ :=
      meet_missing hN (fun x => Value.mask (Value.not (Value.nonzero (f x))) (r x))
    exact ⟨x, by rw [h x]; exact hx⟩
  · rw [h x]
    exact meet_empty hN (fun x => Value.mask (Value.not (Value.nonzero (f x))) (r x)) x
  · obtain ⟨a, b, x, rfl, rfl, h₁, h₂⟩ := meet_point hN
    subst hs
    refine ⟨x, ?_⟩
    rw [h x, axisBound_real, axisBound_real, decide_eq_true h₁, decide_eq_true h₂, hf.missing]; rfl
  · obtain ⟨a, b, _, rfl, rfl, _, _⟩ := meet_point hN
    have hp' := of_decide_eq_true hp
    refine ⟨-c / p, fun x hx => ?_, ?_⟩
    · rw [h x, axisBound_real, axisBound_real, hf.nonzero_away hp' hs hx]
      by_cases h₁ : meets lower s₁ a x <;> by_cases h₂ : meets (!lower) s₂ b x <;>
        simp [h₁, h₂, Value.mask, Value.not]
    · obtain ⟨y, hy⟩ := hr (-c / p)
      rw [h, axisBound_real, axisBound_real, hf.zero_at hp' hs, hy]
      by_cases h₁ : meets lower s₁ a (-c / p) <;> by_cases h₂ : meets (!lower) s₂ b (-c / p) <;>
        simp [h₁, h₂, Value.mask, Value.not, Value.Defined]

/-- The same behind a single bound. -/
theorem beyond_only (lower σ : Bool) (t : Option ℝ) {f : ℝ → Option ℝ} {p : ℚ}
    {s : Option ℝ} (hf : Linear f p s) (hp : decide (p ≠ 0) = true) {w : ℝ → Option ℝ}
    (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower σ t x)
      (Value.mask (Value.not (Value.nonzero (f x))) (r x)))
    (hr : ∀ x, Value.Defined (r x)) :
    Excluded w (fun _ => some 0) (Value.le t t) s := by
  rcases t with _ | a
  · refine ⟨fun _ => ⟨0, by rw [h 0, axisBound_missing]; rfl⟩, fun hN => ?_, fun hN => ?_,
      fun hN => ?_⟩ <;> cases hN
  · have hle : Value.le (some a) (some a) = some true := by simp [Value.le]
    have hp' := of_decide_eq_true hp
    refine ⟨fun hN => ?_, fun hN => ?_, fun _ hs => ?_, fun _ c hs => ?_⟩
    · rw [hle] at hN; cases hN
    · rw [hle] at hN; cases hN
    · obtain ⟨x, hx⟩ := meets_beyond lower σ a
      subst hs
      exact ⟨x, by rw [h x, axisBound_real, decide_eq_true hx, hf.missing]; rfl⟩
    · refine ⟨-c / p, fun x hx => ?_, ?_⟩
      · rw [h x, axisBound_real, hf.nonzero_away hp' hs hx]
        by_cases h₁ : meets lower σ a x <;> simp [h₁, Value.mask, Value.not]
      · obtain ⟨y, hy⟩ := hr (-c / p)
        rw [h, axisBound_real, hf.zero_at hp' hs, hy]
        by_cases h₁ : meets lower σ a (-c / p) <;> simp [h₁, Value.mask, Value.not, Value.Defined]

/-- The same at the front of a weight. -/
theorem front_only {f : ℝ → Option ℝ} {p : ℚ} {s : Option ℝ} (hf : Linear f p s)
    (hp : decide (p ≠ 0) = true) {w : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (Value.not (Value.nonzero (f x))) (r x))
    (hr : ∀ x, Value.Defined (r x)) :
    Excluded w (fun _ => some 0) (some true) s := by
  have hp' := of_decide_eq_true hp
  refine ⟨fun hN => ?_, fun hN => ?_, fun _ hs => ?_, fun _ c hs => ?_⟩
  · cases hN
  · cases hN
  · subst hs
    exact ⟨0, by rw [h 0, hf.missing]; rfl⟩
  · refine ⟨-c / p, fun x hx => ?_, ?_⟩
    · rw [h x, hf.nonzero_away hp' hs hx]; rfl
    · rw [h, hf.zero_at hp' hs]
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ => hr _⟩

/-- The observation of a weight on a point only: a zero under the tests. -/
theorem Excluded.zero {w : ℝ → Option ℝ} {n : Option Bool} {s z : Option ℝ}
    (h : Excluded w (fun _ => some 0) n s)
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) :
    partialIntegral volume w = Value.mask n (Value.mask (Value.le s s) z) := by
  rw [h.integral, zero_observation (fun _ => some 0) (fun _ => rfl), hz]
  simp [Numeric.denote]

end QSym.Distribution.StepSource

namespace QSym.Distribution.DensityProgram
open MeasureTheory

/-- The mass of a single weight of the line is its observation. -/
theorem mass_weight (w : ℝ → Option ℝ) :
    massValue (DensityProgram.weight w .lebesgue).presentation = partialIntegral volume w := by
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  have hw : (DensityProgram.weight w .lebesgue).density = w := by
    funext x; simp only [density, Value.mul_one_left]
  rw [hw]
  rfl

theorem mass_same_side (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) {w w₁ w₂ : ℝ → Option ℝ}
    (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound lower s₂ t₂ x) (r x)))
    (h₁ : ∀ x, w₁ x = Value.mask (StepSource.axisBound lower s₁ t₁ x) (r x))
    (h₂ : ∀ x, w₂ x = Value.mask (StepSource.axisBound lower s₂ t₂ x) (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.add
        (Value.mask (StepSource.boundImplies lower s₁ s₂ t₁ t₂)
          (massValue (DensityProgram.weight w₁ .lebesgue).presentation))
        (Value.mask (StepSource.boundImplied lower s₁ s₂ t₁ t₂)
          (massValue (DensityProgram.weight w₂ .lebesgue).presentation)) := by
  rw [mass_weight, mass_weight, mass_weight]
  exact (StepSource.same_side_cases lower s₁ s₂ t₁ t₂ r h h₁ h₂).integral

theorem mass_third_second (lower s₁ s₂ s₃ : Bool) (t₁ t₂ t₃ : Option ℝ)
    {w w₁ w₂ : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x)
        (Value.mask (StepSource.axisBound (!lower) s₃ t₃ x) (r x))))
    (h₁ : ∀ x, w₁ x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x) (r x)))
    (h₂ : ∀ x, w₂ x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₃ t₃ x) (r x))) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (StepSource.boundsMeet lower s₁ s₂ t₁ t₂)
        (Value.add
          (Value.mask (StepSource.boundImplies (!lower) s₂ s₃ t₂ t₃)
            (massValue (DensityProgram.weight w₁ .lebesgue).presentation))
          (Value.mask (StepSource.boundImplied (!lower) s₂ s₃ t₂ t₃)
            (massValue (DensityProgram.weight w₂ .lebesgue).presentation))) := by
  rw [mass_weight, mass_weight, mass_weight]
  exact (StepSource.third_second_cases lower s₁ s₂ s₃ t₁ t₂ t₃ r h h₁ h₂).integral

theorem mass_third_first (lower s₁ s₂ s₃ : Bool) (t₁ t₂ t₃ : Option ℝ)
    {w w₁ w₂ : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x)
        (Value.mask (StepSource.axisBound lower s₃ t₃ x) (r x))))
    (h₁ : ∀ x, w₁ x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x) (r x)))
    (h₂ : ∀ x, w₂ x = Value.mask (StepSource.axisBound lower s₃ t₃ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x) (r x))) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (StepSource.boundsMeet lower s₁ s₂ t₁ t₂)
        (Value.add
          (Value.mask (StepSource.boundImplies lower s₁ s₃ t₁ t₃)
            (massValue (DensityProgram.weight w₁ .lebesgue).presentation))
          (Value.mask (StepSource.boundImplied lower s₁ s₃ t₁ t₃)
            (massValue (DensityProgram.weight w₂ .lebesgue).presentation))) := by
  rw [mass_weight, mass_weight, mass_weight]
  exact (StepSource.third_first_cases lower s₁ s₂ s₃ t₁ t₂ t₃ r h h₁ h₂).integral

/-- A condition that does not mention the axis leaves the observation from
behind a lower and an upper bound, under the test that a point is between
them, and from behind a single bound, under the test that its term exists. -/
theorem mass_between_guard (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) (g : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x) (Value.mask g (r x))))
    (hv : ∀ x, v x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x) (r x))) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (StepSource.boundsMeet lower s₁ s₂ t₁ t₂)
        (Value.mask g (massValue (DensityProgram.weight v .lebesgue).presentation)) := by
  rw [mass_weight, mass_weight]
  exact (StepSource.between_guarded lower s₁ s₂ t₁ t₂ g r h hv).integral

theorem mass_beyond_guard (lower s : Bool) (t : Option ℝ) (g : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (StepSource.axisBound lower s t x) (Value.mask g (r x)))
    (hv : ∀ x, v x = Value.mask (StepSource.axisBound lower s t x) (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (Value.le t t)
        (Value.mask g (massValue (DensityProgram.weight v .lebesgue).presentation)) := by
  rw [mass_weight, mass_weight]
  exact (StepSource.beyond_guarded lower s t g r h hv).integral

/-- The guard of the domain of a term of a bound leaves the observation from
behind the bounds in front of that bound: the negations of those bounds, or
a domain that does not mention the axis. Behind a lower and an upper bound
under the test that a point is between them, and behind a single bound under
the test that its term exists. -/
theorem mass_between_domain (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) (d : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Binding.guardValue (Value.or (StepSource.axisBound (!lower) (!s₁) t₁ x)
      (Value.or (StepSource.axisBound (!(!lower)) (!s₂) t₂ x) d)) (v x))
    (hv : ∀ x, v x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x) (r x))) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (StepSource.boundsMeet lower s₁ s₂ t₁ t₂)
        (Binding.guardValue d (massValue (DensityProgram.weight v .lebesgue).presentation)) := by
  rw [mass_weight, mass_weight]
  exact (StepSource.between_defended lower s₁ s₂ t₁ t₂ d r h hv).integral

theorem mass_beyond_domain (lower s : Bool) (t : Option ℝ) (d : Option Bool)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x =
      Binding.guardValue (Value.or (StepSource.axisBound (!lower) (!s) t x) d) (v x))
    (hv : ∀ x, v x = Value.mask (StepSource.axisBound lower s t x) (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (Value.le t t)
        (Binding.guardValue d (massValue (DensityProgram.weight v .lebesgue).presentation)) := by
  rw [mass_weight, mass_weight]
  exact (StepSource.beyond_defended lower s t d r h hv).integral

/-- A guard of a weight that can fail at the origin only: `x ≠ 0` or a
condition that does not mention the axis. Where the condition holds the guard
holds at every point; where it fails or is missing, so does the guard at the
origin, and the observation is missing. -/
theorem mass_guard_origin (g : Option Bool) {w m : ℝ → Option ℝ}
    (h : ∀ x, w x = Binding.guardValue (Value.or (Value.nonzero (some x)) g) (m x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Binding.guardValue g (massValue (DensityProgram.weight m .lebesgue).presentation) := by
  rw [mass_weight, mass_weight]
  rcases g with _ | _ | _
  · rw [StepSource.partialIntegral_missing (x := 0)
      (by rw [h 0]; simp [Value.nonzero, Value.or, Binding.guardValue])]
    rfl
  · rw [StepSource.partialIntegral_missing (x := 0)
      (by rw [h 0]; simp [Value.nonzero, Value.or, Binding.guardValue])]
    rfl
  · have hw : w = m := funext fun x => by
      rw [h x]
      by_cases hx : x = 0 <;> simp [hx, Value.nonzero, Value.or, Binding.guardValue]
    rw [hw]
    rfl

/-- A point of the axis that a weight excludes: `x ≠ a`, which is the term
`x - a`, of degree one in the axis, being not zero. Where the exclusion holds,
the weight is the weight with the exclusion taken to hold. That is at every
point but one, so the two have the same observation where both exist at
every point and so does what the term has beside the axis. Without that, a
missing value could be asked for at the excluded point only, or the point
itself could be missing. -/
theorem mass_null_point {w v f : ℝ → Option ℝ} {p : ℚ} {s : Option ℝ}
    (hf : StepSource.Linear f p s) (hp : decide (p ≠ 0) = true) (hs : Value.Defined s)
    (tw : ∀ x, Value.Defined (w x)) (tv : ∀ x, Value.Defined (v x))
    (h : ∀ x, Value.nonzero (f x) = some true → w x = v x) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      massValue (DensityProgram.weight v .lebesgue).presentation := by
  rw [mass_weight, mass_weight]
  obtain ⟨c, hc⟩ := hs
  exact partialIntegral_congr_away w v [-c / p] tw tv
    (fun x hx => h x (hf.nonzero_away (of_decide_eq_true hp) hc (hx _ (by simp))))

/-- A point of the axis that a weight excludes, where the point may be
missing: the term of the exclusion is of degree one in the axis, and the
point exists where what the term has beside the axis does, which `s ≤ s`
says. The exclusion leaves the observation as that test, under the test that
the bounds in front of it leave a point: where they leave none the weight is
a zero whatever the point is, and where they leave one the exclusion is
asked for there. What is behind the exclusion exists at every point. Behind
a lower and an upper bound, behind a single bound, and at the front. -/
theorem mass_between_excluded (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) {f : ℝ → Option ℝ}
    {p : ℚ} {s : Option ℝ} (hf : StepSource.Linear f p s) (hp : decide (p ≠ 0) = true)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x)
        (Value.mask (Value.nonzero (f x)) (r x))))
    (hv : ∀ x, v x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x) (r x)))
    (hr : ∀ x, Value.Defined (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (StepSource.boundsMeet lower s₁ s₂ t₁ t₂)
        (Value.mask (Value.le s s) (massValue (DensityProgram.weight v .lebesgue).presentation)) := by
  rw [mass_weight, mass_weight]
  exact (StepSource.between_excluded lower s₁ s₂ t₁ t₂ hf hp r h hv hr).integral

theorem mass_beyond_excluded (lower σ : Bool) (t : Option ℝ) {f : ℝ → Option ℝ}
    {p : ℚ} {s : Option ℝ} (hf : StepSource.Linear f p s) (hp : decide (p ≠ 0) = true)
    {w v : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (StepSource.axisBound lower σ t x)
      (Value.mask (Value.nonzero (f x)) (r x)))
    (hv : ∀ x, v x = Value.mask (StepSource.axisBound lower σ t x) (r x))
    (hr : ∀ x, Value.Defined (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (Value.le t t)
        (Value.mask (Value.le s s) (massValue (DensityProgram.weight v .lebesgue).presentation)) := by
  rw [mass_weight, mass_weight]
  exact (StepSource.beyond_excluded lower σ t hf hp r h hv hr).integral

theorem mass_front_excluded {f : ℝ → Option ℝ} {p : ℚ} {s : Option ℝ}
    (hf : StepSource.Linear f p s) (hp : decide (p ≠ 0) = true) {w v : ℝ → Option ℝ}
    (r : ℝ → Option ℝ) (h : ∀ x, w x = Value.mask (Value.nonzero (f x)) (r x))
    (hv : ∀ x, v x = r x) (hr : ∀ x, Value.Defined (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (Value.le s s) (massValue (DensityProgram.weight v .lebesgue).presentation) := by
  rw [mass_weight, mass_weight]
  exact (StepSource.front_excluded hf hp r h hv hr).integral

/-- A weight on a point of the axis only, where the point may be missing:
`x = a`, the negation of an exclusion. Its observation is a zero under the
same tests: that the bounds in front of it leave a point, and that the point
exists. What is behind it exists at every point. -/
theorem mass_between_only (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) {f : ℝ → Option ℝ}
    {p : ℚ} {s : Option ℝ} (hf : StepSource.Linear f p s) (hp : decide (p ≠ 0) = true)
    {z : Option ℝ} (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    {w : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (StepSource.axisBound lower s₁ t₁ x)
      (Value.mask (StepSource.axisBound (!lower) s₂ t₂ x)
        (Value.mask (Value.not (Value.nonzero (f x))) (r x))))
    (hr : ∀ x, Value.Defined (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (StepSource.boundsMeet lower s₁ s₂ t₁ t₂) (Value.mask (Value.le s s) z) := by
  rw [mass_weight]
  exact (StepSource.between_only lower s₁ s₂ t₁ t₂ hf hp r h hr).zero hz

theorem mass_beyond_only (lower σ : Bool) (t : Option ℝ) {f : ℝ → Option ℝ}
    {p : ℚ} {s : Option ℝ} (hf : StepSource.Linear f p s) (hp : decide (p ≠ 0) = true)
    {z : Option ℝ} (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    {w : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (StepSource.axisBound lower σ t x)
      (Value.mask (Value.not (Value.nonzero (f x))) (r x)))
    (hr : ∀ x, Value.Defined (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (Value.le t t) (Value.mask (Value.le s s) z) := by
  rw [mass_weight]
  exact (StepSource.beyond_only lower σ t hf hp r h hr).zero hz

theorem mass_front_only {f : ℝ → Option ℝ} {p : ℚ} {s : Option ℝ}
    (hf : StepSource.Linear f p s) (hp : decide (p ≠ 0) = true)
    {z : Option ℝ} (hz : z = some (Numeric.denote (s := .real) (0 : ℚ)))
    {w : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (Value.not (Value.nonzero (f x))) (r x))
    (hr : ∀ x, Value.Defined (r x)) :
    massValue (DensityProgram.weight w .lebesgue).presentation =
      Value.mask (Value.le s s) z := by
  rw [mass_weight]
  exact (StepSource.front_only hf hp r h hr).zero hz

end QSym.Distribution.DensityProgram
