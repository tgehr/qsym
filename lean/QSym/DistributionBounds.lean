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

/-- A case distinction that does not mention the axis: the weight is one of
two weights by a test and its negation, and missing somewhere where the test
is missing. -/
theorem integral_cases {w w₁ w₂ : ℝ → Option ℝ} {c₁ c₂ : Option Bool}
    (hn : c₁ = none → ∃ x, w x = none)
    (h₁ : c₁ = some true → c₂ = some false ∧ ∀ x, w x = w₁ x)
    (h₂ : c₁ = some false → c₂ = some true ∧ ∀ x, w x = w₂ x) :
    partialIntegral volume w =
      Value.add (Value.mask c₁ (partialIntegral volume w₁))
        (Value.mask c₂ (partialIntegral volume w₂)) := by
  rcases c₁ with _ | _ | _
  · obtain ⟨x, hx⟩ := hn rfl
    rw [partialIntegral_missing hx]
    rfl
  · obtain ⟨hc, hw⟩ := h₂ rfl
    rw [hc, funext hw]
    exact (Value.add_zero_left _).symm
  · obtain ⟨hc, hw⟩ := h₁ rfl
    rw [hc, funext hw]
    exact (Value.add_zero_right _).symm

/-- The same under a mask that hides every point where it fails. -/
theorem integral_cases_within {w w₁ w₂ : ℝ → Option ℝ} {n c₁ c₂ : Option Bool}
    (hu : n = none → ∃ x, w x = none)
    (hz : n = some false → ∀ x, w x = some 0)
    (hn : n = some true → c₁ = none → ∃ x, w x = none)
    (h₁ : n = some true → c₁ = some true → c₂ = some false ∧ ∀ x, w x = w₁ x)
    (h₂ : n = some true → c₁ = some false → c₂ = some true ∧ ∀ x, w x = w₂ x) :
    partialIntegral volume w =
      Value.mask n (Value.add (Value.mask c₁ (partialIntegral volume w₁))
        (Value.mask c₂ (partialIntegral volume w₂))) := by
  rcases n with _ | _ | _
  · obtain ⟨x, hx⟩ := hu rfl
    rw [partialIntegral_missing hx]
    rfl
  · rw [zero_observation w (hz rfl)]
    rfl
  · exact integral_cases (hn rfl) (h₁ rfl) (h₂ rfl)

/-- Two bounds on one side at the front of a guard: where the first implies
the second the second leaves, and otherwise the first. A half-line is never
empty, so a missing term makes both sides missing. -/
theorem same_side_integral (lower s₁ s₂ : Bool) (t₁ t₂ : Option ℝ) {w w₁ w₂ : ℝ → Option ℝ}
    (r : ℝ → Option ℝ)
    (h : ∀ x, w x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound lower s₂ t₂ x) (r x)))
    (h₁ : ∀ x, w₁ x = Value.mask (axisBound lower s₁ t₁ x) (r x))
    (h₂ : ∀ x, w₂ x = Value.mask (axisBound lower s₂ t₂ x) (r x)) :
    partialIntegral volume w =
      Value.add (Value.mask (boundImplies lower s₁ s₂ t₁ t₂) (partialIntegral volume w₁))
        (Value.mask (boundImplied lower s₁ s₂ t₁ t₂) (partialIntegral volume w₂)) := by
  rcases t₁ with _ | a
  · refine integral_cases (fun _ => ⟨0, ?_⟩) (fun hc => ?_) (fun hc => ?_)
    · rw [h, axisBound_missing]; rfl
    · rw [boundImplies_missing_left] at hc; cases hc
    · rw [boundImplies_missing_left] at hc; cases hc
  rcases t₂ with _ | b
  · refine integral_cases (fun _ => ?_) (fun hc => ?_) (fun hc => ?_)
    · obtain ⟨x, hx⟩ := meets_beyond lower s₁ a
      exact ⟨x, by rw [h, axisBound_real, axisBound_missing, decide_eq_true hx]; rfl⟩
    · rw [boundImplies_missing_right] at hc; cases hc
    · rw [boundImplies_missing_right] at hc; cases hc
  refine integral_cases (fun hc => ?_) (fun hc => ?_) (fun hc => ?_)
  · rw [boundImplies_real] at hc; cases hc
  · rw [boundImplies_real] at hc
    have hi : implies lower s₁ s₂ a b := of_decide_eq_true (Option.some.inj hc)
    refine ⟨by rw [boundImplied_real, decide_eq_true hi]; rfl, fun x => ?_⟩
    rw [h, h₁, axisBound_real, axisBound_real]
    exact mask_implied (meets_of_implies hi) _
  · rw [boundImplies_real] at hc
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
point is between the first two the observation is a zero whatever the third
is. -/
theorem third_second_integral (lower s₁ s₂ s₃ : Bool) (t₁ t₂ t₃ : Option ℝ)
    {w w₁ w₂ : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x) (Value.mask (axisBound (!lower) s₃ t₃ x) (r x))))
    (h₁ : ∀ x, w₁ x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    (h₂ : ∀ x, w₂ x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₃ t₃ x) (r x))) :
    partialIntegral volume w =
      Value.mask (boundsMeet lower s₁ s₂ t₁ t₂)
        (Value.add (Value.mask (boundImplies (!lower) s₂ s₃ t₂ t₃) (partialIntegral volume w₁))
          (Value.mask (boundImplied (!lower) s₂ s₃ t₂ t₃) (partialIntegral volume w₂))) := by
  refine integral_cases_within (fun hN => ?_) (fun hN x => ?_) (fun hN hc => ?_)
    (fun hN hc => ?_) (fun hN hc => ?_)
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
theorem third_first_integral (lower s₁ s₂ s₃ : Bool) (t₁ t₂ t₃ : Option ℝ)
    {w w₁ w₂ : ℝ → Option ℝ} (r : ℝ → Option ℝ)
    (h : ∀ x, w x = Value.mask (axisBound lower s₁ t₁ x)
      (Value.mask (axisBound (!lower) s₂ t₂ x) (Value.mask (axisBound lower s₃ t₃ x) (r x))))
    (h₁ : ∀ x, w₁ x =
      Value.mask (axisBound lower s₁ t₁ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x)))
    (h₂ : ∀ x, w₂ x =
      Value.mask (axisBound lower s₃ t₃ x) (Value.mask (axisBound (!lower) s₂ t₂ x) (r x))) :
    partialIntegral volume w =
      Value.mask (boundsMeet lower s₁ s₂ t₁ t₂)
        (Value.add (Value.mask (boundImplies lower s₁ s₃ t₁ t₃) (partialIntegral volume w₁))
          (Value.mask (boundImplied lower s₁ s₃ t₁ t₃) (partialIntegral volume w₂))) := by
  refine integral_cases_within (fun hN => ?_) (fun hN x => ?_) (fun hN hc => ?_)
    (fun hN hc => ?_) (fun hN hc => ?_)
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
  exact StepSource.same_side_integral lower s₁ s₂ t₁ t₂ r h h₁ h₂

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
  exact StepSource.third_second_integral lower s₁ s₂ s₃ t₁ t₂ t₃ r h h₁ h₂

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
  exact StepSource.third_first_integral lower s₁ s₂ s₃ t₁ t₂ t₃ r h h₁ h₂

end QSym.Distribution.DensityProgram
