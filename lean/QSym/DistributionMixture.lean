import QSym.DistributionAtomRows

/-! Finite mixtures of point masses.

Weighting and composition are computed constructor by constructor on atoms,
scalings, sums and zero. These are equalities of presentations: no quotient by
equality of measures is used, coefficients are not merged, and a zero
coefficient retains its atom. Every law includes the partial operands.

A real-valued bind out of a parameter chart uses the row interpreter instead of
the ordered integral, so the real laws require a source whose root is not a
chart. The frontend discharges that premise from the source constructor.
-/
namespace QSym.Distribution

/-- Every root except a parameter chart. -/
def Presentation.Mixture {α : Type} : D α → Prop
  | .density _ _ => False
  | _ => True

def MixtureValue {α : Type} (d : Option (D α)) : Prop := ∀ a, d = some a → a.Mixture

theorem mixture_diracValue {α : Type} (a : Option α) : MixtureValue (diracValue a) := by
  intro d h
  cases a with
  | none => cases h
  | some a => cases h; trivial

theorem mixture_zeroValue {α : Type} : MixtureValue (zeroValue (α := α)) := by
  intro d h
  cases h; trivial

theorem mixture_addValue {α : Type} (x y : Option (D α)) : MixtureValue (addValue x y) := by
  intro d h
  cases x with
  | none => cases h
  | some x =>
    cases y with
    | none => cases h
    | some y => cases h; trivial

theorem mixture_scaleValue {α : Type} (r : Option ℝ) (d : Option (D α)) :
    MixtureValue (scaleValue r d) := by
  intro a h
  cases r with
  | none => cases h
  | some r =>
    cases d with
    | none => cases h
    | some d => cases h; trivial

/-! The constructors are strict in a missing distribution. -/
theorem add_none_left {α : Type} (y : Option (D α)) : addValue none y = none := rfl

theorem add_none_right {α : Type} (x : Option (D α)) : addValue x none = none := by
  cases x <;> rfl

theorem scale_none_right {α : Type} (r : Option ℝ) :
    scaleValue r (none : Option (D α)) = none := by
  cases r <;> rfl

theorem weight_none_right {α : Type} (f : Option (α → Option ℝ)) :
    weightValue f none = none := by
  cases f <;> rfl

theorem bind_none_left {α β : Type} (k : Option (α → Option (D β))) :
    bindValue none k = none := rfl

theorem densityAt_none_left (x : Option ℝ) : densityAtValue none x = none := rfl

theorem densityAt_none_right (d : Option (D ℝ)) : densityAtValue d none = none := by
  cases d <;> rfl

/-- A function of the outcome is evaluated at an atom. The coefficient is
strict: a weight that is missing at the atom makes the result missing. -/
theorem weight_diracValue {α : Type} (f : Option (α → Option ℝ)) (a : Option α) :
    weightValue f (diracValue a) = scaleValue (f.bind (fun g => a.bind g)) (diracValue a) := by
  cases f with
  | none => rfl
  | some f =>
    cases a with
    | none => rfl
    | some a =>
      change (f a).map (fun r => Presentation.scale r (.dirac a)) = scaleValue (f a) (some (.dirac a))
      cases f a <;> rfl

theorem weight_addValue {α : Type} (f : Option (α → Option ℝ)) (x y : Option (D α)) :
    weightValue f (addValue x y) = addValue (weightValue f x) (weightValue f y) := by
  cases f with
  | none => rfl
  | some f =>
    cases x with
    | none => rfl
    | some x =>
      cases y with
      | some y => rfl
      | none =>
        change none = addValue (weight f x) none
        cases weight f x <;> rfl

theorem weight_scaleValue {α : Type} (f : Option (α → Option ℝ)) (r : Option ℝ)
    (d : Option (D α)) :
    weightValue f (scaleValue r d) = scaleValue r (weightValue f d) := by
  cases f with
  | none => cases r <;> rfl
  | some f =>
    cases r with
    | none => rfl
    | some r => cases d <;> rfl

/-- Left identity of composition, including a missing atom or kernel. -/
theorem bind_diracValue {α β : Type} (a : Option α) (k : Option (α → Option (D β))) :
    bindValue (diracValue a) k = k.bind (fun g => a.bind g) := by
  cases a <;> cases k <;> rfl

theorem bind_addValue {α β : Type} (x y : Option (D α)) (k : Option (α → Option (D β))) :
    bindValue (addValue x y) k = addValue (bindValue x k) (bindValue y k) := by
  cases x with
  | none => rfl
  | some x =>
    cases y with
    | none =>
      cases k with
      | none => rfl
      | some k =>
        change none = addValue (bind x k) none
        cases bind x k <;> rfl
    | some y => cases k <;> rfl

theorem bind_scaleValue {α β : Type} (r : Option ℝ) (d : Option (D α))
    (k : Option (α → Option (D β))) :
    bindValue (scaleValue r d) k = scaleValue r (bindValue d k) := by
  cases r with
  | none => rfl
  | some r =>
    cases d with
    | none => rfl
    | some d => cases k <;> rfl

theorem bind_zeroValue {α β : Type} (k : Option (α → Option (D β))) :
    bindValue (zeroValue (α := α)) k = k.bind (fun _ => zeroValue) := by
  cases k <;> rfl

namespace GraphFibre

theorem realBind_none_left {α : Type} (k : Option (α → Option (D ℝ))) :
    realBindValue none k = none := rfl

/-- Away from parameter charts the real bind is the ordinary bind. -/
theorem realBind_of_mixture {α : Type} (d : Option (D α)) (k : Option (α → Option (D ℝ)))
    (h : MixtureValue d) : realBindValue d k = bindValue d k := by
  cases d with
  | none => rfl
  | some d =>
    cases k with
    | none => rfl
    | some k =>
      cases d with
      | density w v => exact (h _ rfl).elim
      | invalid | zero | dirac | add | scale | integral => rfl

theorem realBind_diracValue {α : Type} (a : Option α) (k : Option (α → Option (D ℝ))) :
    realBindValue (diracValue a) k = k.bind (fun g => a.bind g) :=
  (realBind_of_mixture _ k (mixture_diracValue a)).trans (bind_diracValue a k)

theorem realBind_addValue {α : Type} (x y : Option (D α)) (k : Option (α → Option (D ℝ)))
    (hx : MixtureValue x) (hy : MixtureValue y) :
    realBindValue (addValue x y) k = addValue (realBindValue x k) (realBindValue y k) := by
  rw [realBind_of_mixture _ k (mixture_addValue x y), realBind_of_mixture x k hx,
    realBind_of_mixture y k hy]
  exact bind_addValue x y k

theorem realBind_scaleValue {α : Type} (r : Option ℝ) (d : Option (D α))
    (k : Option (α → Option (D ℝ))) (hd : MixtureValue d) :
    realBindValue (scaleValue r d) k = scaleValue r (realBindValue d k) := by
  rw [realBind_of_mixture _ k (mixture_scaleValue r d), realBind_of_mixture d k hd]
  exact bind_scaleValue r d k

theorem realBind_zeroValue {α : Type} (k : Option (α → Option (D ℝ))) :
    realBindValue (zeroValue (α := α)) k = k.bind (fun _ => zeroValue) :=
  (realBind_of_mixture _ k mixture_zeroValue).trans (bind_zeroValue k)

end GraphFibre
end QSym.Distribution
