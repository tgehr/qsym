import QSym.DistributionAtomRows

/-! Finite mixtures of point masses.

Weighting and composition are computed constructor by constructor on atoms,
scalings, sums and zero. These are equalities of presentations: no quotient by
equality of measures is used, coefficients are not merged, and a zero
coefficient retains its atom. Every law includes the partial operands.

The real bind is itself structural in sums and scalings, so its laws need no
condition on the source: a parameter chart below a sum keeps its row interpreter.
-/
namespace QSym.Distribution

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

/-- An empty distribution visits no outcome. The weight function itself must
be present, but its body is never evaluated. -/
theorem weight_zeroValue {α : Type} (f : Option (α → Option ℝ)) :
    weightValue f zeroValue = f.bind (fun _ => zeroValue) := by
  cases f <;> rfl

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

/-! The real bind follows the same constructors, also below a parameter chart. -/
theorem realBind_none_left {α : Type} (k : Option (α → Option (D ℝ))) :
    realBindValue none k = none := rfl

theorem realBind_diracValue {α : Type} (a : Option α) (k : Option (α → Option (D ℝ))) :
    realBindValue (diracValue a) k = k.bind (fun g => a.bind g) := by
  cases a <;> cases k <;> rfl

theorem realBind_addValue {α : Type} (x y : Option (D α)) (k : Option (α → Option (D ℝ))) :
    realBindValue (addValue x y) k = addValue (realBindValue x k) (realBindValue y k) := by
  cases x with
  | none => rfl
  | some x =>
    cases y with
    | none =>
      cases k with
      | none => rfl
      | some k =>
        change none = addValue (realBind x k) none
        cases realBind x k <;> rfl
    | some y => cases k <;> rfl

theorem realBind_scaleValue {α : Type} (r : Option ℝ) (d : Option (D α))
    (k : Option (α → Option (D ℝ))) :
    realBindValue (scaleValue r d) k = scaleValue r (realBindValue d k) := by
  cases r with
  | none => rfl
  | some r =>
    cases d with
    | none => rfl
    | some d => cases k <;> rfl

theorem realBind_zeroValue {α : Type} (k : Option (α → Option (D ℝ))) :
    realBindValue (zeroValue (α := α)) k = k.bind (fun _ => zeroValue) := by
  cases k <;> rfl

end GraphFibre
end QSym.Distribution
