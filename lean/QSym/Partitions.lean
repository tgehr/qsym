import QSym.RefinementBase

namespace QSym.Value

theorem not_not (p : Option Bool) : not (not p)=p := by cases p <;> simp [not]

theorem partition {α β : Type} [AddZeroClass α] [AddZeroClass β]
    (f : Option α → Option β) (hf : f none=none)
    (p q : Option Bool) (x y : Option α)
    (hp : Refines (Functions.eqB.apply q (not p)) (some true)) :
    f (add (mask p x) (mask q y)) = add (mask p (f x)) (mask q (f y)) := by
  have add_none {γ : Type} [Add γ] (x : Option γ) : add x none=none := by cases x <;> rfl
  cases p with
  | none => simp [mask, add, hf]
  | some p =>
    cases q with
    | none => simp only [mask, add_none, hf]
    | some q =>
      have hq : q=(!p) := by simpa [Refines, Function2.apply, Functions.eqB, not] using hp
      subst q
      cases p <;> simp [mask, add_zero_left, add_zero_right]

theorem apply_partition {α β : Type} [AddZeroClass α] [AddZeroClass β]
    (f : Function1 α β) (p q : Option Bool) (x y : Option α)
    (hp : Refines (Functions.eqB.apply q (not p)) (some true)) :
    f.apply (add (mask p x) (mask q y)) =
      add (mask p (f.apply x)) (mask q (f.apply y)) :=
  partition f.apply rfl p q x y hp

theorem map_partition {α β : Type} [AddZeroClass α] [AddZeroClass β]
    (f : α → β) (p q : Option Bool) (x y : Option α)
    (hp : Refines (Functions.eqB.apply q (not p)) (some true)) :
    (add (mask p x) (mask q y)).map f =
      add (mask p (x.map f)) (mask q (y.map f)) :=
  partition (fun x => x.map f) rfl p q x y hp

theorem refines_apply_partition {α β : Type} [AddZeroClass α] [AddZeroClass β]
    (f : Function1 α β) (p q : Option Bool) (x y : Option α)
    (hp : Refines (Functions.eqB.apply q (not p)) (some true)) :
    Refines (f.apply (add (mask p x) (mask q y)))
      (add (mask p (f.apply x)) (mask q (f.apply y))) :=
  refines_of_eq (apply_partition f p q x y hp)

theorem refines_abs_partition (p q : Option Bool) (x y : Option ℝ)
    (hp : Refines (Functions.eqB.apply q (not p)) (some true)) :
    Refines (abs (add (mask p x) (mask q y)))
      (add (mask p (abs x)) (mask q (abs y))) :=
  refines_of_eq (map_partition (fun x : ℝ => |x|) p q x y hp)

end QSym.Value

namespace QSym

open Lean Meta Elab Tactic in
elab "qsym_partition_goal" : tactic => do
  let t ← getMainTarget
  unless t.isAppOfArity ``Value.Refines 3 do throwError "not a refinement"
  let source := t.getAppArgs[1]!
  let root := source.getAppFn
  unless root.isConstOf ``Function1.apply || root.isConstOf ``Value.abs do
    throwError "not a unary function"
  unless (source.find? fun e => e.isConstOf ``Value.mask).isSome do
    throwError "not a partition"

macro "qsym_partition" : tactic => `(tactic| (
  qsym_partition_goal
  simp only [Value.not_not] at *
  first
  | (apply Value.refines_apply_partition; assumption)
  | (apply Value.refines_abs_partition; assumption)
))

end QSym
