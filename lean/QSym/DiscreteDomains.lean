import QSym.RefinementBase

namespace QSym
open Lean Meta Elab Tactic in
elab "qsym_discrete_goal" : tactic => withMainContext do
  for decl in ← getLCtx do
    if ← isProp decl.type then continue
    let t ← whnf decl.type
    let t ← if t.isAppOfArity ``Option 1 then whnf t.getAppArgs[0]! else pure t
    unless t.isConstOf ``Nat || t.isConstOf ``Int || t.isConstOf ``Bool do
      throwError "not a discrete scalar goal"

macro "qsym_discrete" : tactic => `(tactic| (
  qsym_discrete_goal
  classical
  simp_all [Value.Refines, Value.Defined, Function1.apply, Function2.apply,
    Functions.addN, Functions.mulN, Functions.subN, Functions.ltN, Functions.leN, Functions.nonzeroN,
    Functions.castNZ, Functions.addZ, Functions.mulZ, Functions.ltZ, Functions.leZ, Functions.nonzeroZ,
    Value.not, Value.or, Value.and]
  all_goals repeat' split at *
  all_goals simp_all
  all_goals omega
))
end QSym
