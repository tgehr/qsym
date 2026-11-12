import Lean.Elab.Print
import QSym.Progress

open Lean Elab Command
namespace QSym

-- This is an audit command, not a proof generator. Reuse Lean's collector and
-- retain its visited set in the immutable environment, so dependencies common
-- to many certificates are walked once. Backtracking also restores the cache.
private instance : Inhabited CollectAxioms.State := ⟨{}⟩
private initialize axiomCache : EnvExtension CollectAxioms.State ← registerEnvExtension (pure {})

syntax "#qsym_check_axioms " ident : command
elab_rules : command
  | `(#qsym_check_axioms $id:ident) => do
    let names ← liftCoreM <| realizeGlobalConstWithInfos id
    let env ← getEnv
    let mut state := axiomCache.getState env
    for name in names do
      unless (env.checked.get.find? name).isSome do
        throwError "declaration has not been kernel-checked: {name}"
      let (_, next) := ((CollectAxioms.collect name).run env).run state
      state := next
    let unexpected := state.axioms.filter fun name =>
      name != ``propext && name != ``Classical.choice && name != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "unexpected axioms: {unexpected}"
    modifyEnv fun env => axiomCache.setState env state
    for name in names do liftCoreM <| Progress.report "checked" name
    logInfo m!"checked axioms for {names}"

end QSym
