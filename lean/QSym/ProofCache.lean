import Lean.Elab.Tactic

open Lean Meta Elab Tactic
namespace QSym

private structure ProofCache where
  constants : NameMap ConstantInfo := {}
  region : Option CompactedRegion := none

private initialize proofCache : IO.Ref (Option ProofCache) ← IO.mkRef none

private def cachedProofs : IO ProofCache := do
  if let some cache ← proofCache.get then return cache
  let mut cache : ProofCache := {}
  if let some path ← IO.getEnv "QSYM_PROOF_CACHE" then
    let (data, region) ← readModuleData path
    cache := { cache with region := some region }
    for c in data.constants do
      cache := { cache with constants := cache.constants.insert c.name c }
  proofCache.set (some cache)
  return cache

private partial def expandAux (cache : ProofCache) (env : Environment) (e : Expr)
    (visiting : NameSet := {}) : TacticM Expr :=
  Core.transform e (pre := fun e => do
    let .const name levels := e | return .continue
    if env.contains name then return .continue
    unless isPrivateName name || name.isInternal do throwError "missing cache dependency: {name}"
    if visiting.contains name then throwError "recursive cache dependency: {name}"
    let some c := cache.constants.find? name | throwError "missing cache auxiliary: {name}"
    let value ← match c with
      | .thmInfo v => pure v.value
      | .defnInfo v =>
        unless v.safety == .safe do throwError "unsafe cache auxiliary: {name}"
        pure v.value
      | _ => throwError "unsupported cache auxiliary: {name}"
    return .done (← expandAux cache env (value.instantiateLevelParams c.levelParams levels)
      (visiting.insert name)))

elab "qsym_cached" : tactic => withMainContext do
  let some name ← Term.getDeclName? | throwError "no declaration"
  let cache ← cachedProofs
  let some (.thmInfo old) := cache.constants.find? name | throwError "no cached proof"
  unless old.levelParams.isEmpty do throwError "polymorphic cache entry"
  let goal ← getMainGoal
  let args := (← getLCtx).foldl (init := #[]) fun xs d =>
    if d.isImplementationDetail then xs else xs.push d.toExpr
  let value ← expandAux cache (← getEnv) old.value
  let proof := mkAppN value args
  let type ← instantiateMVars (← goal.getType)
  let closedType ← mkForallFVars args type
  let closedProof ← mkLambdaFVars args proof
  let decl := Declaration.thmDecl { name, levelParams := [], type := closedType, value := closedProof }
  -- A cached term is only a candidate. Always ask the actual kernel, against
  -- the current type and environment; never import the cached declarations.
  match Kernel.Environment.addDeclCore (← getEnv).toKernelEnv
      (Core.getMaxHeartbeats (← getOptions)).toUSize decl none with
  | .error e => throwError "cached proof does not check: {e.toMessageData (← getOptions)}"
  | .ok _ =>
    goal.assign proof
    replaceMainGoal []
    logInfo "rechecked cached proof"

macro "qsym_cached% " proof:term : term => `(by first | qsym_cached | exact $proof)

end QSym
