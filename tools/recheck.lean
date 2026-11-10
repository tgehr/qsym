import Lean

open Lean

private def declaration (c : ConstantInfo) : Except String Declaration :=
  match c with
  | .thmInfo v => .ok (.thmDecl v)
  | .defnInfo v =>
    if v.safety == .safe then .ok (.defnDecl v) else .error s!"unsafe declaration: {c.name}"
  | _ => .error s!"unsupported declaration: {c.name}"

private partial def replay (constants : NameMap ConstantInfo) (name : Name)
    (env : Kernel.Environment) (visiting : NameSet := {}) : Except String Kernel.Environment := do
  if (env.find? name).isSome then return env
  if visiting.contains name then throw s!"cyclic declaration: {name}"
  let some c := constants.find? name | throw s!"missing declaration: {name}"
  let decl ← declaration c
  let mut env := env
  for dep in c.type.getUsedConstants ++ c.value!.getUsedConstants do
    env ← replay constants dep env (visiting.insert name)
  match Kernel.Environment.addDeclCore env 200000000 decl none with
  | .ok checked => return checked
  | .error _ => throw s!"kernel rejected: {name}"

private def recheck (base : Environment) (auditState : CollectAxioms.State)
    (path : System.FilePath) : IO (Except String (Nat × CollectAxioms.State)) := do
  let (data, _region) ← readModuleData path
  let mut constants : NameMap ConstantInfo := {}
  for c in data.constants do
    if base.contains c.name then return .error s!"import collision: {c.name}"
    if constants.contains c.name then return .error s!"duplicate declaration: {c.name}"
    constants := constants.insert c.name c
  let mut env := base.toKernelEnv
  let mut checkedNames : Array Name := #[]
  for c in data.constants do
    -- The compiler also stores unsafe executable implementations. Never load
    -- those into the logical environment; references to them still fail replay.
    if let .defnInfo v := c then
      if v.safety != .safe then continue
    match replay constants c.name env with
    | .error message => return .error message
    | .ok next => env := next
    checkedNames := checkedNames.push c.name
  let checked := Environment.ofKernelEnv env
  let mut state := auditState
  for name in checkedNames do
    state := ((CollectAxioms.collect name).run checked).run state |>.2
  let unexpected := state.axioms.filter fun name =>
    name != ``propext && name != ``Classical.choice && name != ``Quot.sound
  if !unexpected.isEmpty then return .error s!"unexpected axioms: {unexpected}"
  if checkedNames.isEmpty then return .error "no logical declarations"
  -- Only imported declarations are immutable across certificates. Their axiom
  -- traversal can be shared; every local name must be visited afresh next time.
  for c in data.constants do state := { state with visited := state.visited.erase c.name }
  return .ok (checkedNames.size, state)

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let base ← importModules #[{ module := `QSym }] {}
  let mut auditState : CollectAxioms.State := {}
  for path in args do
    let result ← try recheck base auditState path catch e => pure (.error e.toString)
    if let .ok (_, next) := result then auditState := next
    let fields := [("path", toJson path)] ++ match result with
      | .ok (count, _) => [("ok", toJson true), ("declarations", toJson count)]
      | .error message => [("ok", toJson false), ("error", toJson message)]
    IO.println (Json.compress (Json.mkObj fields))
  return 0
