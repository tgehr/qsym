import Lean

open Lean
namespace QSym.Progress

private initialize failed : IO.Ref Bool ← IO.mkRef false

def report (event : String) (name : Name) : CoreM Unit := do
  let some path ← IO.getEnv "QSYM_PROGRESS_FILE" | return
  if ← failed.get then return
  try
    let record := Json.mkObj [
      ("event", toJson event), ("name", toJson name),
      ("module", toJson (← getEnv).mainModule), ("time_ms", toJson (← IO.monoMsNow))]
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn record.compress
      handle.flush
  catch e =>
    failed.set true
    logWarning m!"Could not write Lean progress: {e.toMessageData}"

end QSym.Progress
