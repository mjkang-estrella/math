import ClockMarginals
import MarkedCounts
set_option autoImplicit false
set_option warningAsError true
set_option pp.all true
set_option pp.maxSteps 10000000
set_option pp.deepTerms true
set_option format.width 160
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) =>
    match env.getModuleIdxFor? n with
    | some i => if ["ClockMarginals", "MarkedCounts"].contains env.header.moduleNames[i]!.toString then some n else none
    | none => none
  for n in names.mergeSort (fun a b => a.toString ≤ b.toString) do
    let some info := env.find? n | throwError "missing declaration"
    let origin := env.header.moduleNames[(env.getModuleIdxFor? n).get!]!
    logInfo m!"DECL|{n}|ORIGIN|{origin}|UNSAFE|{info.isUnsafe}"
    match info with
    | .defnInfo d => logInfo m!"SAFETY|{n}|{repr d.safety}"
    | _ => logInfo m!"SAFETY|{n}|nondefinition"
    elabCommand (← `(#check $(mkIdent n)))
    elabCommand (← `(#print axioms $(mkIdent n)))
