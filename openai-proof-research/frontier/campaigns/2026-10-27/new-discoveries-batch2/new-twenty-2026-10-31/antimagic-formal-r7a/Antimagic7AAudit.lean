import AntimagicFinal7A
import Antimagic2Regression
import AntimagicRegression
import Lean
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 0
run_cmd do
  let env := (← getEnv).setExporting false
  let mut seeds : Array Name := #[]
  for (n, _) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? n with
      | some idx => (env.header.moduleNames[idx]!).toString.startsWith "Antimagic"
      | none => false
    if localModule then seeds := seeds.push n
  let mut seen : NameSet := {}
  let mut todo := seeds
  for _ in [:200] do
    let mut next := #[]
    for n in todo do
      if !seen.contains n then
        seen := seen.insert n
        let some ci := env.find? n | throwError "missing {n}"
        next := next ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          next := next ++ v.getUsedConstants
        if let .inductInfo v := ci then next := next ++ v.ctors.toArray
        next := next ++ ci.all.toArray
        let companion := Name.str n "_unsafe_rec"
        if (env.find? companion).isSome then next := next.push companion
    todo := next
  unless todo.isEmpty do throwError "closure fuel exhausted"
  let mut rows : Array String := #[]
  for n in seen.toArray.qsort Name.lt do
    let some ci := env.find? n | throwError "missing {n}"
    let module := match env.getModuleIdxFor? n with
      | some idx => (env.header.moduleNames[idx]!).toString
      | none => "CURRENT"
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | _ => "declaration"
    let mut deps := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
    for d in deps do unless seen.contains d do throwError "not closed: {n} -> {d}"
    rows := rows.push s!"{n}\t{module}\t{kind}\t{ci.isUnsafe}\t{ci.isPartial}\t{(Lean.Compiler.getImplementedBy? env n).isSome}\t{(getExternAttrData? env n).isSome}"
  liftIO <| IO.FS.writeFile "audit.tsv" (String.intercalate "\n" rows.toList ++ "\n")
  logInfo m!"audited {seen.size} declarations, seeds {seeds.size}; closure verified"
