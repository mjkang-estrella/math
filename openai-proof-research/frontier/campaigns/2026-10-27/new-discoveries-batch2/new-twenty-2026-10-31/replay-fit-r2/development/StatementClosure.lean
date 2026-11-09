import Endpoint
import Lean
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := (← IO.FS.readFile "../modules.txt").trimAscii.toString.splitOn "\n"
  let isPacket := fun n => match env.getModuleIdxFor? n with
    | some i => modules.contains (env.header.moduleNames[i]!).toString
    | none => false
  let endpoint := ``MathDB330264.conjecture_false
  let mut seen : NameSet := {} 
  seen := seen.insert endpoint
  let mut todo := (env.find? endpoint).get!.type.getUsedConstants.toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if isPacket n && !seen.contains n then
      seen := seen.insert n
      let ci := (env.find? n).get!
      todo := ci.type.getUsedConstants.toList ++ todo
      if let some v := ci.value? (allowOpaque := true) then
        todo := v.getUsedConstants.toList ++ todo
  let mut closure : Array Json := #[]
  let mut spans : Array Json := #[]
  let mut forbidden : Array String := #[]
  for (n, ci) in env.constants.toList do
    if isPacket n then
      let modName := (env.header.moduleNames[(env.getModuleIdxFor? n).get!]!).toString
      let range ← findDeclarationRanges? n
      let r := match range with
        | some r => Json.mkObj [("startLine", toJson r.range.pos.line),
            ("startColumn", toJson r.range.pos.column),
            ("endLine", toJson r.range.endPos.line), ("endColumn", toJson r.range.endPos.column)]
        | none => Json.null
      let row := Json.mkObj [("name", toJson n.toString), ("module", toJson modName), ("range", r)]
      spans := spans.push row
      if seen.contains n then closure := closure.push row
      if ci.isUnsafe || ci.isPartial || (Lean.Compiler.getImplementedBy? env n).isSome ||
          (getExternAttrData? env n).isSome || (n.toString.splitOn "_unsafe_rec").length > 1 then
        forbidden := forbidden.push n.toString
  liftIO <| IO.FS.writeFile "closure-raw.json" (Json.mkObj [("closure", toJson closure), ("packetDeclarations", toJson spans)]).pretty
  let axs ← liftCoreM (Lean.collectAxioms endpoint)
  for a in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "disallowed endpoint axiom: {a}"
  logInfo m!"STATEMENT CLOSURE: {closure.size} declarations; {spans.size} packet declarations audited"
  for row in closure do logInfo m!"{row.compress}"
  liftIO <| IO.FS.writeFile "forbidden-metadata.json" (toJson forbidden).pretty
  unless forbidden.isEmpty do throwError "forbidden metadata: {forbidden}"
#print axioms MathDB330264.conjecture_false
