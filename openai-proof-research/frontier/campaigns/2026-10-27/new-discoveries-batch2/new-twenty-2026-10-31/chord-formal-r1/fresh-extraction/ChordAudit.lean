import ChordFinal
import Lean
open Lean Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let localMods := #[`ChordCore, `ChordRepresentative, `ChordSanity, `ChordSmall, `ChordBridgeChecks, `ChordControls, `ChordFourBase0, `ChordFourChunk0_0, `ChordFourChunk0_1, `ChordFourChunk0_2, `ChordFourChunk0_3, `ChordFour0, `ChordFourBase1, `ChordFourChunk1_0, `ChordFourChunk1_1, `ChordFourChunk1_2, `ChordFourChunk1_3, `ChordFour1, `ChordFourBase2, `ChordFourChunk2_0, `ChordFourChunk2_1, `ChordFourChunk2_2, `ChordFourChunk2_3, `ChordFour2, `ChordFourBase3, `ChordFourChunk3_0, `ChordFourChunk3_1, `ChordFourChunk3_2, `ChordFourChunk3_3, `ChordFour3, `ChordFourWitnesses, `ChordRemaining, `ChordFinal]
  let mut closure : NameSet := ({} : NameSet).insert `ChordFinal
  for _ in [:env.header.moduleNames.size] do
    for i in [:env.header.moduleNames.size] do
      if closure.contains env.header.moduleNames[i]! then
        for imp in env.header.moduleData[i]!.imports do
          closure := closure.insert imp.module
  let mut inventory : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if closure.contains env.header.moduleNames[i]! then
      for n in env.header.moduleData[i]!.constNames do inventory := inventory.insert n
  let mut audited : NameSet := {}
  let mut localCount : Nat := 0
  let mut rows : Array String := #[]
  for (n, ci0) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let modName := env.header.moduleNames[idx.toNat]!
      if closure.contains modName then
        let ci := (env.checked.get.find? n).getD ci0
        let isLocal := localMods.contains modName
        let axs ← collectAxioms n
        let ib := (Compiler.getImplementedBy? env n).isSome
        let ex := (externAttr.getParam? env n).isSome
        let companion := decide ((n.toString.splitOn "_unsafe_rec").length > 1)
        if isLocal then
          localCount := localCount+1
          if ci.isUnsafe || ci.isPartial || ci.isAxiom || ib || ex || companion then
            throwError "Forbidden LOCAL metadata {n}"
          for a in axs do
            unless #[`propext, `Classical.choice, `Quot.sound].contains a do
              throwError "Forbidden LOCAL transitive axiom {n}: {a}"
        let mut deps := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
        rows := rows.push (Json.mkObj [
          ("name", toJson n.toString), ("module", toJson modName.toString),
          ("local", toJson isLocal), ("unsafe", toJson ci.isUnsafe),
          ("partial", toJson ci.isPartial), ("axiom", toJson ci.isAxiom),
          ("unsafe_rec", toJson companion), ("implemented_by", toJson ib),
          ("extern", toJson ex), ("axioms", toJson (axs.map Name.toString)),
          ("deps_allowOpaque", toJson (deps.map Name.toString))]).compress
        audited := audited.insert n
  for n in inventory do
    unless audited.contains n do throwError "Missing declaration {n}"
  for n in audited do
    unless inventory.contains n do throwError "Outside closure {n}"
  liftIO <| IO.FS.writeFile "audit.jsonl" (String.intercalate "\n" rows.toList ++ "\n")
  logInfo m!"CLOSURE inventory={inventory.size} audited={audited.size} LOCAL={localCount}; sets equal"
