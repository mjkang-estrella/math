import ConferenceMDS324342
import Controls
import Lean
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? n with
      | some idx => ["ConferenceMDS324342", "Controls"].contains (env.header.moduleNames[idx]!).toString
      | none => false
    if localModule then
      count := count + 1
      let impl := (Lean.Compiler.getImplementedBy? env n).isSome
      let ext := (getExternAttrData? env n).isSome
      if ci.isUnsafe || ci.isPartial || impl || ext || (n.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "forbidden declaration metadata: {n}"
      let axs ← liftCoreM (Lean.collectAxioms n)
      for a in axs do
        unless allowed.contains a do throwError "disallowed axiom {n}: {a}"
      rows := rows.push s!"{n}\t{ci.isUnsafe}\t{ci.isPartial}\t{impl}\t{ext}"
  liftIO <| IO.FS.writeFile "metadata.tsv" (String.intercalate "\n" rows.toList ++ "\n")
  logInfo m!"METADATA declarations={count} forbidden=0; all local axioms allowed"
#print axioms ConferenceMDS.conjecture5_false
#print axioms ConferenceMDS.Control.paley3_satisfies
