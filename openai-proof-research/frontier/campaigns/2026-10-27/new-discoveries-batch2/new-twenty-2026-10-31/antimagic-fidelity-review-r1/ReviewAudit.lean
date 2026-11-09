import AntimagicFinal7A
import Antimagic7AAudit
import Antimagic6AAudit
import Antimagic5AAudit
import Antimagic4AAudit
import Antimagic3Audit
import Antimagic2Audit
import Audit
import Lean
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let mut rows : Array String := #[]
  for (n, c) in env.constants.toList do
    let module := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i]!.toString
      | none => "CURRENT"
    if module.startsWith "Antimagic" || n.toString.startsWith "Antimagic" then
      let impl := (Lean.Compiler.getImplementedBy? env n).isSome
      let ext := (getExternAttrData? env n).isSome
      let ax := match c with | .axiomInfo _ => true | _ => false
      rows := rows.push s!"{n}\t{module}\t{c.isUnsafe}\t{c.isPartial}\t{impl}\t{ext}\t{ax}"
      if c.isUnsafe || c.isPartial || impl || ext || ax || n.toString.endsWith "_unsafe_rec" then
        throwError "forbidden local metadata: {n}"
  liftIO <| IO.FS.writeFile "evidence/local-metadata.tsv" (String.intercalate "\n" rows.toList ++ "\n")
  logInfo m!"Independent local metadata audit PASS: {rows.size} declarations"
#print axioms Antimagic.Round7A.even_case
#print axioms Antimagic.Round7A.mathdb_354228
#check Antimagic.modelStructure
#check Antimagic.modelLeaves
#check Antimagic.lowerBound
#check Antimagic.star_construction
#check Antimagic.binary_construction
#check Antimagic.Round4A.depthTwoConstruction
#check Antimagic.Round6A.nonbinaryHigherConstruction
#check Antimagic.Round7A.binaryHigherConstruction
#check Antimagic.Round4B.modelBridge
