import Endpoint
import Closure107
import AliasControl
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let source := match env.getModuleIdxFor? name with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString
      | none => env.mainModule.toString
    if ["Literal", "Semantics", "Concrete", "Nodes", "Controls", "AliasControl",
        "Endpoint", "Final", "Delta153", "RawClosure", "RawResult"].contains source ||
        source.startsWith "Closure" || source.startsWith "Move" then
      count := count + 1
      if info.isUnsafe || info.isPartial ||
          (Lean.Compiler.getImplementedBy? env name).isSome ||
          (Lean.getExternAttrData? env name).isSome ||
          (name.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "Rejected local declaration {name} in {source}"
      match info with
      | .axiomInfo _ => throwError "Rejected local added axiom {name}"
      | _ => pure ()
  logInfo m!"Audited {count} local declarations by defining module, including private helpers: metadata clean"
#print axioms Endpoint.conditional_negation

