import MaskRaw0000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    let owner := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i]!.toString
      | none => "RawAudit"
    if owner.startsWith "Mask" || owner == "RawAudit" then
      count := count + 1
      if ci.isUnsafe || ci.isPartial || (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n ||
          (n.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "Forbidden local metadata: {n}"
      match ci with
      | .axiomInfo _ => throwError "Local assumption: {n}"
      | _ => pure ()
  logInfo m!"Metadata audit passed: {count} declarations"
#print axioms Percolation.MaskRUP.rawSound13561
