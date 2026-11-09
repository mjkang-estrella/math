import Encoding
open Lean
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let modName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.header.mainModule
    if modName == `Encoding then
      if ci.isUnsafe || ci.isPartial || n.toString.endsWith "_unsafe_rec" then
        throwError "Forbidden Encoding declaration: {n}"
  logInfo "ENCODING_GENERATED_DECLARATIONS_SAFE"
