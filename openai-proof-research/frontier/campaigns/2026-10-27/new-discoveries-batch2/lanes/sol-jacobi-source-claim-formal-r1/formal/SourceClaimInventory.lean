import SourceClaim
import Lean

set_option autoImplicit false
set_option warningAsError true
set_option pp.privateNames true

open Lean Elab Command in
elab "#source_claim_inventory" : command => do
  let env ← getEnv
  let proofModules := #[`DyadicArithmetic, `HalfSubstitution, `SourceUpperBound, `SourceSharpness, `SourceClaim]
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if proofModules.contains modName then
        logInfo m!"SOURCECLAIM_DECL {name}"
        logInfo m!"SOURCECLAIM_MODULE {name} {modName}"
        logInfo m!"SOURCECLAIM_SAFETY {name} {info.isUnsafe}"
        if info.isUnsafe then
          throwError m!"Unsafe declaration: {name}"

#source_claim_inventory
