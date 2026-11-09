import OddPrimitiveSequence
import Lean

set_option autoImplicit false
set_option warningAsError true

open Lean Elab Command in
elab "#odd_primitive_inventory" : command => do
  let env ← getEnv
  let proofModules := #[`MidpointRational, `OddTriangular, `MidpointPrimitive, `OddPrimitiveSequence]
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if proofModules.contains modName then
        logInfo m!"ODD_PRIMITIVE_DECL {name}"
        logInfo m!"ODD_PRIMITIVE_MODULE {name} {modName}"
        logInfo m!"ODD_PRIMITIVE_SAFETY {name} {info.isUnsafe}"

#odd_primitive_inventory
