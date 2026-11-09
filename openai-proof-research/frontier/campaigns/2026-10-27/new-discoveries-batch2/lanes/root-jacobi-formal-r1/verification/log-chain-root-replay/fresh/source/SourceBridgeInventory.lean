import RiccatiScale
import OddPrimitiveSequence
import Lean

set_option autoImplicit false
set_option warningAsError true

open Lean Elab Command in
elab "#source_bridge_inventory" : command => do
  let env ← getEnv
  let proofModules := #[`LiteralFinite, `LiteralMidpoint, `LiteralDifferential,
    `LiteralHankel, `LiteralPotential, `LiteralInverseFactor, `RiccatiScale]
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if proofModules.contains modName then
        logInfo m!"SOURCE_BRIDGE_DECL {name}"
        logInfo m!"SOURCE_BRIDGE_MODULE {name} {modName}"
        logInfo m!"SOURCE_BRIDGE_SAFETY {name} {info.isUnsafe}"

#source_bridge_inventory
