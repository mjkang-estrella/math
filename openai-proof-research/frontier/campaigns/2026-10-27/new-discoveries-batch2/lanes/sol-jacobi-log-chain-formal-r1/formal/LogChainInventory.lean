import LogRiccatiIdentification
import OddPrimitiveSequence
import Lean

set_option autoImplicit false
set_option warningAsError true

open Lean Elab Command in
elab "#log_chain_inventory" : command => do
  let env ← getEnv
  let proofModules := #[`FiniteLogChain, `LiteralLogRiccati, `LogRiccatiIdentification]
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if proofModules.contains modName then
        logInfo m!"LOG_CHAIN_DECL {name}"
        logInfo m!"LOG_CHAIN_MODULE {name} {modName}"
        logInfo m!"LOG_CHAIN_SAFETY {name} {info.isUnsafe}"

#log_chain_inventory
