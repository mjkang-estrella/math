import LogRiccatiIdentification
import OddPrimitiveSequence
import Lean

set_option autoImplicit false
set_option warningAsError true
-- Compiler auxiliaries are intentionally included in the exhaustive audit.
set_option linter.auxLemma false
set_option pp.privateNames true

open Lean Elab Command in
elab "#log_chain_check_all" : command => do
  let env ← getEnv
  let proofModules := #[`FiniteLogChain, `LiteralLogRiccati, `LogRiccatiIdentification]
  for (name, _) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if proofModules.contains modName then
        elabCommand (← `(#check $(mkIdent name)))
        elabCommand (← `(#print axioms $(mkIdent name)))

#log_chain_check_all
