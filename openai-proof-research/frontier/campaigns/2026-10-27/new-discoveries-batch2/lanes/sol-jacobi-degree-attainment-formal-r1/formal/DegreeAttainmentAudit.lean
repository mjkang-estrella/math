import LiteralPureCoefficient
import Lean

set_option autoImplicit false
set_option warningAsError true
set_option linter.auxLemma false
set_option pp.privateNames true

open Lean Elab Command in
elab "#degree_attainment_check_all" : command => do
  let env ← getEnv
  let proofModules := #[`ParameterDegree, `CatalanTop, `ScaledTop, `PurePrimitive, `LiteralPureCoefficient]
  for (name, _) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if proofModules.contains modName then
        elabCommand (← `(#check $(mkIdent name)))
        elabCommand (← `(#print axioms $(mkIdent name)))

#degree_attainment_check_all
