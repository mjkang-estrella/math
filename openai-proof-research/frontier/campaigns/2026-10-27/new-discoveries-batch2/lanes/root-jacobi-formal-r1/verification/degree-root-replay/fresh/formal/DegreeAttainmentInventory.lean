import LiteralPureCoefficient
import Lean

set_option autoImplicit false
set_option warningAsError true
set_option pp.privateNames true

open Lean Elab Command in
elab "#degree_attainment_inventory" : command => do
  let env ← getEnv
  let proofModules := #[`ParameterDegree, `CatalanTop, `ScaledTop, `PurePrimitive, `LiteralPureCoefficient]
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if proofModules.contains modName then
        logInfo m!"ATTAINMENT_DECL {name}"
        logInfo m!"ATTAINMENT_MODULE {name} {modName}"
        logInfo m!"ATTAINMENT_SAFETY {name} {info.isUnsafe}"
        if info.isUnsafe then
          throwError m!"Unsafe declaration: {name}"

#degree_attainment_inventory
