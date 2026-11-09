import SourceContact
import GraphResolvent
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option pp.all true
set_option maxRecDepth 8192
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if mod == `SourceContact || mod == `QuadraticBranches || mod == `ExactOrders || mod == `SecondBranch || mod == `BranchBounds || mod == `HalfPlane || mod == `GraphResolvent || mod == `Audit || mod == `AuditR2 then
      count := count + 1
      let axs ← collectAxioms name
      logInfo m!"DECL {name}\nMODULE {mod}\nTYPE {repr ci.type}\nBODY {repr (ci.value? (allowOpaque := true))}\nUNSAFE {ci.isUnsafe}\nPARTIAL {ci.isPartial}\nAXIOMS {axs}"
      if ci.isUnsafe || ci.isPartial then throwError "unsafe or partial declaration {name}"
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "unapproved axiom {ax} in {name}"
  logInfo m!"TOTAL_LOCAL_DECLARATIONS {count}"
