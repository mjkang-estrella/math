import SplitMatching
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mut n : Nat := 0
 for (name, ci) in env.constants.toList do
  if (env.getModuleIdxFor? name).any (fun idx => env.header.moduleNames[idx.toNat]! == `SplitMatching) then
   n := n+1
   let ax ← Lean.collectAxioms name
   let bad := ax.filter fun a => !(#[`propext,`Classical.choice,`Quot.sound].contains a)
   if !bad.isEmpty then throwError "Forbidden axioms in {name}: {bad}"
   if ci.isPartial then throwError "Partial: {name}"
   if ci.isAxiom then throwError "New axiom: {name}"
   if ci.isUnsafe then throwError "Unsafe: {name}"
   logInfo m!"AUDIT {name} axioms={ax} unsafe={ci.isUnsafe}"
 logInfo m!"AUDITED_DECLARATIONS {n}"
