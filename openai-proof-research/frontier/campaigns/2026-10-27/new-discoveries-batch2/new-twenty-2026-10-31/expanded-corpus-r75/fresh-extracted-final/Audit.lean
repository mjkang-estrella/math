import Magic
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mut count : Nat := 0
 for (n,c) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  if env.header.moduleNames[idx.toNat]! != `Magic then continue
  count := count + 1
  let ax ← Lean.collectAxioms n
  logInfo m!"DECL|{n}|unsafe={c.isUnsafe}|partial={c.isPartial}|body={c.value? (allowOpaque := true) |>.isSome}|axioms={ax.toList}"
  if c.isUnsafe || c.isPartial || (c.value? (allowOpaque := true)).isNone then throwError "invalid declaration {n}"
  for a in ax do
   unless [``propext, ``Classical.choice, ``Quot.sound].contains a do throwError "forbidden axiom {a}"
 logInfo m!"COUNT|{count}"
#print Magic381805.SourceConjecture
#print Magic381805.IsFamily
#print Magic381805.IsSuperEdgeMagic
#print axioms Magic381805.source_refutation
