import Magic
import Lean
set_option pp.all true
set_option pp.universes true
set_option pp.explicit true
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
  logInfo m!"FULL_TYPE|{n}|{c.type}"
  if c.isUnsafe || c.isPartial || (c.value? (allowOpaque := true)).isNone then throwError "invalid declaration {n}"
  for a in ax do
   unless [``propext, ``Classical.choice, ``Quot.sound].contains a do throwError "forbidden axiom {a}"
 unless count == 37 do throwError "unexpected declaration count {count}"
 logInfo m!"COUNT|{count}"
#print axioms Magic381805.source_refutation
#print axioms Magic381805.strength_le
