import Endpoint
import Lean
open Lean Elab Command
set_option pp.universes true
set_option pp.fullNames true
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n,c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if ["Defs", "Cover", "Obstruction", "Endpoint"].contains m.toString then
      count := count + 1
      let ax ← Lean.collectAxioms n
      let value := c.value? (allowOpaque := true)
      logInfo m!"DECL|{m}|{n}|unsafe={c.isUnsafe}|partial={c.isPartial}|body={value.isSome}|axioms={ax.toList}\nTYPE|{c.type}"
      if c.isUnsafe || c.isPartial then throwError "unsafe or partial {n}"
      if value.isNone then throwError "missing body {n}"
      for a in ax do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "unexpected axiom {a}"
  logInfo m!"COUNT|{count}"
#print Cover377831.SourceConjecture
#print Cover377831.ContainsSGQPQ
#print axioms Cover377831.source_refutation
