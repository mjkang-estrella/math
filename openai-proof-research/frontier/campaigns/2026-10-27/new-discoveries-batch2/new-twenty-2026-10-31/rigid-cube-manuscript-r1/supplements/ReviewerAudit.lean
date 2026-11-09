import Signed
import Audit
import Inventory
import Safety
import Lean
set_option pp.all true
set_option pp.universes true
open Lean Elab Command in
run_elab do
  let env := (← getEnv).setExporting false
  let mut count := 0
  for (n, c) in env.constants.toList do
    let origin := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
    if origin == some `Cube || origin == some `Signed || origin == some `Audit || origin == some `Inventory || origin == some `Safety then
      count := count + 1
      if c.isUnsafe || c.isPartial then throwError "unsafe/partial {n}"
      match c with
      | .axiomInfo _ => throwError "local axiom {n}"
      | _ => pure ()
      unless (c.value? true).isSome do throwError "missing body {n}"
      let axs ← collectAxioms n
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "forbidden axiom {ax} in {n}"
      logInfo m!"AUDIT {n}\nORIGIN {origin}\nTYPE {c.type}\nBODY true UNSAFE {c.isUnsafe} PARTIAL {c.isPartial}\nAXIOMS {axs}"
  unless count == 33 do throwError "unexpected declaration count {count}"
  logInfo m!"AUDIT_COUNT {count}"
