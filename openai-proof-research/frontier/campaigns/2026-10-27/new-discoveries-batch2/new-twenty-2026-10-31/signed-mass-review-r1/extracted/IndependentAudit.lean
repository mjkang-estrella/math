import SignedMass
import Lean.Util.CollectAxioms
open Lean Elab Command in
set_option pp.all true in
run_cmd do
 let env ← getEnv
 let mut count := 0
 for (n,c) in env.constants.toList do
  let origin := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
  if origin == some `SignedMass then
   count := count + 1
   let axs ← collectAxioms n
   unless axs.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
    throwError m!"Forbidden axioms {n}: {axs}"
   if c.isUnsafe || c.isPartial || (c.value? true).isNone then
    throwError m!"Unsafe, partial or missing body: {n}"
   logInfo m!"DECL {n} ORIGIN {origin} BODY {(c.value? true).isSome} UNSAFE {c.isUnsafe} PARTIAL {c.isPartial} AXIOMS {axs} TYPE {c.type}"
 logInfo m!"TOTAL {count}"
#print axioms MathDB368007.source_refutation
