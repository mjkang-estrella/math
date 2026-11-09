import OrderedFull
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
 let env ← getEnv
 let mut count : Nat := 0
 for (n, ci) in env.constants.toList do
  if n.toString.startsWith "OrderedCounterexample" then
   let axs ← Lean.collectAxioms n
   for ax in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
     throwError "Forbidden axiom {ax} in {n}"
   if ci.isUnsafe then throwError "Unsafe declaration {n}"
   logInfo m!"AUDIT {n} : {axs}"
   count := count + 1
 logInfo m!"AUDITED {count} declarations"
#print OrderedCounterexample.full_source_conjecture_false
#print OrderedCounterexample.E_exists
