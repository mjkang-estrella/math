import Lean
import Magic
set_option warningAsError true
open Magic381805
axiom cheat : SourceConjecture
theorem uses_cheat : SourceConjecture := cheat
open Lean Elab Command in
run_cmd do
 let axs ← Lean.collectAxioms `uses_cheat
 for ax in axs do
  unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
   throwError "forbidden axiom {ax}"
