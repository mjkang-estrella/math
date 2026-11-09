import OrdinalLine
set_option warningAsError true
axiom cheat : OrdinalSpaces366371.MajorizationConjecture
theorem uses_cheat : OrdinalSpaces366371.MajorizationConjecture := cheat
open Lean Elab Command in
run_cmd do
 let axs ← Lean.collectAxioms `uses_cheat
 for ax in axs do
  unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
   throwError "forbidden axiom {ax}"
