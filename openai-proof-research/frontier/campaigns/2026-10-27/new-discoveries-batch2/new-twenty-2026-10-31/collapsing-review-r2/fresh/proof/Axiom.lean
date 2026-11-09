import MathDB378395
set_option warningAsError true
axiom cheat : False
open Lean Elab Command in
run_cmd do
 let axs ← Lean.collectAxioms `cheat
 for ax in axs do
  unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
   throwError "forbidden {ax}"
