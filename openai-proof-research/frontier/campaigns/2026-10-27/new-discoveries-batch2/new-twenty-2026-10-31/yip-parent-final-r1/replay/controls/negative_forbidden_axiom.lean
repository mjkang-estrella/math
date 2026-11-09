import Yip355956
set_option warningAsError true
axiom cheat : MathDB355956.YipConjecture
theorem uses_cheat : MathDB355956.YipConjecture := cheat
open Lean Elab Command in
run_cmd do
 let axs ← Lean.collectAxioms `uses_cheat
 for ax in axs do
  unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
   throwError "forbidden axiom {ax}"
