import LastSplit
import Lean
set_option autoImplicit false
set_option pp.privateNames true
set_option linter.auxLemma false
open Lean Elab Command in
elab "#root_axiom_audit" : command => do
 let env ← getEnv
 for (name, _) in env.constants do
  if let some idx := env.getModuleIdxFor? name then
   if ([`Literal, `Terminal, `Law, `Cells, `Product, `Prefix, `Marks, `Boards, `Injection, `Abundance, `Tail, `Concentration, `Assembly, `LastSplit].contains env.header.moduleNames[idx.toNat]!) then
    elabCommand (← `(command| #check $(mkIdent name)))
    elabCommand (← `(command| #print axioms $(mkIdent name)))
#root_axiom_audit
