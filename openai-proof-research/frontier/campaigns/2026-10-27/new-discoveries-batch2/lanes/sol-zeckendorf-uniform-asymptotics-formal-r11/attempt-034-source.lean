import UniformSuffix
import Lean
set_option autoImplicit false
set_option pp.privateNames true
set_option linter.auxLemma false
open Lean Elab Command in
elab "#root_axiom_audit" : command => do
 let env ← getEnv
 for idx in [:env.header.moduleData.size] do
  if ([`Literal, `Terminal, `Law, `Cells, `Product, `Prefix, `Marks, `Boards, `Injection, `Abundance, `Tail, `Concentration, `Assembly, `SuffixUnion, `LastSplit, `Growth, `Uniform, `UniformSuffix].contains env.header.moduleNames[idx]!) then
   for name in env.header.moduleData[idx]!.constNames do
    elabCommand (← `(command| #check $(mkIdent name)))
    elabCommand (← `(command| #print axioms $(mkIdent name)))
#root_axiom_audit
