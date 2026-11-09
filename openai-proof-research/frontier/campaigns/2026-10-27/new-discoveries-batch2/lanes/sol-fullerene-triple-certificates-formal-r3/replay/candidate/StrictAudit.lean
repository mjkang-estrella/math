import Lean.Elab.Command
import Lean.Elab.Print
set_option autoImplicit false
set_option warningAsError true
set_option pp.privateNames true
open Lean Elab Command in
elab "#strict_audit" "[" mods:ident,* "]" : command => do
 let env ← getEnv
 let mut origins : NameSet := {}
 for m in mods.getElems do
  origins := origins.insert m.getId
 let mut todo : Array Name := #[]
 let mut owned : Array Name := #[]
 for (name, info) in env.constants do
  if let some idx := env.getModuleIdxFor? name then
   let modName := env.header.moduleNames[idx.toNat]!
   if origins.contains modName then
    logInfo m!"OWN_DECL {name}"
    logInfo m!"OWN_MODULE {name} {modName}"
    logInfo m!"OWN_SAFETY {name} {info.isUnsafe}"
    logInfo m!"OWN_PARTIAL {name} {info.isPartial}"
    if info.isPartial || info.isUnsafe then throwError m!"REJECTED origin {name}"
    owned := owned.push name
    todo := todo.push name
 for modName in origins do
  if !env.header.moduleNames.contains modName then throwError m!"REJECTED missing origin {modName}"
  logInfo m!"AUDITED_ORIGIN {modName}"
 let mut seen : NameSet := {}
 while !todo.isEmpty do
  let name := todo.back!
  todo := todo.pop
  if !seen.contains name then
   seen := seen.insert name
   let some info := env.find? name | throwError m!"REJECTED absent constant {name}"
   if info.isPartial || info.isUnsafe then throwError m!"REJECTED transitive type/body dependency {name}"
   todo := todo ++ info.type.getUsedConstants
   if let some v := info.value? then todo := todo ++ v.getUsedConstants
 logInfo m!"TRANSITIVE_SAFE_COUNT {seen.size}"
 for name in owned do
  elabCommand (← `(command| #check $(mkIdent name)))
  elabCommand (← `(command| #print axioms $(mkIdent name)))
