import Geometry
import Lean
set_option autoImplicit false
set_option warningAsError true
set_option pp.privateNames true
open Lean Elab Command in
elab "#literal_inventory" : command => do
 let env ← getEnv
 let mut todo : Array Name := #[]
 for (name, info) in env.constants do
   if let some idx := env.getModuleIdxFor? name then
     let modName := env.header.moduleNames[idx.toNat]!
     if modName ∈ [`Geometry] then
       logInfo m!"OWN_DECL {name}"
       logInfo m!"OWN_MODULE {name} {modName}"
       logInfo m!"OWN_SAFETY {name} {info.isUnsafe}"
       if info.isUnsafe then throwError m!"Rejected declaration {name}"
       todo := todo.push name
 let mut seen : NameSet := {}
 while !todo.isEmpty do
   let name := todo.back!
   todo := todo.pop
   if !seen.contains name then
     seen := seen.insert name
     if let some info := env.find? name then
       if info.isUnsafe then throwError m!"Rejected transitive dependency {name}"
       todo := todo ++ info.type.getUsedConstants
       if let some v := info.value? then
         todo := todo ++ v.getUsedConstants
 logInfo m!"TRANSITIVE_SAFE_COUNT {seen.size}"
#literal_inventory
