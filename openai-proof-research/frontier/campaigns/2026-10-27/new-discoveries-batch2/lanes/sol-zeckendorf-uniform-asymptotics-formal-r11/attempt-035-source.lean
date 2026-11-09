import Lean
set_option autoImplicit false
set_option linter.auxLemma false
open Lean Elab Command in
elab "#literal_inventory" : command => do
 let env ← getEnv
 let mut todo : Array Name := #[]
 for idx in [:env.header.moduleData.size] do
     let modName := env.header.moduleNames[idx]!
     if (modName == `Literal || modName == `Terminal || modName == `Law || modName == `Cells || modName == `Product || modName == `Prefix || modName == `Marks || modName == `Boards || modName == `Injection || modName == `Abundance || modName == `Tail || modName == `Concentration || modName == `Assembly || modName == `LastSplit || modName == `SuffixUnion || modName == `Growth || modName == `Uniform || modName == `UniformSuffix) then
       for name in env.header.moduleData[idx]!.constNames do
         let some info := env.find? name | throwError m!"Missing origin {name}"
         logInfo m!"OWN_DECL {name}"
         logInfo m!"OWN_MODULE {name} {modName}"
         logInfo m!"OWN_SAFETY {name} {info.isUnsafe}"
         let partialFlag : Bool := match info with
           | .defnInfo v => v.safety == .partial
           | _ => false
         logInfo m!"OWN_PARTIAL {name} {partialFlag}"
         if partialFlag then throwError m!"REJECTED_ORIGIN_PARTIAL {name}"
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
       match info with
       | .defnInfo v =>
         if v.safety == .partial then throwError m!"REJECTED_TRANSITIVE_PARTIAL {name}"
       | _ => pure ()
       if let .axiomInfo _ := info then
         unless name == `propext || name == `Classical.choice || name == `Quot.sound do
           throwError m!"REJECTED_AXIOM {name}"
       todo := todo ++ info.type.getUsedConstants
       if let some v := info.value? then
         todo := todo ++ v.getUsedConstants
 logInfo m!"TRANSITIVE_SAFE_COUNT {seen.size}"
open Lean Elab Command in
elab "#root_axiom_audit" : command => do
 let env ← getEnv
 for idx in [:env.header.moduleData.size] do
  if ([`Literal, `Terminal, `Law, `Cells, `Product, `Prefix, `Marks, `Boards, `Injection, `Abundance, `Tail, `Concentration, `Assembly, `SuffixUnion, `LastSplit, `Growth, `Uniform, `UniformSuffix].contains env.header.moduleNames[idx]!) then
   for name in env.header.moduleData[idx]!.constNames do
    elabCommand (← `(command| #check $(mkIdent name)))
    elabCommand (← `(command| #print axioms $(mkIdent name)))
