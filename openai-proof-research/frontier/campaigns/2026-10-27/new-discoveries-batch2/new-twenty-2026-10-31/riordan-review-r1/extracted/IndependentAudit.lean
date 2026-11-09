import Endpoint
import Lean
open Lean Elab Command
run_cmd do
 let e ← getEnv
 let mut total : Nat := 0
 for (n,c) in e.constants.toList do
  let some idx := e.getModuleIdxFor? n | continue
  let moduleName := e.header.moduleNames[idx.toNat]!.toString
  if moduleName == "Core" || moduleName == "Endpoint" || moduleName == "Table" || moduleName.startsWith "Row" then
   total := total + 1
   let partialFlag := match c with | .defnInfo v => v.safety == .partial | _ => false
   let impl := (Lean.Compiler.implementedByAttr.getParam? e n).isSome
   let ext := Lean.isExtern e n
   let ax ← Lean.collectAxioms n
   logInfo m!"DECL|{moduleName}|{n}|unsafe={c.isUnsafe}|partial={partialFlag}|implemented_by={impl}|extern={ext}|axioms={ax.toList}"
   if c.isUnsafe || partialFlag || impl || ext || n.toString.endsWith "_unsafe_rec" then throwError "rejected declaration {n}"
   if c.value? true |>.isNone then throwError "declaration has no body {n}"
   for a in ax do
    if !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a then throwError "disallowed axiom {a}"
 logInfo m!"TOTAL={total}"
#print Riordan.SourceConjecture
#print Riordan.source_conjecture_false
#print axioms Riordan.source_conjecture_false
