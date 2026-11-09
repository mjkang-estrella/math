import Hierarchy
set_option pp.all true
set_option pp.universes true
set_option pp.fullNames true
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let some idx := env.getModuleIdxFor? `Supervenience.literal_conjecture_false | throwError "missing module"
 let mut count : Nat := 0
 for (n, ci) in env.constants.toList do
  if env.getModuleIdxFor? n == some idx then
   count := count + 1
   let axs ← collectAxioms n
   let body := (ci.value? (allowOpaque := true)).isSome
   logInfo m!"DECL {n}\nMODULE_INDEX {idx}\nTYPE {ci.type}\nVALUE_PRESENT {body}\nUNSAFE {ci.isUnsafe}\nAXIOM {ci.isAxiom}\nAXIOMS {axs.toList}"
   if ci.isUnsafe || ci.isAxiom then throwError "bad declaration {n}"
   match ci with
   | .defnInfo v =>
     if v.safety != .safe then throwError "partial/unsafe definition {n}"
     unless body do throwError "missing definition body {n}"
   | .thmInfo _ => unless body do throwError "missing theorem body {n}"
   | _ => pure ()
   for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do throwError "bad axiom {ax}"
 logInfo m!"TOTAL {count}"
 unless count == 101 do throwError "unexpected declaration count {count}"
#print Supervenience.eval
#print Supervenience.translate
#print Supervenience.StrictStep
#print Supervenience.HierarchyConjecture
#print axioms Supervenience.literal_conjecture_false
