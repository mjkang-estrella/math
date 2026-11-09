import EndpointStrong
import Lean
open Lean Elab Command
run_cmd do
 let e ← getEnv
 let localModules : List String := ["Core", "Table", "Endpoint", "InfiniteFamily", "EndpointStrong"] ++ (List.range 15).map (fun i => s!"Row{i}")
 let mut seeds : Array Name := #[]
 let mut modules : Std.HashSet String := {}
 for (n,c) in e.constants.toList do
  let some idx := e.getModuleIdxFor? n | continue
  let m := e.header.moduleNames[idx.toNat]!.toString
  if localModules.contains m then
   modules := modules.insert m
   seeds := seeds.push n
   let ax ← Lean.collectAxioms n
   logInfo m!"LOCAL|{m}|{n}|axioms={ax.toList}"
   if c.value? true |>.isNone then throwError "local declaration lacks body {n}"
 for m in localModules do
  unless modules.contains m do throwError "missing closure module {m}"
 let deps := fun (c : ConstantInfo) => c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
 let mut work := seeds
 let mut seen : Std.HashSet Name := {}
 let mut externTotal : Nat := 0
 let mut implementedTotal : Nat := 0
 let mut allowedAxioms : Std.HashSet Name := {}
 while !work.isEmpty do
  let n := work.back!
  work := work.pop
  if seen.contains n then continue
  seen := seen.insert n
  let some c := e.find? n | throwError "missing declaration {n}"
  let partialFlag := match c with | .defnInfo v => v.safety == .partial | _ => false
  let impl := (Lean.Compiler.implementedByAttr.getParam? e n).isSome
  let ext := Lean.isExtern e n
  logInfo m!"DECL|{n}|unsafe={c.isUnsafe}|partial={partialFlag}|implemented_by={impl}|extern={ext}"
  if ext then externTotal := externTotal + 1
  if impl then implementedTotal := implementedTotal + 1
  if c.isUnsafe || partialFlag || n.toString.endsWith "_unsafe_rec" then throwError "rejected declaration {n}"
  if seeds.contains n && (impl || ext) then throwError "local runtime replacement {n}"
  match c with
  | .axiomInfo _ =>
    unless ([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains n do throwError "disallowed axiom {n}"
    allowedAxioms := allowedAxioms.insert n
  | _ => pure ()
  work := work ++ deps c
 -- Fixed point check: the reported audited set contains every seed and every
 -- dependency edge, and traversal inserted only seeds or their dependencies.
 for n in seeds do
  unless seen.contains n do throwError "unaudited seed {n}"
 for n in seen.toArray do
  let some c := e.find? n | throwError "missing audited declaration {n}"
  for d in deps c do
   unless seen.contains d do throwError "closure escapes to {d}"
 logInfo m!"LOCAL_TOTAL={seeds.size}"
 logInfo m!"DEPENDENCY_TOTAL={seen.size}"
 logInfo m!"UPSTREAM_EXTERN={externTotal}|UPSTREAM_IMPLEMENTED_BY={implementedTotal}"
 logInfo m!"AXIOMS={allowedAxioms.toArray}"
 logInfo "CLOSURE_EQUALITY=true"
#print Riordan.SourceConjectureInfiniteFamily
#print axioms Riordan.source_conjecture_false
#print axioms Riordan.source_conjecture_false_infinite_family
