import LiftWalks
import Literal
import MainRanges
import RelabelFactors
import RelabelMagic
import Seed16Closed4
import Seed16Open5
import Seed32Closed4
import Seed32Open5
import SeedIntervals
import SeedIteration
import SeedRecursion
import SeedStructure
import SeedWalkBridge
import StrongCycles
import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
  let env ← getEnv
  let handle ← IO.FS.Handle.mk "logs/audit-all-5-dag.jsonl" .write
  let ids ← IO.mkRef ({} : Std.HashMap ExprStructEq Nat)
  let intern := fun e : Expr => do
    let table ← ids.get
    if let some i := table[ExprStructEq.mk e]? then return i
    let i := table.size
    ids.set (table.insert (ExprStructEq.mk e) i)
    return i
  let emit := fun j : Json => handle.putStrLn j.compress
  let done ← IO.mkRef ({} : Std.HashSet Nat)
  let rec visit (node : Expr) : IO Unit := do
      let i ← intern node
      if (← done.get).contains i then return
      done.modify (fun st => st.insert i)
      let (tag, fields) ← match node with
        | .app f a => pure ("app", [toJson (← intern f), toJson (← intern a)])
        | .lam n t b bi => pure ("lam", [toJson (reprStr n), toJson (← intern t), toJson (← intern b), toJson (reprStr bi)])
        | .forallE n t b bi => pure ("forallE", [toJson (reprStr n), toJson (← intern t), toJson (← intern b), toJson (reprStr bi)])
        | .letE n t v b nd => pure ("letE", [toJson (reprStr n), toJson (← intern t), toJson (← intern v), toJson (← intern b), toJson nd])
        | .mdata d b => pure ("mdata", [toJson (reprStr d), toJson (← intern b)])
        | .proj n k b => pure ("proj", [toJson (reprStr n), toJson k, toJson (← intern b)])
        | _ => pure ("leaf", [toJson (reprStr node)])
      emit (Json.mkObj [("node",toJson i),("ctor",toJson tag),("fields",toJson fields)])
      match node with
      | .app f a => visit f; visit a
      | .lam _ t b _ => visit t; visit b
      | .forallE _ t b _ => visit t; visit b
      | .letE _ t v b _ => visit t; visit v; visit b
      | .mdata _ b => visit b
      | .proj _ _ b => visit b
      | _ => pure ()
  let dump := fun e : Expr => do
    let root ← intern e
    visit e
    return root
  let mut count : Nat := 0
  for (n,c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if (["LiftWalks", "Literal", "MainRanges", "RelabelFactors", "RelabelMagic", "Seed16Closed4", "Seed16Open5", "Seed32Closed4", "Seed32Open5", "SeedIntervals", "SeedIteration", "SeedRecursion", "SeedStructure", "SeedWalkBridge", "StrongCycles"] : List String).contains m.toString then
      count := count + 1
      let ax ← Lean.collectAxioms n
      logInfo m!"DECL|{n}|MODULE|{m}|UNSAFE|{c.isUnsafe}|PARTIAL|{c.isPartial}|AXIOMS|{ax.toList}"
      let ty ← dump c.type
      let body ← match c.value? true with
        | some v => pure (some (← dump v))
        | none => pure none
      emit (Json.mkObj [("declaration",toJson n.toString),("module",toJson m.toString),("full_type_root",toJson ty),("full_body_value_true_root",toJson body)])
      if c.isUnsafe || c.isPartial then throwError "bad safety {n}"
      match c with
      | .axiomInfo _ => throwError "local axiom {n}"
      | _ => pure ()
      match c with
      | .inductInfo _ => logInfo m!"KERNEL_DECL_KIND|inductive|{n}"
      | .ctorInfo _ => logInfo m!"KERNEL_DECL_KIND|constructor|{n}"
      | .recInfo _ => logInfo m!"KERNEL_DECL_KIND|recursor|{n}"
      | _ => if !(c.value? true).isSome then throwError "missing body {n}"
      for x in ax do
        if !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains x then
          throwError "disallowed axiom {x} in {n}"
  handle.flush
  logInfo m!"AUDITED_LOCAL_DECLARATIONS|{count}"
