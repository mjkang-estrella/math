import LiftGraph
import AffineLift
import LiftFibres
import LiftSums
import LiftSections
import LiftIncidence
import LiftEdgeCount
import StrongCycles
import Literal
import Certificates
import Base16Open5
import Base16Open7
import Base16Open9
import Base16Open11
import Base16Closed4
import Base16Closed6
import Base16Closed8
import Base16Closed10
import Base32Open5
import Base32Open7
import Base32Open9
import Base32Open11
import Base32Open13
import Base32Open15
import Base32Open17
import Base32Open19
import Base32Open21
import Base32Open23
import Base32Open25
import Base32Open27
import Base32Closed4
import Base32Closed6
import Base32Closed8
import Base32Closed10
import Base32Closed12
import Base32Closed14
import Base32Closed16
import Base32Closed18
import Base32Closed20
import Base32Closed22
import Base32Closed24
import Base32Closed26
import BaseEndpoints
import Four
import TranslationCardinality
import TranslationFour
import TotalBits
import Complements
import InterpolationArithmetic
import GeneralObstruction
import SeedStructure
import Seed16Closed4
import Seed16Open5
import Seed32Closed4
import Seed32Open5
import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
  let env ← getEnv
  let handle ← IO.FS.Handle.mk "logs/audit-r3-dag.jsonl" .write
  let ids ← IO.mkRef ({} : Std.HashMap Expr Nat)
  let intern := fun e : Expr => do
    let table ← ids.get
    if let some i := table[e]? then return i
    let i := table.size
    ids.set (table.insert e i)
    return i
  let emit := fun j : Json => handle.putStrLn j.compress
  let dump := fun e : Expr => do
    let root ← intern e
    e.forEach fun node => do
      let i ← intern node
      let (tag, fields) ← match node with
        | .app f a => pure ("app", [toJson (← intern f), toJson (← intern a)])
        | .lam n t b bi => pure ("lam", [toJson (reprStr n), toJson (← intern t), toJson (← intern b), toJson (reprStr bi)])
        | .forallE n t b bi => pure ("forallE", [toJson (reprStr n), toJson (← intern t), toJson (← intern b), toJson (reprStr bi)])
        | .letE n t v b nd => pure ("letE", [toJson (reprStr n), toJson (← intern t), toJson (← intern v), toJson (← intern b), toJson nd])
        | .mdata d b => pure ("mdata", [toJson (reprStr d), toJson (← intern b)])
        | .proj n k b => pure ("proj", [toJson (reprStr n), toJson k, toJson (← intern b)])
        | _ => pure ("leaf", [toJson (reprStr node)])
      emit (Json.mkObj [("node",toJson i),("ctor",toJson tag),("fields",toJson fields)])
    return root
  let mut count : Nat := 0
  for (n,c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if (["LiftGraph", "AffineLift", "LiftFibres", "LiftSums", "LiftSections", "LiftIncidence", "LiftEdgeCount", "StrongCycles"] : List String).contains m.toString then
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
