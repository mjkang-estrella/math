import Lean

/-!
# Declaration audit tooling for the MathDB 368807 dossier

Not a proof module.  `ASEPAudit.declReport` describes one constant; `ASEPAudit.closure` walks the
transitive dependency closure of a set of constants through types and bodies directly (it does not
use the axiom data that `collectAxioms` caches in the oleans).  `#assert_std_axioms c` fails unless
both methods find only `propext`, `Classical.choice` and `Quot.sound` below `c`.
-/

open Lean Elab Command Meta

namespace ASEPAudit

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Constants that must never occur in an accepted closure. -/
def forbiddenConsts : List Name :=
  [`sorryAx, `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "recursor"

/-- Compiler-generated helper produced for recursive definitions (`foo._unsafe_rec`). -/
def isUnsafeRecName : Name → Bool
  | .str _ "_unsafe_rec" => true
  | _ => false

/-- Result of an uncached closure walk. -/
structure Closure where
  seen : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}
  unsafeConsts : NameSet := {}
  partialConsts : NameSet := {}
  unsafeRec : NameSet := {}
  forbidden : NameSet := {}

def closure (env : Environment) (roots : Array Name) : Closure := Id.run do
  let mut st : Closure := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if st.seen.contains c then continue
    st := { st with seen := st.seen.insert c }
    if isUnsafeRecName c then st := { st with unsafeRec := st.unsafeRec.insert c }
    if forbiddenConsts.contains c then st := { st with forbidden := st.forbidden.insert c }
    match env.find? c with
    | none => st := { st with missing := st.missing.insert c }
    | some ci =>
      if ci.isUnsafe then st := { st with unsafeConsts := st.unsafeConsts.insert c }
      if ci.isPartial then st := { st with partialConsts := st.partialConsts.insert c }
      let mut es : Array Expr := #[ci.type]
      match ci with
      | .axiomInfo _ => st := { st with axioms := st.axioms.insert c }
      | .defnInfo v => es := es.push v.value
      | .thmInfo v => es := es.push v.value
      | .opaqueInfo v => es := es.push v.value
      | .inductInfo v => todo := todo ++ v.ctors.toArray ++ v.all.toArray
      | .ctorInfo v => todo := todo.push v.induct
      | .recInfo v => todo := todo ++ v.all.toArray
      | .quotInfo _ => pure ()
      for e in es do
        for d in e.getUsedConstants do
          unless st.seen.contains d do todo := todo.push d
  return st

def names (s : NameSet) : List String := (s.toList.map Name.toString).mergeSort

def nonStd (s : NameSet) : List Name := s.toList.filter (fun a => !allowedAxioms.contains a)

/-- One JSON record per declaration. -/
def declReport (env : Environment) (n : Name) (m : Name) (ci : ConstantInfo) : MetaM (Json × Bool) := do
  let axs ← collectAxioms n
  let ty ← withOptions (fun o => (o.set `format.width (1000000 : Nat)).set `pp.oneline true) do
    return toString (← ppExpr ci.type)
  let ib := (Compiler.getImplementedBy? env n).isSome
  let ex := isExtern env n
  let v := ci.value?
  let vOpaque := ci.value? (allowOpaque := true)
  let isDefOrThm := match ci with | .defnInfo _ | .thmInfo _ => true | _ => false
  let unsafeRec := isUnsafeRecName n
  let axOk := axs.all (fun a => allowedAxioms.contains a)
  -- a declaration is clean when it is safe, non-partial, has a body (`value? (allowOpaque := true)`)
  -- if it is a def/theorem,
  -- carries no implemented_by/extern attribute, is not an axiom/opaque and uses standard axioms.
  -- `_unsafe_rec` helpers are reported separately (they are compiler output, never kernel-usable).
  let clean := !ci.isUnsafe && !ci.isPartial && (!isDefOrThm || vOpaque.isSome) && !ib && !ex &&
    kindOf ci != "axiom" && kindOf ci != "opaque" && axOk
  let j := Json.mkObj [
    ("name", toJson n.toString), ("module", toJson m.toString), ("kind", toJson (kindOf ci)),
    ("type", toJson ty), ("type_expr_hash", toJson ci.type.hash.toNat),
    ("value?", toJson v.isSome), ("value?_allowOpaque", toJson vOpaque.isSome),
    ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
    ("unsafe_rec_helper", toJson unsafeRec), ("implemented_by", toJson ib), ("extern", toJson ex),
    ("collectAxioms", toJson (axs.toList.map Name.toString)), ("clean", toJson clean)]
  return (j, clean)

/-- `#assert_std_axioms c`: both axiom computations must give a subset of the three standard axioms,
and the closure must contain no `sorryAx`, `ofReduceBool`, `ofReduceNat`, unsafe or partial constant. -/
elab "#assert_std_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env := (← getEnv).setExporting false
  let axs ← liftCoreM <| collectAxioms n
  let cl := closure env #[n]
  let bad1 := axs.toList.filter (fun a => !allowedAxioms.contains a)
  let bad2 := nonStd cl.axioms
  unless bad1.isEmpty && bad2.isEmpty && cl.forbidden.isEmpty && cl.unsafeConsts.isEmpty &&
      cl.partialConsts.isEmpty && cl.missing.isEmpty do
    throwError "ASEPAUDIT FAIL {n}: nonstandard axioms {bad1} / {bad2}, forbidden {names cl.forbidden}, unsafe {names cl.unsafeConsts}, partial {names cl.partialConsts}, missing {names cl.missing}"
  logInfo m!"ASEPAUDIT OK {n}: {axs}"

end ASEPAudit
