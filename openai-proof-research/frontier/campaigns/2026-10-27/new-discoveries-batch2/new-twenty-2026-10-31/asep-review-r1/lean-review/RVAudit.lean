import ASEPArcs
import PermOrder
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

/-! Reviewer's full declaration audit of the 22 author modules (every constant whose home module is one
of them, including auxiliary/generated constants).  For each: module, kind, safety, body presence,
full type, Lean `collectAxioms` (uses olean-cached data), implemented_by / extern attributes.
Independently: a body-walking traversal over the WHOLE transitive closure of all local constants
(shared visited set, ignoring cached axiom data) that records every axiom reached and any constant
whose body is unavailable.  Output: one JSON object per line on stdout. -/

open Lean Elab Command Meta

def localMods : Array Name := #[`ASEPDefs, `ASEPArcs, `ASEPSound, `ASEPVertex, `ASEPCheck, `ASEPData,
  `ASEPCover, `ASEPCerts0, `ASEPCerts1, `ASEPCerts2, `ASEPCerts3, `ASEPCerts4, `ASEPCerts5, `ASEPCerts6,
  `ASEPCerts7, `ASEPCerts8, `ASEPCerts9, `ASEPCerts10, `ASEPCerts11, `ASEPBridge, `ASEPMain, `PermOrder]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "recursor"

def safetyOf : ConstantInfo → String
  | .defnInfo v => match v.safety with | .unsafe => "unsafe" | .partial => "partial" | .safe => "safe"
  | .opaqueInfo v => if v.isUnsafe then "unsafe" else "safe"
  | ci => if ci.isUnsafe then "unsafe" else "safe"

def bodyOf : ConstantInfo → Option Expr
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

/-- Independent closure walk (no cached axiom data). -/
partial def walk (env : Environment) (todo : Array Name) : NameSet × NameSet × NameSet × Nat := Id.run do
  let mut seen : NameSet := {}; let mut axs : NameSet := {}; let mut missing : NameSet := {}
  let mut noBody : NameSet := {}; let mut st := todo
  while h : st.size > 0 do
    let c := st.back; st := st.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | none => missing := missing.insert c
    | some ci =>
      if let .axiomInfo _ := ci then axs := axs.insert c
      let mut es : Array Expr := #[ci.type]
      match ci with
      | .defnInfo v => es := es.push v.value
      | .thmInfo v => es := es.push v.value
      | .opaqueInfo v => es := es.push v.value
      | .inductInfo v => st := st ++ v.ctors.toArray
      | .ctorInfo v => st := st.push v.induct
      | .recInfo v => st := st.push v.getMajorInduct
      | _ => pure ()
      for e in es do
        for d in e.getUsedConstants do
          if !seen.contains d then st := st.push d
  return (axs, missing, noBody, seen.size)

elab "#rvaudit" : command => do
  let env ← getEnv
  let penv := env.setExporting false
  let mods := env.header.moduleNames
  let locals : Array (Name × Name × ConstantInfo) := penv.constants.map₁.fold (init := #[]) fun acc n ci =>
    match penv.getModuleIdxFor? n with
    | some idx => let m := mods[idx.toNat]!; if localMods.contains m then acc.push (n, m, ci) else acc
    | none => acc
  let locals := locals.qsort (fun a b => Name.lt a.1 b.1)
  let mut union : NameSet := {}
  let mut nbad := 0
  for (n, m, ci) in locals do
    let axs ← collectAxioms n
    for a in axs do union := union.insert a
    let ty ← liftTermElabM do
      withOptions (fun o => (o.set `format.width (100000 : Nat)).set `pp.oneline true) do
        return toString (← ppExpr ci.type)
    let ib := (Compiler.getImplementedBy? penv n).isSome
    let ex := isExtern penv n
    let body := bodyOf ci
    let ok := axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) &&
      safetyOf ci == "safe" && !ib && !ex && kindOf ci != "axiom" && kindOf ci != "opaque"
    if !ok then nbad := nbad + 1
    let j := Json.mkObj [("name", toJson n.toString), ("module", toJson m.toString), ("kind", toJson (kindOf ci)),
      ("safety", toJson (safetyOf ci)), ("value?", toJson body.isSome),
      ("implemented_by", toJson ib), ("extern", toJson ex),
      ("axioms", toJson (axs.map Name.toString)), ("ok", toJson ok), ("type", toJson ty)]
    logInfo m!"RVDECL {j.compress}"
  let (waxs, missing, _, nseen) := walk penv (locals.map (·.1))
  let s := Json.mkObj [("num_local_constants", toJson locals.size), ("num_not_ok", toJson nbad),
    ("collectAxioms_union", toJson (union.toList.map Name.toString)),
    ("walk_closure_size", toJson nseen), ("walk_axioms", toJson (waxs.toList.map Name.toString)),
    ("walk_missing_constants", toJson (missing.toList.map Name.toString))]
  logInfo m!"RVSUMMARY {s.compress}"

#rvaudit
