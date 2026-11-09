import audit.IndependentMetadata
import CMDRRAuditFinal
import CMDRRAuditR3
import CMDRRSignAPI
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.CSimpAttr
open Lean Elab Command

namespace IndependentMetadataClosure

def kind : ConstantInfo → String
 | .axiomInfo _ => "axiom"
 | .defnInfo _ => "definition"
 | .thmInfo _ => "theorem"
 | .opaqueInfo _ => "opaque"
 | .inductInfo _ => "inductive"
 | .ctorInfo _ => "constructor"
 | .recInfo _ => "recursor"
 | .quotInfo _ => "quotient"

def structural (ci : ConstantInfo) : Array Name :=
 match ci with
 | .inductInfo v => v.all.toArray ++ v.ctors.toArray
 | .ctorInfo v => #[v.induct]
 | .recInfo v => v.all.toArray ++ v.rules.toArray.flatMap (fun r => #[r.ctor] ++ r.rhs.getUsedConstants)
 | _ => #[]

def jnames (ns : Array Name) : Json := toJson (ns.map Name.toString)

elab "independent_metadata_closure" : command => do
 let env ← getEnv
 let aux := #["CMDRRControls", "CMDRRAuditR3", "CMDRRAuditFinal", "CMDRRSignAPI"]
 let origin := fun n => ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).map Name.toString
 let mut prod : Array Name := #[]
 let mut tools : Array Name := #[]
 for (n, _) in env.constants.toList do
  if let some m := origin n then
   if m.startsWith "CMDRR" || m == "audit.IndependentMetadata" then
    if aux.contains m || m == "audit.IndependentMetadata" then tools := tools.push n else prod := prod.push n
 logInfo m!"ROOTS {Json.compress (Json.mkObj [("production", jnames prod), ("auxiliary", jnames tools)])}"
 for scope in #[("production", prod), ("auxiliary", tools)] do
  let mut todo := scope.2
  let mut seen : NameSet := {}
  while !todo.isEmpty do
   let n := todo.back!
   todo := todo.pop
   unless seen.contains n do
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing {n}"
    let own := (origin n).any (·.startsWith "CMDRR")
    let body := ci.value? (allowOpaque := true)
    let ext := isExtern env n
    let imp := Compiler.getImplementedBy? env n
    let cs := (Compiler.CSimp.ext.getState env).map.find? n
    let deps := ci.type.getUsedConstants ++ body.toArray.flatMap Expr.getUsedConstants ++ structural ci
    if ci.isAxiom && !#[``propext, ``Classical.choice, ``Quot.sound].contains n then
     throwError "Forbidden axiom {n}"
    if scope.1 == "production" && (ci.isUnsafe || ci.isPartial) then
     throwError "Unsafe/partial kernel dependency {n}"
    if own && scope.1 == "production" && (ext || imp.isSome || cs.isSome) then
     throwError "Production code replacement {n}"
    match ci with
    | .quotInfo _ =>
      unless #[`Quot, `Quot.mk, `Quot.lift, `Quot.ind].contains n do
       throwError "Unexpected quotient primitive {n}"
    | .ctorInfo v =>
      let some (.inductInfo iv) := env.find? v.induct | throwError "Constructor parent {n}"
      unless iv.ctors.contains n do throwError "Constructor not in parent {n}"
    | .recInfo v =>
      for a in v.all do
       unless (env.find? a).any ConstantInfo.isInductive do throwError "Recursor parent {n}"
      for r in v.rules do
       unless (env.find? r.ctor).any ConstantInfo.isCtor do throwError "Recursor constructor {n}"
    | .inductInfo v =>
      for c in v.ctors do
       let some (.ctorInfo cv) := env.find? c | throwError "Inductive constructor {n}"
       unless cv.induct == n do throwError "Inductive parent mismatch {n}"
    | .axiomInfo _ => pure ()
    | _ => unless body.isSome do throwError "Missing checked body {n}"
    let j := Json.mkObj [
     ("scope", toJson scope.1), ("name", toJson n.toString),
     ("origin", toJson (origin n)), ("kind", toJson (kind ci)),
     ("has_body", toJson body.isSome), ("unsafe", toJson ci.isUnsafe),
     ("partial", toJson ci.isPartial), ("extern", toJson ext),
     ("implementedBy", toJson (imp.map Name.toString)),
     ("csimp", toJson (cs.map fun e => e.toDeclName.toString)),
     ("csimpTheorem", toJson (cs.map fun e => e.thmName.toString)),
     ("deps", jnames deps)]
    logInfo m!"NODE {j.compress}"
    todo := todo ++ deps
  logInfo m!"DONE {scope.1} {seen.size}"

end IndependentMetadataClosure
independent_metadata_closure

