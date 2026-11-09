/-
Machine-readable environment audit (R2) for the MathDB 352972 certificate.

Enumerates EVERY declaration of the production modules `FlatBalance` and
`FlatBalanceBridges` directly from the elaborated environment, including
private, generated, structure-constructor, recursor and auxiliary
declarations, and reports for each: kind, definition safety, origin module,
the full type, the full value body when present, and the complete
transitive axiom closure. Also reports the union of axioms over all new
declarations, an explicit unsafe/partial/opaque scan, and the transitive
constant closure of both refutation endpoints.

This file only inspects the environment and prints; it proves nothing.
Pins: Lean v4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

import FlatBalanceBridges

open Lean Elab Command

private def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def safetyOf (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo v =>
    if v.safety == .unsafe then "unsafe"
    else if v.safety == .partial then "partial"
    else "safe"
  | .opaqueInfo _ => "opaque"
  | _ => "safe"

private def usedConsts (e : Expr) : Array Name :=
  e.foldConsts #[] fun c acc => acc.push c

private partial def closureAux (env : Environment) (frontier : List Name)
    (seen : Std.HashSet Name) (axs : Array Name) : Std.HashSet Name × Array Name :=
  match frontier with
  | [] => (seen, axs)
  | e :: rest =>
    if seen.contains e then closureAux env rest seen axs
    else
      let seen := seen.insert e
      match env.find? e with
      | none => closureAux env rest seen axs
      | some ci =>
        let direct := usedConsts ci.type ++ (match ci.value? with | some v => usedConsts v | none => #[])
        let axs := match ci with
          | .axiomInfo _ => if axs.contains e then axs else axs.push e
          | _ => axs
        closureAux env (rest ++ direct.toList) seen axs

run_cmd do
  liftTermElabM do
    let env ← getEnv
    let nMods := env.header.moduleData.size
    let mut targetIdx : Option Nat := none
    let mut bridgeIdx : Option Nat := none
    for i in [0:nMods] do
      let mn := env.header.moduleNames[i]!
      if mn == `FlatBalance then targetIdx := some i
      if mn == `FlatBalanceBridges then bridgeIdx := some i
    let mut names : Array Name := #[]
    match targetIdx with
    | some i => names := names ++ env.header.moduleData[i]!.constNames
    | none => logInfo "AUDITWARN missing module FlatBalance"
    match bridgeIdx with
    | some i => names := names ++ env.header.moduleData[i]!.constNames
    | none => logInfo "AUDITWARN missing module FlatBalanceBridges"
    logInfo s!"AUDITENV modules=FlatBalance,FlatBalanceBridges declCount={names.size}"
    let mut axiomUnion : Array Name := #[]
    let mut unsafeCount := 0
    let mut partialCount := 0
    let mut opaqueCount := 0
    for n in names do
      match env.find? n with
      | none => logInfo s!"AUDITERR missing {n}"
      | some ci =>
        let kind := kindOf ci
        let safety := safetyOf ci
        if safety == "unsafe" then unsafeCount := unsafeCount + 1
        if safety == "partial" then partialCount := partialCount + 1
        if safety == "opaque" then opaqueCount := opaqueCount + 1
        let modName := match env.getModuleIdxFor? n with
          | some i => env.header.moduleNames[i]!
          | none => Name.mkSimple "current"
        let tyF ← Lean.Meta.liftMetaM (Lean.Meta.ppExpr ci.type)
        let valF ← match ci.value? with
          | some v => Lean.Meta.liftMetaM (Lean.Meta.ppExpr v)
          | none => pure "(none)"
        let axs ← Lean.collectAxioms n
        for a in axs do
          unless axiomUnion.contains a do
            axiomUnion := axiomUnion.push a
        let axsStr := String.intercalate "," (axs.toList.map toString)
        logInfo s!"AUDITDECL name={n} kind={kind} safety={safety} module={modName} axioms=[{axsStr}]"
        logInfo s!"AUDITTYPE {n} :: {tyF}"
        logInfo s!"AUDITVALUE {n} := {valF}"
    let unionStr := String.intercalate "," (axiomUnion.toList.map toString)
    logInfo s!"AUDITSUMMARY decls={names.size} unsafe={unsafeCount} partial={partialCount} opaque={opaqueCount} axiomUnion=[{unionStr}]"
    for endpoint in [`FlatBalance.not_flat_balanced_conjecture,
                     `FlatBalance.not_flat_balanced_conjecture_via_bridges] do
      let (seen, axs) := closureAux env [endpoint] {} #[]
      let mut localNames : Array Name := #[]
      for n in names do
        if seen.contains n then localNames := localNames.push n
      let list := String.intercalate "," (localNames.toList.map toString)
      let axStr := String.intercalate "," (axs.toList.map toString)
      logInfo s!"AUDITCLOSURE endpoint={endpoint} localClosureSize={localNames.size} localClosure=[{list}] axioms=[{axStr}]"

#print FlatBalance.not_flat_balanced_conjecture
#print FlatBalance.oddCliqueSum_K33
#print FlatBalance.evenCliqueSum_K33
