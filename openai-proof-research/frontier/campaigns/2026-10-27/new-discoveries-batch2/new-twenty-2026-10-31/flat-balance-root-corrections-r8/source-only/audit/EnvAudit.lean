/-
INDEPENDENT environment audit (r6) for the MathDB 352972 certificate.

Enumerates EVERY declaration of the production modules `FlatBalance` and
`FlatBalanceBridges` directly from the elaborated environment (no namespace
filter): private, generated, constructor, recursor, equation-lemma and
auxiliary declarations included.  For each: kind, definition safety,
origin module, reducibility hints (defns), full type, full value with
`value? (allowOpaque := true)`, direct constant dependencies, and the
complete transitive axiom closure (`Lean.collectAxioms`, cross-checked
against an independent BFS).  Also: union of axioms over all new
declarations (fatal if anything outside propext/Classical.choice/
Quot.sound), and the FULL transitive constant closure of BOTH refutation
endpoints with the local sub-closure.

Missing module or name is FATAL (throwError), never warn-and-pass.
This file is audit tooling only: it is NOT imported by any production
module and its own recursion lives outside the production dependency
closure; it proves nothing and adds no production declarations.

Pins: Lean v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52),
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

import FlatBalanceBridges
import Lean

open Lean Elab Command

namespace IndependentAuditEnvAudit

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def safetyOf : ConstantInfo → String
  | .defnInfo v => match v.safety with
    | DefinitionSafety.unsafe => "unsafe"
    | DefinitionSafety.partial => "partial"
    | DefinitionSafety.safe => "safe"
  | .opaqueInfo _ => "opaque"
  | _ => "none"

private def hintsOf : ConstantInfo → String
  | .defnInfo v => match v.hints with
    | ReducibilityHints.abbrev => "abbrev"
    | ReducibilityHints.opaque => "opaque_hint"
    | ReducibilityHints.regular _ => "regular"
  | _ => "none"

private def namesJson (l : List Name) : Json :=
  Json.arr (l.toArray.map (fun c => Json.str (toString c)))

private def extraOf : ConstantInfo → List (String × Json)
  | .inductInfo v => [("ctors", namesJson v.ctors),
                      ("numParams", Json.num v.numParams),
                      ("numIndices", Json.num v.numIndices)]
  | .ctorInfo v => [("induct", Json.str (toString v.induct))]
  | .recInfo v => [("allInductives", namesJson v.all),
                   ("numMinors", Json.num v.numMinors)]
  | _ => []

/-- Independent BFS transitive closure over constant dependencies. -/
private partial def bfsClosure (env : Environment) (frontier : List Name)
    (seen : Std.HashSet Name) (edges : List (String × Json)) (axs : Array Name) :
    Except String (Std.HashSet Name × List (String × Json) × Array Name) :=
  match frontier with
  | [] => pure (seen, edges, axs)
  | e :: rest =>
    if seen.contains e then bfsClosure env rest seen edges axs
    else
      let seen := seen.insert e
      match env.find? e with
      | none => Except.error s!"closure constant not found in environment: {e}"
      | some ci =>
        let deps := ci.getUsedConstantsAsSet.toList
        let axs :=
          match ci with
          | .axiomInfo _ => if axs.contains e then axs else axs.push e
          | _ => axs
        let edges := edges ++ [(toString e, namesJson deps)]
        bfsClosure env (rest ++ deps) seen edges axs

/-- Independent BFS axiom closure (axiom-kind constants only). -/
private partial def bfsAxioms (env : Environment) (frontier : List Name)
    (seen : Std.HashSet Name) (axs : Array Name) : Except String (Array Name) :=
  match frontier with
  | [] => pure axs
  | e :: rest =>
    if seen.contains e then bfsAxioms env rest seen axs
    else
      let seen := seen.insert e
      match env.find? e with
      | none => Except.error s!"axiom-closure constant not found: {e}"
      | some ci =>
        let deps := ci.getUsedConstantsAsSet.toList
        let axs := match ci with
          | .axiomInfo _ => if axs.contains e then axs else axs.push e
          | _ => axs
        bfsAxioms env (rest ++ deps) seen axs

private def axArraysEq (a b : Array Name) : Bool :=
  a.size == b.size && (a.zip b).all fun p => p.1 == p.2

end IndependentAuditEnvAudit

open IndependentAuditEnvAudit

run_cmd do
  liftTermElabM do
    -- Full unabridged pretty-printing: proofs and deep terms included,
    -- generous step/recursion limits, no ellipsis omission.
    Lean.withOptions (fun o =>
      o.set `pp.proofs true
        |>.set `pp.deepTerms true
        |>.set `pp.deepTerms.threshold 100000
        |>.set `pp.proofs.threshold 100000
        |>.set `pp.maxSteps 1000000
        |>.set `maxRecDepth 8192) do
      let env ← getEnv
      let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

      -- Module resolution: FATAL if missing.
      let mut targetIdx : Option Nat := none
      let mut bridgeIdx : Option Nat := none
      for i in [0:env.header.moduleData.size] do
        let mn := env.header.moduleNames[i]!
        if mn == `FlatBalance then targetIdx := some i
        if mn == `FlatBalanceBridges then bridgeIdx := some i
      unless targetIdx.isSome && bridgeIdx.isSome do
        throwError "AUDITFATAL: production module FlatBalance/FlatBalanceBridges missing from environment header"

      let rawNames : Array Name :=
        env.header.moduleData[targetIdx.get!]!.constNames ++
        env.header.moduleData[bridgeIdx.get!]!.constNames
      let seenNames : Std.HashSet Name := rawNames.foldl (init := {}) fun acc n => acc.insert n
      let names : Array Name := rawNames.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n

      logInfo s!"AUDITENV modules=FlatBalance,FlatBalanceBridges rawCount={seenNames.size} dedupCount={names.size}"

      let mut decls : Array Json := #[]
      let mut axiomUnion : Array Name := #[]
      let mut unsafeCount := 0
      let mut partialCount := 0
      let mut opaqueCount := 0
      let mut kindCounts : Std.HashMap String Nat := {}

      for n in names do
        match env.find? n with
        | none => throwError s!"AUDITFATAL: declared constant {n} of a production module not found in environment"
        | some ci =>
          let kind := kindOf ci
          let safety := safetyOf ci
          if safety == "unsafe" then unsafeCount := unsafeCount + 1
          if safety == "partial" then partialCount := partialCount + 1
          if safety == "opaque" then opaqueCount := opaqueCount + 1
          let kc := match kindCounts.get? kind with | some v => v | none => 0
          kindCounts := kindCounts.insert kind (kc + 1)
          let modName := match env.getModuleIdxFor? n with
            | some i => env.header.moduleNames[i]!
            | none => Name.mkSimple "current-file"
          let tyF ← do
            let f ← Lean.Meta.liftMetaM (Lean.Meta.ppExpr ci.type)
            pure (Lean.Format.pretty f 200)
          let valO := ci.value? (allowOpaque := true)
          let valF ← match valO with
            | some v => do
              let f ← Lean.Meta.liftMetaM (Lean.Meta.ppExpr v)
              pure (Lean.Format.pretty f 200)
            | none => pure ""
          let axs ← Lean.collectAxioms n
          for a in axs do
            unless axiomUnion.contains a do axiomUnion := axiomUnion.push a
          let deps := ci.getUsedConstantsAsSet.toList
          let axStr := String.intercalate "," (axs.toList.map toString)
          let j := Json.mkObj ([
            ("name", Json.str (toString n)),
            ("kind", Json.str kind),
            ("safety", Json.str safety),
            ("reducibilityHints", Json.str (hintsOf ci)),
            ("module", Json.str (toString modName)),
            ("axioms", namesJson axs.toList),
            ("type", Json.str tyF),
            ("value", (match valO with | some _ => Json.str valF | none => Json.null)),
            ("directConstants", namesJson deps)
          ] ++ extraOf ci)
          decls := decls.push j
          logInfo s!"AUDITDECL name={n} kind={kind} safety={safety} hints={hintsOf ci} module={modName} axioms=[{axStr}]"
          logInfo s!"AUDITTYPE {n} :: {tyF}"
          if valO.isSome then
            logInfo s!"AUDITVALUE {n} := {valF}"

      -- Axiom union gate: fatal on anything outside the permitted three.
      let extraAxs := axiomUnion.filter (fun a => !allowed.contains a)
      unless extraAxs.isEmpty do
        throwError s!"AUDITFATAL: axioms outside propext/Classical.choice/Quot.sound in production closure: {extraAxs}"

      -- Endpoints: FATAL if missing; full transitive closure of both.
      let endpoints : Array Name := #[`FlatBalance.not_flat_balanced_conjecture,
                                     `FlatBalance.not_flat_balanced_conjecture_via_bridges]
      let mut closures : Array Json := #[]
      for ep in endpoints do
        match env.find? ep with
        | none => throwError s!"AUDITFATAL: endpoint {ep} missing"
        | some _ => pure ()
        let (seen, edges, _axsBFS) ←
          match bfsClosure env [ep] {} [] #[] with
          | Except.error msg => throwError msg
          | Except.ok v => pure v
        let localNames := names.filter (fun n => seen.contains n)
        let axsCollect ← Lean.collectAxioms ep
        let axsBFS2 ←
          match bfsAxioms env [ep] {} #[] with
          | Except.error msg => throwError msg
          | Except.ok v => pure v
        unless axArraysEq axsCollect axsBFS2 do
          throwError s!"AUDITFATAL: axiom-closure mismatch for {ep}: collectAxioms={axsCollect} bfs={axsBFS2}"
        let axsStr := String.intercalate "," (axsCollect.toList.map toString)
        let locStr := String.intercalate "," (localNames.toList.map toString)
        let j := Json.mkObj [
          ("endpoint", Json.str (toString ep)),
          ("closureSize", Json.num seen.size),
          ("localClosureSize", Json.num localNames.size),
          ("closure", namesJson seen.toList),
          ("localClosure", namesJson localNames.toList),
          ("edges", Json.mkObj edges),
          ("axiomClosureCollectAxioms", namesJson axsCollect.toList),
          ("axiomClosureIndependentBFS", namesJson axsBFS2.toList)]
        closures := closures.push j
        logInfo s!"AUDITCLOSURE endpoint={ep} closureSize={seen.size} localClosureSize={localNames.size} localClosure=[{locStr}] axioms=[{axsStr}]"

      let unionStr := String.intercalate "," (axiomUnion.toList.map toString)
      let kindList := kindCounts.toList
      let summary := Json.mkObj [
        ("declCount", Json.num names.size),
        ("unsafe", Json.num unsafeCount),
        ("partial", Json.num partialCount),
        ("opaque", Json.num opaqueCount),
        ("kindCounts", Json.mkObj (kindList.map fun p => (p.1, Json.num p.2))),
        ("axiomUnion", namesJson axiomUnion.toList)]
      let doc := Json.mkObj [
        ("audit", Json.str "independent-env-audit-352972-r6"),
        ("pins", Json.mkObj [
          ("lean", Json.str "4.34.1"),
          ("lean_commit", Json.str "5045d0056413266e57c625dcd7c365b10e377c52"),
          ("mathlib", Json.str "d13f23b723b8a846827a245b89c10fc7d3f11612")]),
        ("modules", Json.arr #[
          Json.str "FlatBalance",
          Json.str "FlatBalanceBridges"]),
        ("summary", summary),
        ("declarations", Json.arr decls),
        ("endpointClosures", Json.arr closures)]

      let outPath := "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/flat-balance-final-review-sol-r7/results/352972-env-audit.json"
      IO.FS.writeFile outPath (Json.pretty doc 160)
      logInfo s!"AUDITSUMMARY decls={names.size} unsafe={unsafeCount} partial={partialCount} opaque={opaqueCount} kinds={kindList} axiomUnion=[{unionStr}] wrote={outPath}"
