import ASEPArcs
import PermOrder
import AuditLib

/-!
# Full declaration audit (MathDB 368807 dossier)

Every constant whose home module is one of the 22 frozen modules is reported, including generated
ones (auxiliary proofs, matchers, equation lemmas, structure projections, `_unsafe_rec` helpers):
module, kind, full type, `value?` (with and without `allowOpaque`), unsafe/partial flags,
implemented_by/extern attributes and `collectAxioms`.  Independently, an uncached body walk computes
the closure of all local constants and of each endpoint.  The command fails (so the replay fails)
if any check does not hold.
-/

open Lean Elab Command Meta ASEPAudit

def auditModules : Array Name := #[`ASEPData, `ASEPCheck, `ASEPCover, `ASEPCerts0, `ASEPCerts1,
  `ASEPCerts2, `ASEPCerts3, `ASEPCerts4, `ASEPCerts5, `ASEPCerts6, `ASEPCerts7, `ASEPCerts8,
  `ASEPCerts9, `ASEPCerts10, `ASEPCerts11, `ASEPDefs, `ASEPSound, `ASEPVertex, `ASEPBridge,
  `ASEPMain, `ASEPArcs, `PermOrder]

def endpointNames : Array Name := #[`ASEP.arc_counterexample, `ASEP.arc_neighborhood_tour_conjecture_false,
  `ASEP.counterexample, `ASEP.neighborhood_tour_conjecture_false, `ASEP.segment_not_face,
  `ASEP.segment_not_exposed]

/-- Kernel-checked facts every endpoint closure must reach (the certificate checks and the coverage). -/
def requiredInClosure : Array Name :=
  #[`ASEP.certs_cover, `ASEP.XN_tight, `ASEP.not_extreme_of_dir] ++
  (Array.range 48).map (fun k => Name.mkStr `ASEP s!"chunk{k}_ok")

/-- Endpoints that assert that `x*` is a vertex must also reach the extremality proof. -/
def requiredFor (e : Name) : Array Name :=
  if e == `ASEP.segment_not_face || e == `ASEP.segment_not_exposed then requiredInClosure
  else requiredInClosure.push `ASEP.xs_extreme

elab "#asep_full_audit" : command => do
  let env := (← getEnv).setExporting false
  let mods := env.header.moduleNames
  let locals : Array (Name × Name × ConstantInfo) := env.constants.map₁.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := mods[idx.toNat]!
      if auditModules.contains m then acc.push (n, m, ci) else acc
    | none => acc
  let locals := locals.qsort (fun a b => Name.lt a.1 b.1)
  let mut failures : Array String := #[]
  let mut helpers : Array Name := #[]
  let mut perModule : Std.HashMap String Nat := {}
  let mut kinds : Std.HashMap String Nat := {}
  for (n, m, ci) in locals do
    let (j, clean) ← liftTermElabM <| declReport env n m ci
    logInfo m!"ASEPAUDIT-DECL {j.compress}"
    perModule := perModule.insert m.toString (perModule.getD m.toString 0 + 1)
    kinds := kinds.insert (kindOf ci) (kinds.getD (kindOf ci) 0 + 1)
    if isUnsafeRecName n then
      helpers := helpers.push n
      -- a helper is tolerated only as a partial/unsafe compiler artefact of a safe local definition
      match n with
      | .str base _ =>
        match env.find? base with
        | some (.defnInfo v) =>
          unless v.safety == .safe do failures := failures.push s!"helper base not safe: {base}"
          unless ci.isPartial || ci.isUnsafe do failures := failures.push s!"helper not flagged: {n}"
        | _ => failures := failures.push s!"helper without safe base definition: {n}"
      | _ => pure ()
    else if !clean then
      failures := failures.push s!"unclean declaration: {n}"
  -- uncached walk over the closure of all local constants together
  let all := closure env (locals.map (·.1))
  unless (nonStd all.axioms).isEmpty do failures := failures.push s!"nonstandard axioms {nonStd all.axioms}"
  unless all.missing.isEmpty do failures := failures.push s!"missing constants {names all.missing}"
  unless all.forbidden.isEmpty do failures := failures.push s!"forbidden constants {names all.forbidden}"
  -- endpoint closures
  let mut eps : Array Json := #[]
  for e in endpointNames do
    let some _ := env.find? e | failures := failures.push s!"endpoint missing: {e}"
    let cl := closure env #[e]
    let axs ← liftCoreM <| collectAxioms e
    let helperHits := helpers.filter (fun h => cl.seen.contains h)
    let absent := (requiredFor e).filter (fun r => !cl.seen.contains r)
    let ok := (nonStd cl.axioms).isEmpty && axs.all (fun a => allowedAxioms.contains a) &&
      cl.missing.isEmpty && cl.forbidden.isEmpty && cl.unsafeConsts.isEmpty &&
      cl.partialConsts.isEmpty && cl.unsafeRec.isEmpty && helperHits.isEmpty && absent.isEmpty
    unless ok do failures := failures.push s!"endpoint check failed: {e}"
    eps := eps.push <| Json.mkObj [("endpoint", toJson e.toString),
      ("closure_size", toJson cl.seen.size), ("walk_axioms", toJson (names cl.axioms)),
      ("collectAxioms", toJson (axs.toList.map Name.toString)),
      ("unsafe_in_closure", toJson (names cl.unsafeConsts)), ("partial_in_closure", toJson (names cl.partialConsts)),
      ("unsafe_rec_in_closure", toJson (names cl.unsafeRec)),
      ("local_unsafe_rec_helpers_reached", toJson (helperHits.toList.map Name.toString)),
      ("forbidden_in_closure", toJson (names cl.forbidden)), ("missing", toJson (names cl.missing)),
      ("required_facts_absent", toJson (absent.toList.map Name.toString)), ("ok", toJson ok)]
  let summary := Json.mkObj [
    ("num_local_constants", toJson locals.size),
    ("per_module", toJson (perModule.toList.map (fun (a, b) => Json.mkObj [("module", toJson a), ("count", toJson b)]))),
    ("per_kind", toJson (kinds.toList.map (fun (a, b) => Json.mkObj [("kind", toJson a), ("count", toJson b)]))),
    ("unsafe_rec_helpers", toJson (helpers.toList.map Name.toString)),
    ("all_locals_walk_closure_size", toJson all.seen.size),
    ("all_locals_walk_axioms", toJson (names all.axioms)),
    ("all_locals_walk_unsafe", toJson (names all.unsafeConsts)),
    ("all_locals_walk_partial", toJson (names all.partialConsts)),
    ("endpoints", toJson eps), ("failures", toJson failures.toList)]
  logInfo m!"ASEPAUDIT-SUMMARY {summary.compress}"
  unless failures.isEmpty do throwError "ASEPAUDIT FAIL {failures.toList}"

#asep_full_audit

#assert_std_axioms ASEP.arc_counterexample
#assert_std_axioms ASEP.arc_neighborhood_tour_conjecture_false
#assert_std_axioms ASEP.counterexample
#assert_std_axioms ASEP.neighborhood_tour_conjecture_false
#assert_std_axioms ASEP.segment_not_face
#assert_std_axioms ASEP.segment_not_exposed
