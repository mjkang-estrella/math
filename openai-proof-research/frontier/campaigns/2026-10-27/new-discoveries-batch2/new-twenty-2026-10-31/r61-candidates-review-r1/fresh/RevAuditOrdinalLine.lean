import OrdinalLine
open Lean Elab Command Meta

/- Reviewer audit (r61-candidates-review-r1): every constant whose module is `OrdinalLine`. -/
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `OrdinalLine | throwError "module not found"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some idx then names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut bad : Array String := #[]
  for n in names do
    let some c := env.find? n | throwError "missing {n}"
    let kind := match c with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "recursor"
    let valExpr? : Option Expr := match c with
      | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value | _ => none
    let hasVal := valExpr?.isSome
    let valSorry := match valExpr? with | some e => e.hasSorry | none => false
    if valSorry then bad := bad.push s!"sorry-in-value {n}"
    let needsVal := kind == "def" || kind == "theorem" || kind == "opaque"
    if kind == "axiom" || kind == "opaque" || kind == "quot" then bad := bad.push s!"kind {kind} {n}"
    if needsVal && !hasVal then bad := bad.push s!"novalue {n}"
    if c.isUnsafe then bad := bad.push s!"unsafe {n}"
    if c.isPartial then bad := bad.push s!"partial {n}"
    if (Lean.Compiler.implementedByAttr.getParam? env n).isSome then bad := bad.push s!"implemented_by {n}"
    if Lean.isExtern env n then bad := bad.push s!"extern {n}"
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless allowed.contains a do bad := bad.push s!"axiom {a} in {n}"
    let ty ← liftTermElabM <| do
      let f ← ppExpr c.type
      pure (toString f)
    logInfo m!"DECL {n} | module OrdinalLine | kind {kind} | value {hasVal} | valueDepth {toString (match valExpr? with | some e => e.approxDepth.toNat | none => 0)} | unsafe {c.isUnsafe} | partial {c.isPartial} | axioms {axs.toList} | type {ty.replace "\n" " "}"
  logInfo m!"TOTAL_LOCAL {names.size}"
  if bad.size > 0 then throwError m!"AUDIT_FAIL {bad.toList}"
  logInfo m!"AUDIT_OK"
