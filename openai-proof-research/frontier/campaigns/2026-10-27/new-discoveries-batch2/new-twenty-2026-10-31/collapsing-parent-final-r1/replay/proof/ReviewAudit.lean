/-
  REVIEWER SUPPLEMENT (not part of the literal mathematical module `MathDB378395`).
  Enumerates every constant stored in the module data of `MathDB378395`, including
  auxiliary and compiler/structure-generated declarations, and cross-checks that list
  against a scan of the whole environment for constants whose origin is `MathDB378395`.
  For each constant it prints the origin, kind and full type (pp.all), checks body
  presence via `value? true` for every definition and theorem, rejects axioms, opaque
  constants, quotient primitives, unsafe/partial/implemented_by/extern constants and
  `sorry` in any value, and checks that the transitive axioms are a subset of
  {propext, Classical.choice, Quot.sound}.
-/
import MathDB378395
set_option warningAsError true
set_option pp.all true
set_option pp.proofs true
set_option pp.maxSteps 10000000
set_option pp.deepTerms true
set_option maxRecDepth 10000
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let some idx := env.getModuleIdx? `MathDB378395 | throwError "module MathDB378395 not imported"
 let names := (env.header.moduleData[idx.toNat]!.constNames).qsort (fun a b => a.toString < b.toString)
 -- independent cross-check: scan every constant in the environment by origin
 let mut scanned : Array Name := #[]
 for (n, _) in env.constants.toList do
  if env.getModuleIdxFor? n == some idx then scanned := scanned.push n
 scanned := scanned.qsort (fun a b => a.toString < b.toString)
 unless scanned == names do throwError "inventory mismatch {names.size} vs {scanned.size}"
 let mut count : Nat := 0
 let mut withBody : Nat := 0
 for n in names do
  let some ci := env.find? n | throwError "lost {n}"
  let origin := (env.getModuleIdxFor? n).bind (env.header.moduleNames[·]?)
  unless origin == some `MathDB378395 do throwError "origin mismatch {n}"
  let kind := match ci with
   | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
   | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
   | .ctorInfo _ => "ctor" | .recInfo _ => "recursor"
  count := count + 1
  let body := (ci.value? true).isSome
  logInfo m!"DECL {n} ORIGIN {origin} KIND {kind} UNSAFE {ci.isUnsafe} PARTIAL {ci.isPartial} BODY {body}"
  logInfo m!"FULL_TYPE {n}\n{ci.type}"
  if ci.isUnsafe || ci.isPartial then throwError "unsafe or partial {n}"
  if kind == "axiom" || kind == "opaque" || kind == "quot" then throwError "forbidden kind {kind} {n}"
  if (Lean.Compiler.implementedByAttr.getParam? env n).isSome then throwError "implemented_by {n}"
  if Lean.isExtern env n then throwError "extern {n}"
  if kind == "def" || kind == "theorem" then
   unless body do throwError "missing body {n}"
   withBody := withBody + 1
  if let some v := ci.value? true then
   if v.hasSorry then throwError "sorry in value {n}"
  let axs ← Lean.collectAxioms n
  logInfo m!"TRANSITIVE_AXIOMS {n} {axs}"
  for ax in axs do
   unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
    throwError "forbidden axiom {n} {ax}"
 logInfo m!"TOTAL {count} WITH_BODY {withBody}"
 unless count == 134 do throwError "unexpected inventory {count}"
