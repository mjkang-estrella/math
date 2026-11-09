import CountR5Controls
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
open Lean
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000
run_cmd do
  let env ← getEnv
  let localMods : Array Name := #[`Dynamics, `Reduction, `SourceSemantics, `Cardinality,
    `CountRotation, `CountArithmetic, `CountFourier, `CountTransfer, `CountFinal, `CountControls, `CountSpectralAlgebra, `CountSpectralModel, `CountFinal2, `CountSpectralControls, `CountR4Period, `CountFinal3, `CountR4Controls, `CountR5Top, `CountR5Inclusion, `CountR5Fibre, `CountFinal4, `CountR5Controls]
  let mut seeds : NameSet := {}
  for (n, _) in env.constants.toList do
    let owner := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.header.mainModule
    if localMods.contains owner then seeds := seeds.insert n
  let mut pending := seeds.toArray
  let mut closure : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if !closure.contains n then
      closure := closure.insert n
      let some ci := env.find? n | throwError "Missing declaration {n}"
      for d in ci.getUsedConstantsAsSet do
        if !closure.contains d then pending := pending.push d
  let mut flagged : Nat := 0
  let mut localFlagged : Nat := 0
  let mut allAxioms : NameSet := {}
  for n in closure do
    let some ci := env.find? n | throwError "Missing declaration {n}"
    for d in ci.getUsedConstantsAsSet do
      unless closure.contains d do throwError "Closure not closed: {n} -> {d}"
    let impl := Lean.Compiler.getImplementedBy? env n
    let ext := isExtern env n
    let bad := ci.isUnsafe || ci.isPartial || impl.isSome || ext || n.toString.endsWith "_unsafe_rec"
    if bad then
      flagged := flagged + 1
      if seeds.contains n then localFlagged := localFlagged + 1
    match ci with
    | .axiomInfo _ =>
      allAxioms := allAxioms.insert n
      unless n == `propext || n == `Classical.choice || n == `Quot.sound do
        throwError "Forbidden axiom {n}"
    | _ => pure ()
    logInfo m!"CLOSURE_DECL {n} LOCAL {seeds.contains n} UNSAFE {ci.isUnsafe} PARTIAL {ci.isPartial} IMPLEMENTED_BY {impl} EXTERN {ext}"
  unless localFlagged == 0 do throwError "Local forbidden flags {localFlagged}"
  logInfo m!"AUDIT_TOTAL seeds={seeds.size} closure={closure.size} flags={flagged} localFlags={localFlagged} axioms={allAxioms.toArray}"
  logInfo "AUDIT_SET_EQUALS_REACHABLE_CLOSURE: constructed from all local declarations, including generated declarations; every dependency checked in set"
#print axioms ChanLevine.Round5.primitiveTopCoefficient
#print axioms ChanLevine.Round5.primitivePeriodData
#print axioms ChanLevine.Round5.weighted_inclusion_exclusion
#print axioms ChanLevine.Round5.fourier_inclusion_exclusion
#print axioms ChanLevine.Round5.spectralOrder
#print axioms ChanLevine.Round5.unitCount
#print ChanLevine.Round5.spectralOrder
#print ChanLevine.Round5.unitCount
