import Audit
import Lean
open Lean Elab Command

/-! Independent review audit (xor-magic-review-r1).  Written separately from the
packet's Audit.lean: enumerates every constant whose defining module is a packet
module, rejects axioms / unsafe / partial / opaque / implemented_by / extern, and
checks transitive axioms against the allowed three. -/

def packetMods : List String := ["Literal", "Certificates", "Base16Open5", "Base16Open7", "Base16Open9",
  "Base16Open11", "Base16Closed4", "Base16Closed6", "Base16Closed8", "Base16Closed10", "Base32Open5",
  "Base32Open7", "Base32Open9", "Base32Open11", "Base32Open13", "Base32Open15", "Base32Open17",
  "Base32Open19", "Base32Open21", "Base32Open23", "Base32Open25", "Base32Open27", "Base32Closed4",
  "Base32Closed6", "Base32Closed8", "Base32Closed10", "Base32Closed12", "Base32Closed14", "Base32Closed16",
  "Base32Closed18", "Base32Closed20", "Base32Closed22", "Base32Closed24", "Base32Closed26", "BaseEndpoints",
  "Four", "TranslationCardinality", "TranslationFour", "TotalBits", "Complements", "InterpolationArithmetic",
  "GeneralObstruction", "SeedStructure", "Seed16Closed4", "Seed16Open5", "Seed32Closed4", "Seed32Open5", "Audit"]

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut thms : Nat := 0
  let mut bad : Array String := #[]
  let mut axset : Array Name := #[]
  for (n, c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless packetMods.contains m.toString do continue
    count := count + 1
    match c with
    | .axiomInfo _ => bad := bad.push s!"axiom {n}"
    | .opaqueInfo _ => bad := bad.push s!"opaque {n}"
    | .thmInfo _ => thms := thms + 1
    | _ => pure ()
    if c.isUnsafe then bad := bad.push s!"unsafe {n}"
    if c.isPartial then bad := bad.push s!"partial {n}"
    if (Lean.Compiler.implementedByAttr.getParam? env n).isSome then bad := bad.push s!"implemented_by {n}"
    if Lean.isExtern env n then bad := bad.push s!"extern {n}"
    let ax ← Lean.collectAxioms n
    for a in ax do
      unless axset.contains a do axset := axset.push a
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do bad := bad.push s!"{n} uses {a}"
  logInfo m!"REVIEW_AUDIT|declarations={count}|theorems={thms}|axioms_used={axset.toList}|bad={bad.toList}"
  unless bad.isEmpty do throwError "REVIEW_AUDIT_FAILED"

#print XorMagic.Bits
#print XorMagic.OpenMagic
#print XorMagic.ClosedMagic
#print XorMagic.OpenExists
#print XorMagic.ClosedExists
#print XorMagic.PrintedAt
#print XorMagic.CorrectedAt
#check @XorMagic.corrected_at_4
#check @XorMagic.corrected_at_5
#check @XorMagic.not_printed_at_four
#check @XorMagic.not_printed_ge_four
#check @XorMagic.not_closed_top_four
#check @XorMagic.translation_exists
#print axioms XorMagic.corrected_at_4
#print axioms XorMagic.corrected_at_5
#print axioms XorMagic.not_printed_ge_four
#print axioms XorMagic.not_closed_top_four
#print axioms XorMagic.Seed32Open5.factorCycle
