import Cassinian
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if ["Cassinian"].contains m.toString then
      count := count + 1
      let ax ← Lean.collectAxioms n
      let kind := match c with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      logInfo m!"INVENTORY|{m}|{n}|{kind}|{c.isUnsafe}|{ax.toList}"
      if c.isUnsafe then throwError "unsafe local declaration {n}"
      if kind == "axiom" then throwError "local axiom {n}"
      for a in ax do
        if !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains a then
          throwError "disallowed axiom {a} in {n}"
  logInfo m!"AUDITED_LOCAL_DECLARATIONS|{count}"
#print Cassinian331705.SourceClaim
#print Cassinian331705.source_refutation
#print axioms Cassinian331705.source_refutation
