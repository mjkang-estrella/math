import Final
import Lean
open Lean Elab Command
-- Independent review audit: kind inventory, body/value presence, transitive axioms.
run_cmd do
  let env ← getEnv
  let mut n : Nat := 0
  let mut noVal : Array Name := #[]
  let mut axiomDecls : Array Name := #[]
  let mut nThm : Nat := 0
  let mut nDef : Nat := 0
  let mut nOther : Nat := 0
  let mut kindOther : Array String := #[]
  for (nm, ci) in env.constants.toList do
    unless (nm.toString.splitOn "CommonBasis332371").length > 1 do continue
    n := n + 1
    match ci with
    | .thmInfo _ => nThm := nThm + 1
    | .defnInfo _ => nDef := nDef + 1
    | .axiomInfo _ =>
      axiomDecls := axiomDecls.push nm
    | .ctorInfo _ => nOther := nOther + 1; kindOther := kindOther.push "ctor"
    | .recInfo _ => nOther := nOther + 1; kindOther := kindOther.push "rec"
    | .inductInfo _ => nOther := nOther + 1; kindOther := kindOther.push "induct"
    | .opaqueInfo _ => nOther := nOther + 1; kindOther := kindOther.push "opaque"
    | .quotInfo _ => nOther := nOther + 1; kindOther := kindOther.push "quot" 
    match ci.value? (allowOpaque := true) with
    | some _ => pure ()
    | none =>
      match ci with
      | .axiomInfo _ => pure ()
      | _ => noVal := noVal.push nm
  logInfo m!"REVIEW inventory: {n} declarations (thm {nThm}, def {nDef}, other {nOther})"
  unless kindOther.isEmpty do logInfo m!"REVIEW other kinds: {kindOther}"
  logInfo m!"REVIEW local axiom declarations: {axiomDecls}"
  logInfo m!"REVIEW non-axiom declarations lacking value?: {noVal}"
  let axs ← collectAxioms `CommonBasis332371.counterexample
  logInfo m!"REVIEW transitive axioms of counterexample: {axs}"
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "review: forbidden transitive axiom {ax}"
  -- body presence: every local constant must be an axiom (none expected) or carry a value
  for (nm, ci) in env.constants.toList do
    unless (nm.toString.splitOn "CommonBasis332371").length > 1 do continue
    match ci with
    | .axiomInfo _ => throwError "review: local axiom {nm}"
    | _ => match ci.value? (allowOpaque := true) with
      | some _ => pure ()
      | none => throwError "review: no body for {nm}"
  unless n == 106 do throwError "review: declaration count {n} != 106"
  logInfo "REVIEW body-presence, count and axiom-closure checks passed"
