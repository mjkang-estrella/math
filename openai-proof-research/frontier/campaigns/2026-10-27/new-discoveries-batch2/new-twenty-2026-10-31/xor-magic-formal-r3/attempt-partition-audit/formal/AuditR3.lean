import LiftGraph
import AffineLift
import LiftFibres
import LiftSums
import LiftSections
import LiftIncidence
import LiftEdgeCount
import StrongCycles
import Literal
import Certificates
import Base16Open5
import Base16Open7
import Base16Open9
import Base16Open11
import Base16Closed4
import Base16Closed6
import Base16Closed8
import Base16Closed10
import Base32Open5
import Base32Open7
import Base32Open9
import Base32Open11
import Base32Open13
import Base32Open15
import Base32Open17
import Base32Open19
import Base32Open21
import Base32Open23
import Base32Open25
import Base32Open27
import Base32Closed4
import Base32Closed6
import Base32Closed8
import Base32Closed10
import Base32Closed12
import Base32Closed14
import Base32Closed16
import Base32Closed18
import Base32Closed20
import Base32Closed22
import Base32Closed24
import Base32Closed26
import BaseEndpoints
import Four
import TranslationCardinality
import TranslationFour
import TotalBits
import Complements
import InterpolationArithmetic
import GeneralObstruction
import SeedStructure
import Seed16Closed4
import Seed16Open5
import Seed32Closed4
import Seed32Open5
import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n,c) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if (["LiftGraph", "AffineLift", "LiftFibres", "LiftSums", "LiftSections", "LiftIncidence", "LiftEdgeCount", "StrongCycles"] : List String).contains m.toString then
      count := count + 1
      let ax ← Lean.collectAxioms n
      logInfo m!"DECL|{n}|MODULE|{m}|UNSAFE|{c.isUnsafe}|PARTIAL|{c.isPartial}|AXIOMS|{ax.toList}"
      logInfo m!"FULL_TYPE_AST|{repr c.type}"
      logInfo m!"FULL_BODY_AST_value?_true|{repr (c.value? true)}"
      if c.isUnsafe || c.isPartial then throwError "bad safety {n}"
      match c with
      | .axiomInfo _ => throwError "local axiom {n}"
      | _ => pure ()
      match c with
      | .inductInfo _ => logInfo m!"KERNEL_DECL_KIND|inductive|{n}"
      | .ctorInfo _ => logInfo m!"KERNEL_DECL_KIND|constructor|{n}"
      | .recInfo _ => logInfo m!"KERNEL_DECL_KIND|recursor|{n}"
      | _ => if !(c.value? true).isSome then throwError "missing body {n}"
      for x in ax do
        if !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains x then
          throwError "disallowed axiom {x} in {n}"
  logInfo m!"AUDITED_LOCAL_DECLARATIONS|{count}"
