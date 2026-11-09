import SourceClaim
import Lean
set_option autoImplicit false
set_option warningAsError true
set_option pp.privateNames true
set_option linter.auxLemma false
open Lean Elab Command in
elab "#whole_audit" : command => do
  let env ← getEnv
  let modules := #[`MidpointAlgebra, `BinaryDigits, `Filtration, `Riccati, `MidpointSequence,
    `ParameterDegree, `CatalanTop, `SourceDefs, `LiteralFinite, `MidpointParity,
    `MidpointNormalForm, `MidpointRational, `LiteralMidpoint, `LiteralDifferential,
    `LiteralHankel, `LiteralPotential, `LiteralInverseFactor, `RiccatiScale, `ScaledTop,
    `OddTriangular, `MidpointPrimitive, `OddPrimitiveSequence, `BinomialMoments,
    `FiniteTransform, `BinomialOddSum, `PurePrimitive, `FiniteLogChain,
    `LiteralLogRiccati, `LogRiccatiIdentification, `LiteralPureCoefficient,
    `DyadicArithmetic, `HalfSubstitution, `SourceUpperBound, `SourceSharpness, `SourceClaim]
  for (name, info) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if modules.contains origin then
        logInfo m!"DECL {name}"
        logInfo m!"ORIGIN {name} {origin}"
        logInfo m!"UNSAFE {name} {info.isUnsafe}"
        if info.isUnsafe then throwError m!"Unsafe declaration: {name}"
        elabCommand (← `(#check $(mkIdent name)))
        elabCommand (← `(#print axioms $(mkIdent name)))
#whole_audit
