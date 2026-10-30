# Literal source differential component

**Assignment status: partial.** This lane closes the literal finite source to
the rational midpoint **linear** differential equation, together with the
all-order imaginary normalization and exact midpoint identification. It also
constructs the specified half-substitution of the actual integral Riccati
sequence and proves its recurrence. The all-order logarithmic derivative
identification with that sequence remains unproved. This is not a certificate
of the full requested source/Riccati/odd-primitive bridge or of `SourceClaim`.

All writes are confined to this lane. There were no child agents, git mutations,
other-lane edits, network requests, external posts, browser actions or account
actions. The only git invocation was read-only `git show d92803ddec:<path>` to
check and copy the frozen input bytes.

## Closed endpoint and actual types

Import `RiccatiScale`. The following names are in
`JacobiShifted.SourceBridge`. `A` is `MvPolynomial (Fin 2)
MidpointRational.QAlg`, and `G` is `QuadraticAlgebra A (-1) 0`.
`deltaA` acts on parameter coefficients using the **actual**
`MidpointRational.delta`; `deltaG` acts on the two Gaussian coordinates using
`deltaA`. Its `.im` is Gaussian imaginary part, distinct from the quadratic
`w` coordinate inside `QAlg`.

The closed combined endpoint is exactly:

```lean
theorem literal_source_linear_bridge (n : ℕ) :
    midpointG (F n)=sourceFCoeff n ∧ midpointG (L n)=sourceLogCoeff n ∧
    deltaG (deltaG (F n))+imaginaryUnit*deltaG (F (n+1))-gaussianEmbed S*F n=0 ∧
    tauA (L n).im= -(L n).im ∧ midpointA (L n).im=(sourceLogCoeff n).im
```

The finite Hankel endpoint is exactly:

```lean
theorem literal_hankel_midpoint_R1 (s : ℕ) :
    deltaG (deltaG (C s))+imaginaryUnit*(s : G)*deltaG (C s)+
      imaginaryUnit*deltaG (C (s+1))-gaussianEmbed S*C s=0
```

Here `S` is the explicit element

```lean
rationalScalar (1/2)*
  ((MvPolynomial.X 0+MvPolynomial.X 1)*MvPolynomial.C (MidpointRational.w^2)+
    (MvPolynomial.X 0-MvPolynomial.X 1)*MvPolynomial.C (MidpointRational.w*MidpointRational.x))
```

`literal_F_R2` proves the same linear equation using `potentialCurve`, and
`potentialCurve_eq : potentialCurve = gaussianEmbed S` identifies that
explicit curve expression with the midpoint potential. Neither theorem has a
differential-equation premise.

The actual integral-sequence substitution endpoints are:

```lean
theorem scale_delta (p : Midpoint.Param) :
  scale (integralOp p)=deltaA (scale p)
theorem scaledH_zero : scaledH 0=0
theorem scaledH_one : scaledH 1=S
theorem scaledH_recurrence (n : ℕ) (hn : 1≤n) :
  scaledH (n+1)= -deltaA (scaledH n)-
    ∑ i ∈ Finset.range (n+1), scaledH i*scaledH (n-i)
```

`scale` is `MvPolynomial.eval₂Hom (MvPolynomial.C.comp
MidpointRational.lift) subVar`; `subVar 0=(u+v)/2` and
`subVar 1=(u-v)/2`. No divisibility preservation is claimed for this map.

The first logarithmic derivative, including its sign, is proved directly:

```lean
theorem logarithmic_derivative_one :
  deltaG (L 1)= -imaginaryUnit*gaussianEmbed (scaledH 1)
theorem imaginary_logarithmic_derivative_one :
  deltaA (L 1).im= -scaledH 1
```

The authoritative fully elaborated types of all declarations, including
generated private declarations, are in
`verification/fresh/logs/SourceBridgeAudit.log`.

## Proof mechanism

`LiteralFinite` generalizes only the evaluation ring of the exact finite
formulas in `SourceDefs`. It retains the original factorial product,
`inverseFactorCoeff`, augmentation, finite convolution powers and finite
logarithm. It proves naturality under ring homomorphisms and proves that the
source instantiation is the actual `sourceC`, `sourceFCoeff`, `powerCoeff` and
`sourceLogCoeff`. In particular `L` is not defined by a Riccati recurrence.

`LiteralMidpoint` constructs `t=w+x`, `tInv=w-x`, proves `t*tInv=1`, and uses
`xi=(1+i*t)/2`, `eta=(1-i*tInv)/2`. The actual midpoint homomorphism sends
them to the unchanged source midpoint coordinates. Coefficientwise tau sends
both to their Gaussian conjugates and fixes the rational parameter
coefficients. Naturality transfers this to the full literal finite logarithm.
Taking Gaussian imaginary parts proves its tau-odd normalization at every
order. No parameter-swap antisymmetry shortcut is used.

`LiteralDifferential` proves Leibniz for the concrete coefficient operators,
the curve identity `2*xi*eta=xi+eta`, and
`deltaG xi=i*xi*(xi-1)`, `deltaG eta=i*eta*(eta-1)`.

`LiteralHankel` starts from the literal product
`hankelNumerator_succ`. Rational factorial cancellation gives
`(l+1)*a_i(l+1)=(parameter_i-l*(l+1))*a_i(l)`. It differentiates the actual
finite sum, shifts its two index sums with the vanished boundary terms, and
proves the monomial second-derivative identity. The mixed term vanishes by
the proved curve relation. Summing gives `literal_hankel_R1`.
`LiteralPotential` identifies its potential with `S` by direct ring algebra.

`LiteralInverseFactor` derives the shifted coefficient recurrence from
`inverseFactorCoeff`'s own finite geometric convolution and proves its support
vanishing. Reindexing the differentiated finite `F` sum then gives R2. No
Stirling-number identification or assumed coefficient recurrence is used.

`RiccatiScale` maps the concrete integral `Midpoint.h`, proves commutation with
the actual delta, transports the actual `h_recurrence`, and bundles the closed
linear source endpoint. The first logarithmic derivative follows from the
literal finite `L 1=F 1` identity and R2 at zero.

## Exact integration map and remaining obligation

Copy the new modules listed in `build-order.json` alongside the byte-identical
frozen dependencies, then import `RiccatiScale`. The namespace is separate
from the root namespaces; no frozen definition needs changing. The inherited
`OddPrimitiveSequence` is included in the combined audit/replay imports.

**Still missing:** an all-order coefficientwise logarithmic chain theorem for
the actual finite `literalLog`, followed by the coefficient comparison/unique
Riccati recurrence proving
`deltaG (L n)=i^(-n)*gaussianEmbed (scaledH n)` for positive `n` (with a suitable
formal encoding of the Gaussian unit powers). Consequently the all-order odd
imaginary derivative identity and its use of root's normalized primitive
uniqueness have not been proved here. The normalization and midpoint parts of
that future step are already closed. There is no theorem here that assumes
the missing log-chain or coefficient-identification statements as premises.

No use of `PowerSeries.logOf`, spectral-variable differentiation, analytic
asymptotics, a hidden ODE, a replacement source abstraction, or a primitive
existence premise occurs. The finite-polynomial geometric telescoping route
for the remaining coefficientwise log-chain was considered but not implemented;
it has no claimed PASS. Degree/Catalan/final valuation assembly remains root's
separate work.

## Verification and provenance

`inputs-before.json` records the frozen input hashes after comparison with
commit `d92803ddec`. Every root formal `.lean` was copied byte-identically;
unused copies are retained under `inputs/frozen-root`, outside the final
module set. `inputs-after.json` verifies the original paths and the copied
snapshots again. The original root files, including `SourceDefs.lean`, are
unchanged.

`run_lean.py` is copied exactly from root and `guard.py` exactly from the
primitive lane. The strict replay asserts the supplied Lean executable SHA
and mathlib revision. It packages only Lean sources and the two runner scripts,
extracts into a fresh lane-local directory, asserts the extraction contains no
local oleans, and compiles sequentially with
`-j1 -M4096 -DwarningAsError=true -DautoImplicit=false`. Each process tree uses
the sampled 3 GiB RSS guard, without an address-space cap.

Reproduce in this lane:

```sh
python3 replay.py --output verification/another-fresh-extraction
```

The destination must not exist. `source-manifest.json` and
`formal-source.tar.gz` contain the exact replay input hashes and deterministic
source-only archive. The strict receipt is
`verification/fresh/receipt.json`. `SourceBridgeInventory` checks exact module
origin and safety for all new proof-module declarations; `SourceBridgeAudit`
executes actual `#check` and `#print axioms` commands for every such name,
including private and generated names. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted by the parser. Imported filtration, midpoint and
odd-primitive audits and literal `SourceChecks` are replayed as well. The
audit/inventory command implementations are verification tooling, outside the
proof-module declaration set.

Failed incremental elaborations are retained in `formal/logs`, including the
finite-map simplification fixes, nested-extensionality fixes, Nat-cast typing,
ring normalization and associativity fixes, a `congr` heartbeat timeout, and
the audit's initial auxiliary-name handling failures. Numeric components in
private Lean names cannot be reconstructed as ordinary string components;
the final audit passes the actual environment `Name` directly through
`mkIdent` to the check/print commands. Only the auxiliary-reference linter is
disabled for those explicit exhaustive audit commands. Final proof modules
retain warnings as errors. No failed elaboration is represented as a
certificate. Initial dependency compilation and the first bridge compilation
did not overlap; their receipt timestamps were checked. Resource outcomes and
exact hashes are recorded in `provenance.json` and the replay receipt.
