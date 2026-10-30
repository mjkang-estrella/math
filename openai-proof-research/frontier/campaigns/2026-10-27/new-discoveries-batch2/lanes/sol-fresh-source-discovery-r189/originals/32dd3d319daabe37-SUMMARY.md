# Closed literal Jacobi SourceClaim — implementation complete

The final theorem is kernel checked with exactly this type:

```lean
JacobiShifted.source_claim : JacobiShifted.SourceClaim
```

It proves **both** the all-coefficient denominator upper bound and sharpness at
`Finsupp.single 0 r`, for every `r : ℕ` with `1 ≤ r`, using root's unchanged
literal `sourceKappa`, `TwoLocal`, `dyadicExponent`, and `SourceClaim` definitions.
There are no remaining mathematical bridges or additional hypotheses.
The sharp coefficient is nonzero and has exact valuation `-dyadicExponent r`.

The five new mathematical modules are `DyadicArithmetic`, `HalfSubstitution`,
`SourceUpperBound`, `SourceSharpness`, and `SourceClaim`. They contribute 58
module-origin declarations, including private/generated helpers and local
instances. Counts by origin are 18, 9, 23, 7, and 1 respectively. This includes
the generated `JacobiShifted.TwoLocal.eq_1` allocated in `DyadicArithmetic`;
the original definition's source bytes remain unchanged.

The upper bound expands the actual half substitution as an integer polynomial
numerator divided by `2^degree`. It transports the proved normalized integral
primitives in a finite support sum and identifies this sum with the literal
logarithmic coefficient by derivative equality and tau normalization. Legendre
and factorial divisibility make every scaled summand TwoLocal. The sharpness
proof combines the literal Catalan/binomial-sum formula, the closed binomial
valuation, Kummer, nonvanishing, and the odd-denominator/valuation equivalence.

## Verification and artifacts

The final **source-only isolated replay PASS** is
`verification/final-fresh/replay-receipt.json`, also copied to
`replay-receipt.json`. It rebuilt 35 mathematical modules (30 unchanged frozen
dependencies plus five new proof modules) and three audit/interface modules
from copied source, with no local prebuilt artifacts. Every mathematical log
is empty. All 38 actual Lean logs match the development logs byte-for-byte.

Actual `#check` and `#print axioms` output covers every one of the 58 new
module-origin declarations. All have `isUnsafe=false`; their only axioms are
`propext`, `Classical.choice`, and `Quot.sound`. The final theorem uses those
same three axioms. `declarations.json` enumerates the complete audited set;
`formal/SourceClaimAudit.lean.log`, `SourceClaimInventory.lean.log`, and
`SourceClaimInterfaces.lean.log` retain the actual reports. The latter also
prints the unchanged source definitions and checks the expanded literal type.
Audit elaborator implementations are outside the mathematical proof set.

Lean binary SHA and mathlib revision match the user pins before and after the
replay. Builds use the unchanged `run_lean.py`, sequential `-j1 -M4096`,
`warningAsError=true`, and `autoImplicit=false`. Peak sampled process-tree RSS:
**3,106,912 KiB**, below the 3,145,728 KiB guard.
Diagnostics: 84,598 bytes, below the 512 MiB cap. There is no
512 MiB address-space cap.

The deterministic archive is `packet/source-claim-component.zip` (76,466 bytes),
with no prebuilt artifacts. Its SHA-256 is:

```text
b3567bbcc7a3f6f178a5fd714ca2e078e9a4a63aa5f26d32f14ffdf5ac9f9b80
```

Reproduce with a destination that does not already exist:

```sh
python3 scripts/replay.py packet/source-claim-component.zip verification/a-new-empty-directory
```

The archive contains the standalone replay script, immutable source manifest,
pins, component configuration, original runner/guard, and all necessary sources.
Rebuilding the archive reproduces its hash. The first fresh replay also passed;
the final replay follows a receipt-field clarification only. All Lean source
bytes are identical across those two runs; `verification/replay-history.json`
records that history.

`INTERFACES.md`, `PROOFMAP.md`, and `import-map.json` provide the integration,
proof, and import maps. `provenance.json`, `provenance-initial.json`,
`supplemental-provenance.json`, `library-provenance.json`, `new-source-map.json`,
`manifest.json`, and `frozen-source-check.json` supply hashes and source paths.
All 44 originally copied frozen source/runner files match their originals
before and after. In particular, `SourceDefs.lean` remains SHA-256
`df95c10e6a9371c1fc3f09424375a4ff51707980db0635e9a321d2c8a09033a5`.

## Scope and honest remaining work

No assigned mathematical gap remains. Root still handles the manuscript,
independent final review, current novelty investigation, integration,
acceptance, and accounting. Jacobi credit remains **0**; shared counts remain
**2/30 additional, 32/60 total**. No git operations, children, network contact,
posting, browser actions, ledger edits, or other-lane file writes occurred.

One packaging command omitted its working directory and briefly created three
empty workspace-root directories (`scripts`, `packet`, `verification`). They
contained no files and were immediately removed; their absence was rechecked.
This instruction deviation is disclosed rather than claiming perfect write
confinement. All retained artifacts are in this assigned lane, and frozen root
source bytes are unchanged. See also `HONEST-GAPS.md`.
