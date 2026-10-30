# Literal Jacobi finite-log chain and Riccati identification

**COMPLETE for the assigned log/Riccati bridge.** Import
`LogRiccatiIdentification`. There are no remaining premises or gaps in the
interfaces below. This component does not prove `SourceClaim`, degree bounds,
Catalan attainment, the final denominator/valuation assembly, or a novelty or
credit claim. Those are outside this assignment.

The namespace remains `JacobiShifted.SourceBridge`. The frozen `L` definition
is unchanged: `L n = literalLog coeffEmbed xi eta n`, with its actual finite
power-sum formula, and the inherited `midpoint_L` identifies it with the
unchanged `sourceLogCoeff`. `scaledH` remains the exact rational substitution
of the actual integral `Midpoint.h`, using a=(u+v)/2 and b=(u-v)/2.

## Closed interfaces

The new `LiteralLogRiccati` module defines only the derivative abbreviation
`U n := deltaG (L n)` and packages the actual sequences as power series.
It does not redefine `F`, `L`, or `scaledH`.

```lean
theorem literal_log_finiteLog (n : ℕ) :
  L n = FiniteChain.finiteLog (coeffEmbed.comp MvPolynomial.C) F n

theorem literal_log_chain (n : ℕ) :
  (∑ j ∈ Finset.range (n+1), F j * U (n-j)) = deltaG (F n)

theorem L_zero : L 0 = 0
theorem U_zero : U 0 = 0
theorem U_one : U 1 = -imaginaryUnit * gaussianEmbed S

theorem literal_riccati_coeff (n : ℕ) :
  imaginaryUnit * U (n+1) + deltaG (U n) +
    (∑ j ∈ Finset.range (n+1), U j * U (n-j)) -
    (if n=0 then gaussianEmbed S else 0) = 0

theorem U_recurrence (n : ℕ) (hn : 1 ≤ n) :
  imaginaryUnit * U (n+1) = -deltaG (U n) -
    ∑ j ∈ Finset.range (n+1), U j * U (n-j)
```

The new `LogRiccatiIdentification` module closes all orders, including zero:

```lean
theorem logarithmic_derivative_all (n : ℕ) :
  deltaG (L n) = (-imaginaryUnit)^n * gaussianEmbed (scaledH n)

theorem U_eq_scaledH (n : ℕ) :
  U n = (-imaginaryUnit)^n * gaussianEmbed (scaledH n)

theorem imaginary_logarithmic_derivative_odd (r : ℕ) (hr : 1 ≤ r) :
  deltaA (L (2*r-1)).im = (-1 : A)^r * scaledH (2*r-1)

theorem imaginary_logarithmic_derivative_odd_coeff
    (r : ℕ) (hr : 1 ≤ r) (m : Fin 2 →₀ ℕ) :
  MidpointRational.delta ((L (2*r-1)).im.coeff m) =
    (-1 : MidpointRational.QAlg)^r * (scaledH (2*r-1)).coeff m
```

The closed source/evaluation bundles are:

```lean
theorem literal_source_log_riccati_bridge (n : ℕ) :
  midpointG (F n) = sourceFCoeff n ∧
  midpointG (L n) = sourceLogCoeff n ∧
  deltaG (L n) = (-imaginaryUnit)^n * gaussianEmbed (scaledH n) ∧
  tauA (L n).im = -(L n).im ∧
  midpointA (L n).im = (sourceLogCoeff n).im

theorem literal_source_odd_log_bridge (r : ℕ) (hr : 1 ≤ r) :
  deltaA (L (2*r-1)).im = (-1 : A)^r * scaledH (2*r-1) ∧
  tauA (L (2*r-1)).im = -(L (2*r-1)).im ∧
  midpointA (L (2*r-1)).im = (sourceLogCoeff (2*r-1)).im
```

The authoritative actual `#check` and `#print axioms` output, including every
compiler-generated declaration, is `verification/fresh/logs/LogChainAudit.log`.
`declarations.json` lists the exact module-origin inventory. The existing
normalization, evaluation, linear equation, scaled recurrence and normalized
primitive results are inherited without source edits.

## Finite proof and source link

`FiniteLogChain` proves a generic statement over a commutative ring R with a
rational scalar homomorphism q and an additive Leibniz operator d that kills
q. `liftD` applies d to the coefficients. It is **not** differentiation in the
series variable. `coeff_finitePower` proves the exact identification between
the existing finite convolution powers and power-series multiplication.

For a with zero constant coefficient, `coeff_pow_vanish` proves directly by
finite convolution induction that `[z^n]a^k=0` when n<k. `truncLog q a N` is
the finite positive-power logarithm polynomial. Its coefficient below N is
proved to be exactly the original finite-log sum. Leibniz, scalar cancellation
inside the rational image, and finite geometric telescoping prove

    (1+a) liftD(truncLog q a N) = liftD(a) (1-(-a)^N).

Taking N=n+1 annihilates the remainder coefficient, giving
`finite_log_chain`. The actual source instantiation supplies all hypotheses
from `deltaG_mul`, `deltaG_one`, `deltaG_coeffEmbed`, and `F_zero`.
`literal_log_finiteLog` is definitional equality with the actual frozen `L`.
No logarithm identity or source-identification assertion is a premise.

Differentiating the proved series convolution gives
`delta² F = F (delta U + U²)`. The actual R2 is written as
`i delta F + z (delta² F - S F)=0`; its zero coefficient uses `F 0=1`.
Substituting the convolution gives F times the Riccati expression equal to
zero. `FiniteChain.cancel_zero` cancels F by induction on coefficients, using
only its constant coefficient equal to one. There is no invertibility,
no-zero-divisors, formal-log, or uniqueness premise.

Strong coefficient induction compares the resulting recurrence with the
proved concrete `scaledH_recurrence`. The product phases combine using
j+(n-j)=n, and i*(-i)=1 removes the successor phase. The odd phase is proved
with natural powers, giving the displayed sign (-1)^r in A. Taking actual
Gaussian imaginary parts and then arbitrary parameter coefficients produces
the odd identities. No zpow or spectral-variable derivative is used.

## Integration and verification

The only new proof modules to add beside the frozen root modules are:

- `FiniteLogChain.lean`
- `LiteralLogRiccati.lean`
- `LogRiccatiIdentification.lean`

The new verification modules are `LogChainAudit.lean` and
`LogChainInventory.lean`. They enumerate declarations by their actual Lean
module origin, including private/generated declarations, execute actual
`#check`/`#print axioms`, and inspect `ConstantInfo.isUnsafe`. They are audit
tooling, outside the mathematical proof-module set.

`formal-source.tar.gz` is a deterministic source-only archive. It contains no
local prebuilt artifacts. `source-manifest.json` records its input hashes.
`replay.py` extracts it into a new lane-local directory, asserts that the
extraction has no local oleans, checks the exact Lean binary SHA and mathlib
revision, and compiles the entire dependency graph sequentially. The fresh
receipt is `verification/fresh/receipt.json`, with `success: true`.

Reproduce from this lane, choosing a destination that does not yet exist:

```sh
python3 replay.py --output verification/another-fresh
```

Every compile uses the unchanged copied runners with
`-j1 -M4096 -DwarningAsError=true -DautoImplicit=false` and a sampled 3 GiB
process-tree RSS guard. There is no virtual-address-space cap. All proof logs
are empty in the final replay. The new exhaustive audit allows only
`propext`, `Classical.choice`, `Quot.sound`, and reports every new declaration
safe. The inherited source-bridge audits/inventory, filtration, midpoint,
odd-primitive audits and source checks also pass. Exact resources, hashes and
revisions are in `provenance.json` and the fresh receipt.

`component-packet.tar.gz` is the deterministic review packet, including source,
runners, manifests, exact interfaces, provenance and replay evidence.
`make_packet.py` regenerates it from the fixed files listed in its manifest.

## Frozen inputs and candid failed attempts

Every root formal Lean input was compared byte-for-byte using read-only
`git show` at commit `49cfad647f311e75ed73d3640104b3ad70c5c1f9` before copying.
The originals and lane-local copies were hashed before and after; see
`inputs-before.json` and `inputs-after.json`. Unneeded frozen modules are kept
in `inputs/frozen-root`, outside the replay dependency graph. `run_lean.py`
is copied unchanged from root; `guard.py` is copied unchanged from the prior
source component. The original `SourceDefs.lean` and all other frozen root
inputs remain untouched.

Setup first used a wrong git object-path prefix, then corrected it without
changing any input. Failed Lean incremental logs are retained under
`formal/logs`. They record an unavailable `Mathlib.Tactic.Omega` import (omega
was already available), coefficient-mk definitional reduction,
finite-sum inclusion direction, cast/map normalization, a looping `neg_pow`
simplification, overly recursive extensionality, coefficient simplification
order, Gaussian function reduction, and odd-phase coordinate simplification.
The final source contains no experiment files and all final checks pass.
An audit-preparation script initially treated `Path('.').parent` as the lane;
it was corrected to `Path.cwd().parent` before constructing the final packet.

There was one write-scope error: an authoring command omitted its working
directory and briefly created the new `LiteralLogRiccati.lean` at the workspace
root. It was immediately moved into this assigned lane, and that outside path
is absent. No existing shared source was edited. This transient write means a
claim of absolutely no writes outside the lane would be inaccurate. All final
artifacts are inside the assigned lane. Work was solo, with no child agents,
git mutations, browser/network work, external messages or ledger mutations.
