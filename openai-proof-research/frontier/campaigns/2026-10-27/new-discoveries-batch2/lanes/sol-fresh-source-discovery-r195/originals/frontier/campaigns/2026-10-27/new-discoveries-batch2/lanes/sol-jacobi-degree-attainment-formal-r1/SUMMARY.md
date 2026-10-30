# Degree and literal pure-u coefficient component

The assigned parameter-degree bound, Catalan top layer, rational scaling, and
literal sourceKappa pure-u coefficient formula are closed Lean components.

The integration entry point is `formal/LiteralPureCoefficient.lean`.
The final theorem is `JacobiShifted.SourceBridge.sourceKappa_pure_u`:

    ∀ r : ℕ, 1≤r →
      (sourceKappa r).coeff (Finsupp.single 0 r) =
        (catalan (r-1) : ℚ)*binomialOddSum (r-1)/(2 : ℚ)^(4*r-2).

`INTERFACES.md` lists the exact preceding degree, top-component, and scaling
interfaces. `PROOFMAP.md` describes their derivation from the actual recurrence
and literal finite source. `HONEST-GAPS.md` separates this completed component
from root's remaining all-coefficient denominator and SourceClaim work.

The five new mathematical modules compile sequentially with the unchanged
provided runner and RSS guard, -j1, -M4096, warningAsError=true and
autoImplicit=false. The declaration audit executes actual #check and #print
axioms for every module-origin declaration, including generated auxiliaries;
the inventory also checks isUnsafe=false. Only propext, Classical.choice and
Quot.sound occur. The exact reports are retained in formal/*.lean.log.

A deterministic source-only component archive is at
`packet/degree-attainment-component.zip`. Reproduce the fresh extraction using:

    python3 scripts/replay.py packet/degree-attainment-component.zip verification/a-new-empty-directory

The replay requires the locally pinned Lean binary and mathlib location in
`pins.json`. It asserts the binary SHA and mathlib revision, rejects prebuilt
artifacts in the archive, rebuilds sequentially, enforces the sampled 3 GiB
process-tree RSS guard, limits diagnostics to 512 MiB without an address-space
cap, and checks exhaustive audit coverage. The actual extracted replay receipt
is `verification/fresh/replay-receipt.json` (also copied to `replay-receipt.json`).

`provenance.json` records original and copied source hashes, including unchanged
run_lean.py and guard.py. `frozen-source-check.json` records the final comparison
against the original source paths. All writes stay within this assigned lane.
No children, git mutation, shared-ledger write, browser/account/external action,
paper, discovery acceptance, or credit claim was made.
