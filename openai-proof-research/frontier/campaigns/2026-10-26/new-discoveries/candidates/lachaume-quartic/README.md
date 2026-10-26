# Lachaume diagonal-concavity refutation

One source-question outcome: Lachaume1712.10327v1Conjecture1 / MathDB338076. The literal positive-coefficient elementary-symmetric sum f=1+2sigma1+sigma2+2sigma3+sigma4 has a globally concave fourth root on the positive diagonal, but violates midpoint concavity at strictly positive four-variable inputs. Actual C²regularity is proved.

Three modules61declarations pass fresh strict parent and independent Lean replay, standard3axioms only. The unchanged two-page manuscript and independent all-five-gate review are included. Final extracted replay/acceptance is recorded in the external packet receipt and campaign ledger; those control acceptance.

The companion sourceConjecture3 nonreal-root endpoint is UNCOUNTED known mathematics: Zaimi's2016MathOverflow x⁴−1 example, translated x→x+2, already has allpositivecoefficients and the same differential-converse failure. The preserved preliminary report's translation/positivity-range errors are corrected in parent-addendum.md and independently confirmed by the final review. Only the substantive Conjecture1 refutation receives one prospective credit. Novelty searches are bounded, no absolute priority guarantee.

Reproduction after extraction, using the pinned external toolchain/packages:

    python3 verification/verify_candidate.py . --lean-bin /absolute/path/to/lean --packages /absolute/path/to/pinned/.lake/packages
    python3 scripts/check_quartic.py

Lean4.34.1, mathlib/dependency exact commits are in verification/pins.json. The verifier builds fresh module copies, treats warnings as errors, checks all61types/axioms and rejects proof holes/new axioms. The standard-library Fraction checker supplements the proof. verification/independent-math.py is a separate optional SymPy/mpmath check. final-review-hashes.json binds current proof/paper; frozen-parent-hashes.json is a HISTORICAL earlier manuscript snapshot, not the current paper binding. MANIFEST.json binds all archive payload bytes.
