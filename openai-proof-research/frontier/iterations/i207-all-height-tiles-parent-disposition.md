# I207 saved proof review and auxiliary correction

2026-10-12. **Provider failed after saving its review; independent finalization pending. Eight accepted, two remaining.**

The [saved review](../reviews/i207-all-height-tiles-proof.md) checks the all-height optimum, the nonlinear finite-cover theorem, and the functional stability bound. Its written verdict is PASS WITH EXPLICIT REPAIRS. The T3 task itself ended with `Provider turn failed.` and no terminal mathematical handoff. The original acknowledgement and later failure are both preserved in the [dispatch archive](iteration207-all-height-tiles-proof-task.json). This distinction is retained; the saved document is evidence, not a fabricated successful run.

The parent read the full review. Its explicit matrix multiplication, negative-step staircase argument, nonnormal conjugation, cutoff ordering and finite-cell count agree with the initial parent checks. Its auxiliary counterexample is valid: exchanging the two displayed representatives leaves the sparse-lattice coverage intact but loses the specified dense-lattice orbit. This flaw concerns an unused comparison paragraph, not either nominated theorem.

## Correction to the auxiliary two-lattice paragraph

In I203's analytic record, section 6, replace the unrestricted pointwise reading of the measurable-completion paragraph by the following scope:

> Starting with the cited almost-everywhere tile/packing, the measurable completion at the larger covolume covers both lattices almost everywhere. Arbitrary null-set modifications of the input need not preserve pointwise coverage. For the source's bounded finite-polytopal choice, the completion is piecewise polytopal; its closure has the same area and covers both lattices pointwise. This is the pointwise two-height consequence used for comparison.

The original author's files are retained unchanged for provenance. This addendum qualifies that auxiliary statement. Theorem 1 already has a direct pointwise construction at every real height, and Theorem 3 has its own pointwise retention proof. No periodic lower bound for arbitrary cylinder covers is asserted.

## Next gate and provenance

[I210](iteration210-all-height-tiles-proof-finalization-brief.md) receives the complete original request, saved I207 findings and this proposed repair for a focused independent finalization under the same GPT-6.1 Sol/high/ultrafast settings. [I208](iteration208-all-height-tiles-contribution-brief.md) independently assesses contribution, while [I209](iteration209-elliptic-tetrahedron-improvement-brief.md) investigates a concrete geometric consequence. No ninth finding is accepted at this checkpoint.

The saved review and literature bytes agree with their authentication ledger. The authentication file's SHA-256 is `64504c18f060d356b0182ad41006866849f7edfb49971b1efae643491e371ed6`. No source copies were added by I207. These are filesystem/provenance checks, not mathematical tests or an upstream audit.
