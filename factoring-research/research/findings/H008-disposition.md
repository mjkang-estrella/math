# H008 — restricted selector closed after independent review

Date: 2026-10-08. Verified factoring complexity improvement: **NONE**.

The coordinator accepts the [independent review](H008-independent-review.md)
of the [proposed thin-embedding selector](H008-resultant-selector.md).
The padded Sylvester determinant argument gives
`|Res_2(g,h)| <= 72*epsilon*H^4` even for zero outer coefficients. The strict
threshold below 1 forces a common homogeneous factor. Normalized primitive
irreducible quadratics therefore contribute at most one per embedding, and
at most d for the fixed degree-d f. The prescribed epsilon eventually satisfies
the threshold. This closes the claimed large population of new irreducible
quadratic rows from that selector.

The original W001 wording did not clearly exclude every reducible quadratic.
Consequently **do not apply the d-row bound to all its rows**. The review's
extension classifies pairwise-zero families as one irreducible, a common linear
factor family, or a three-product triangle. Linears padded to degree two can
share the factor at infinity. A common factor can leave many distinct linear
factors and corresponding relation directions.

For genuine reducibles, primitive factors have product of heights at most
sqrt(3) H; all factors lie in a linear coefficient square of size O(H²).
Common-factor groups have the exact parity relation `R=V+c*1^T`: even
dependencies carry one extra parity condition, and the possible odd coset
must also be retained. This is not a rank-at-most-d theorem. A full quadratic
cube scan costs H³ times polynomial arithmetic and does not create square-class
directions outside its ordinary bounded-height linear factors. No smoothness
probability or universal rejection of relation-based factoring follows.

The coordinator checked the determinant expansion, reversal, scale comparison,
support-set classification and parity identities. These are informal reviewed
mathematics, not Lean theorems. Frozen proposer/reviewer evidence hashes match
their manifests. No new finite experiment was run by the reviewer.

**Next:** H013 replaces the single-embedding condition with an exact global
resultant inequality and charges the full coefficient scan. It must distinguish
genuine correlated cancellation from simply using smaller-height polynomials.
That separate task is in tasks-H013.json; no successful selector is assumed.
