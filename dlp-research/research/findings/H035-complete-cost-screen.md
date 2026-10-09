# H035 complete schedule comparison for folded hashing

Status: reviewed PAPER result in the explicit model below. Root derived the
representation and integrated independent native Sol schedule accounting,
native Astra stopped-probe/cost review, and Claude Opus5.5 comparator review.
No implementation, numerical experiment, Lean theorem, novelty claim or
validated executable ECDLP improvement. The square-root exponent is unchanged.

## Accepted conditional statement

Let p and q be comparable primes, p=3 mod4, with a certified ordinary curve
and prime-order challenge subgroup. Use the same contiguous interleaved H019
schedule, uniform full-range target including zero, ideal independent hash
randomness, and no hash-dependent resource censoring. Let n=ceil(log2(q)).
The cost model has canonical modular field primitives with fixed prices M,S,A,
fixed-price record/index operations, and binary Fermat inverses costing O(n)
field operations. This last bound is stronger than merely polynomial inversion.

Set k=ellH=n² and B=k*(2ellH+1)=O(n⁴). Generate offsets and centers successively,
not by independently multiplying every center label. Both arms use the same
buffers, head counts, node capacities, null-pointer widths, and common reserved
workspace for their finitely many coefficients and hash seeds. Head/node
initialization and full-capacity release remain charged leading work.

In the shifted arm choose u uniform in Fp*, r uniform in Fp independently and
store full points X=u²*x+r, Y=u³*y. A regular paired side calculation emits

    L± = w±²-(Xi+Xj) = u²*x(Pi±Pj)-2r.

Its b-pair subtotal is (5b-3)M+2bS+6bA+I, including denominator inversion.
These side keys are not stored full-point abscissae. Full updates require
Xout=L+3r; all center/startup/exception keys require L=X-3r. Infinity remains
a separate sentinel. Doubling uses 3(X-r)²+u⁴*A as its slope numerator.
Transform/recovery/verification costs are paid, against the original input.

The schedule has E[T]=(2sqrt(2)/3)*sqrt(q)+O(1) inspected keys. Non-side keys
number O(sqrt(q)/n²), and final generation waste is O(n⁴). The remaining paid
bounds are:

| Work | Bound in the fixed-price model |
|---|---:|
| Randomness, coefficients, transformations | polynomial in n |
| Successive offset/center/stride construction | O(n³) |
| Batch inverse overhead | O(sqrt(q)/n) |
| Full-center updates and key corrections | O(sqrt(q)/n²) |
| Exceptional dispatches | O(n³) |
| Verification in original coordinates | O(n²) |
| Final-block waste and workspace reservation/release | O(n⁴) |

Every bound is o(sqrt(q)). For exceptions, all center indices span
O(sqrt(q)+n⁴)<q. For each offset a center equals ±offset at most twice;
center infinity occurs once, causing at most ellH side dispatches. Advance
exceptions are O(1). Thus O(ellH) exceptional calls at O(n) cost suffice.
The isomorphism preserves these equalities and all recovery relations.

The exact stopped-chain theorem in H035-exact-stopped-probes.md gives identical
expected fixed-price table work for full-affine and square-only shifted hashes,
conditional on the same geometric trace. Their joint laws and individual cache
traces need not agree. Separately evaluating a full-affine hash costs M+A on
each side key; therefore, with b0=2sqrt(2)/3,

    E[W_separate_affine - W_shifted] = b0*(M+A)*sqrt(q)+o(sqrt(q)).

This compares complete modeled schedules, not just kernels. A positive limiting
fraction also requires common leading costs bounded relative to M+A. It does
not establish a hardware percentage or dominance over the best available
implementation. Certification work, when required, remains common charged work;
it is not declared lower order without a separate bound.

## Competent comparator and limits

Thorup v9 Theorem3.7 proves vector multiply-shift: split the canonical key into
d v-bit limbs, let H=2^h, use intermediate width W>=v+h-1, and extract h high
bits of sum(a_i*x_i)+b modulo2^W with independent uniform coefficients.
Source: https://arxiv.org/pdf/1504.06804 . Its wide truncated products, seed
reads, additions, loops and extraction must be priced. W is not implicitly one
hardware word. Canonical key digit production may be shared with normalization.
Pair multiply-shift in the same source is Exercise3.10; this record does not
attribute a proved guarantee to that exercise or rely on it.

For any proved family with distinct-pair collision probability1/H, the
difference from square-affine beta is O(1/p). With O(q) eligible comparisons,
this is O(q/p)=O(1) expected probes. Thus a separate vector hash's actual
positive marginal fixed price c_H replaces M+A in the leading saving; no field
multiply equivalence is assumed. Its polynomial setup is paid. Under symbolic
polynomial-width prices, choose growing batch parameters explicitly large
enough to dominate the nuisance price ratios (e.g. n^(d+2) when those ratios
are bounded by C*n^d). This is an asymptotic construction, not a finite tuning.

Raw canonical bits have zero separate arithmetic hash cost. If their expected
table work has the same leading law, no positive leading arithmetic saving
remains. That expected traffic premise is unproved for the actual H019 stream;
neither its truth nor failure follows from the separate-hash comparison.
Variable-limb comparisons, normalization, cache misses, bandwidth, allocation
and resource-capped runs need additional analysis. The frozen H034 artifact
cannot test this theorem and will not be rerun.

## Reviewer disagreements retained

Opus round2 withdrew the false full-uniformity claim for class-dependent sign
folding and its universal raw-bit/word-hash dominance claims. Its raw report is
retained in H035-priorart-opus-r2-raw.md. Root accepts the vector comparator's
width contract, not its unsourced CIOS ratios, approximate7% saving, L1-residency
assurance or hardware inference. Its tabulation byte counts assume64-bit
outputs; wider bucket indices increase entry sizes. Per-root folding into a
projective conversion was not specified for the frozen affine source and is
not accepted as a free conversion.

The shared mechanism does not imply H034's relative ranking is invariant.
With gate [(1-f)b-a]*gB > a*Delta+f*z*h, a common reduction in gB changes the
margin unless the remaining terms vanish; Delta's sign and changed traffic
must be established. Conditional derivative arguments with Delta>=0 do not
prove unconditional ranking preservation. No H034 advantage follows either.
The optional p=1 mod4 Burgess sketch is unverified and unused; the accepted
theorem restricts p=3 mod4. No additional side investigation is required.

## Decision and next conclusion-changing step

Retain folded hashing as a shared baseline optimization in this model. It is
not a new collision algorithm and supplies no candidate-specific gain. No
H035 implementation or experiment is admitted on this evidence. A concrete
backend with complete normalization/table prices, or a justified raw-bit
traffic comparison, could change the practical conclusion. Independent fresh
idea generation continues separately, without anchoring all work here.

Review evidence: Sol /root/h034_c4_implementation final schedule report;
Astra /root/h007_additive_relations separate final audit accepted the equation
and corrected the inverse premise to I=O(n); Opus round2 task ID retained in
its raw report. All were read-only with no solver runs/imports/edits/children.
