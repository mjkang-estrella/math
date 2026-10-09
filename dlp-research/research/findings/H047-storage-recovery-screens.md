# H047 residue payloads and filter-tree recovery: no matched gain

2026-10-09 UTC. Two executable paper constructions, independently reviewed.
Neither supplies a credible complete-work gain or an admitted experiment.
Current exponent1/2; verified improvement **NONE**.

## Residue payload followed by exact bounded search

For babies x(iG), 1<=i<=b<q/2, store an approximate-membership structure and
a retrieval payload r=i mod d, 1<=d<q. The baby abscissae are distinct under
this range condition. Store a correctly prepared beta-entry exact subtable for
H=dG, also of order q. For a filter pass, reconstruct the actual full query
point R. Validate r as an encoding of an integer in [0,d), then search BOTH
orientations sigma=+/-1 for

    sigma R-rG=jH,
    ceil((1-r)/d) <= j <= floor((b-r)/d).

An empty interval or invalid payload rejects. For r=0 the first index is 1,
not 0. Correct BSGS padding and any signed abscissa subtable must check final
integer bounds and signs. A genuine member has a unique valid orientation
because b<q/2. Set i=r+dj. If R=aG+cQ and c!=0 modulo q, recover
k=(sigma i-a)/c and verify kG=Q. A zero c is not a scalar recovery.

A nonmember may receive ANY retrieval payload. Exhaust the returned valid
interval or otherwise prove rejection; do not mistake payload production for
membership. With prepared shifts and the exact subtable, both orientations
take O(ceil(b/(d beta))+1) group/query steps in this explicit resolver.
Generating rG, full-point reconstruction, exact lookup, range checks and final
verification remain additional, as do all setup, labels and scratch costs.

In a simple retained-bit model, put V=max(1,b/(d beta)) and select fingerprint
error of order 1/V to bound unsuccessful-resolution work per nonmember query.
Before rounding and constant overhead, payload plus fingerprint bits are

    log2(d)+log2(V)=log2(b/beta)  when b/(d beta)>=1.

Thus the factor-d resolver reduction spends this model's fingerprint saving
on payload. Beyond the V=1 floor, payload bits continue increasing. This is an
accounting identity for the encoding, NOT a universal storage lower bound or
a finite performance comparison. Include beta exact records, retrieval build
failures/rebuilds, seeds, filter construction and peak temporary storage.

The false-work calculation needs a declared guarantee on the actual query
distribution. A fixed full-cap nonmember stream independent of filter seeds
supports a linearity-of-expectation upper bound. Adaptive/repeated queries do
not automatically have a fresh conditional error probability after observations.
A correct deterministic cap or seed-aware stopping argument cannot be omitted.

## Independent-node binary filter descent

Build separate filters for a binary hierarchy of baby-index intervals. The
path to a leaf supplies its index. Explore children only after a node passes;
at leaves exactly check the candidate point and recover/verify the scalar.
With independent node seeds, fixed seed-independent nonmember query, and
nonmember pass probability at most rho<1/2, a fresh false subtree has at most

    1+2rho+(2rho)^2+... = 1/(1-2rho)

expected tested nodes. This counts filter tests, not total bit/group work.
A true member retains its genuine path and also explores false sibling
subtrees: expected tests are O(log(b)/(1-2rho)), not constant. Exact leaf
verification needs a stored exact key or paid point reconstruction; it is not
free merely because the path identifies an index.

The separate-filter implementation represents b memberships at each level,
so fixed-error filters take O(b log b) bits before seed/address metadata and
construction scratch. Generating or retaining keys at all levels is paid.
Compare against H030-hierarchy-scope.md's aligned, translated, reusable child
filters and conditional O(b)-bit envelope, including its own lookup, successful
path, alignment, seed and field-hash costs. That comparator is not an
unconditional optimum or a claim of measured speed.

## Source, independent review and decision

Native Sol /root/h034_c4_implementation proposed both constructions after an
independent initial search. Native Astra /root/h007_additive_relations reviewed
exact integer intervals, signs, false-tree branching, true paths and costs.
Root checked the equations, floor regime, branch recurrence and H030 comparator.
Sol and root freshly read [Dietzfelbinger–Pagh, sections 1.1–1.3](https://www.rasmuspagh.net/papers/bloomier.pdf):
retrieval allows arbitrary nonmember payloads; its RAM/hash/universe and
construction assumptions accompany any imported bound. This source does not
supply an ECDLP speedup or a construction-peak exemption.

No new complete operator with a credible matched advantage emerged. Retain the
options and qualifications, but do not launch a storage microbenchmark without
a favorable complete-solver invoice against competent layouts and the aligned
hierarchy. No generic optimality or impossibility result is claimed.
No experiments/imports/scripts, seeds, curves, Lean claims or Audit additions.
H034 cap unchanged; exact project check and result in STATE. The paper proofs
and conditional costs are not certified by compilation.
