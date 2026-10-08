# H028 archive-free matching and explicit complete-cost gate

2026-10-08. Native Sol reviewed the variant proposed by Opus r2; root checked
the matching, probability and straight-line arithmetic. PAPER contract only.
No execution, verified complete-work gain, calibrated throughput or novelty claim.
NEW separate Sol final-ledger review confirmed both root addition-count
corrections and the baseline-specific random-generator setup qualification.

## Exact archive-free contract

Use H019 contiguous interleaved prefixes and full deterministic caps. Pay
independent uniform s!=0,r, set G'=sG,Q'=Q+rG. Retain all nonidentity records
as full canonical h key plus scalar index. No h orientation bit or historical
center archive is needed. On insertion scan EVERY record in the matching
opposite bucket, at most once per record pair. For baby i and giant j, try both

    k = s*(jD+i)-r modq,   k = s*(jD-i)-r modq,

accepting only after checking kG=Q. Ordinary nonidentity h0 stays in the table.
Actual giantO is dispatched before lookup, with k=sjD-r. Detect identity side
outputs while full centers/offsets remain available, before discarding coordinates.
Baby0 is separately dispatched. Full point coverage and first genuine-match
prefix remain H019's; false raw matches only add work. All complete-block
computation and terminal overshoot are paid. No false solution or retry premise.

By the independently proved fibre bound and paid randomization,

    E C_raw <= 6IJ/q,  E C_false <= 4IJ/q,
    E verification scalar multiplications <= 12IJ/q.

At IJ=q/2+o(q), at most6+o(1) scalar multiplications are expected over full caps.
Each uses O(logq) group operations plus scalar arithmetic. Early-stopped work
is bounded by full-cap work. This holds for each fixed original input; no
pairwise independence is needed. There is no deterministic sqrt(q) verification
bound: an unlucky blinding can have many matches. Deadlines/restarts need
their own contract; fixed full coverage always eventually succeeds.

## Corrected arithmetic: common work must be counted on both sides

For each ordinary side pair, both kernels compute one denominator difference,
two slope numerator sums/differences and two slope multiplications.
After that the x kernel shares xsum=xC+xJ, then subtracts it from each squared
slope (3 further additions). The h kernel computes hC±hJ and subtracts slopes
(4 further additions). Thus h adds ONE field addition per pair, not saves one.
Root found a provisional reviewer count mixing common numerators on one side;
Sol agreed and withdrew it.

Canonicalizing each h costs at most one field negation and one representative
comparison. Each center h advancement adds2 field additions. For k centers
and ell side pairs per center, the conservative extra regular-block charge is

    -2kell*S + 3k(ell+1)*Af + k(2ell+1)*C,

before table differences. Here Af counts field add/sub/negate, C comparisons.
M/I terms unchanged; h's M/S/I cost per key is

    5(ell+1)/(2ell+1)*M
      + (ell+1)/(k(2ell+1))*(If-3M) + S/(2ell+1).

With slowly growing batches its limit is2.5M, versus2.5M+S for x, but that
expression alone omits important costs.

Absolute leading addition counts ALSO include the shared denominator difference:
x uses6Af/pair, h uses9Af/pair including canonicalization. Root caught that
common0.5Af/key omission from the reviewer's first absolute ledger.
Let s=S/M,a=Af/M,c=C/M; L is common per-key label/lookup/storage cost/M
and DeltaL is h-specific extra table cost/M. Then the conservative leading
weighted costs, with that common subtraction included, are

    Bx = 2.5+s+3a+L,
    Bh <= 2.5+4.5a+c+L+DeltaL.

The sufficient saving condition is s>1.5a+c+DeltaL. A sufficient10% gate is

    s-1.5a-c-DeltaL >= 0.1*(2.5+s+3a+L).

The common expected leading generated-key count is(2sqrt2/3)*sqrtq under the
H019 prefix/blinding assumptions. These are explicitly priced model conditions,
not evidence that actual a,c,L,DeltaL meet them. Ignoring these costs with s=.8
would give2.5/3.3~.758, a generation-arithmetic ratio only. Equal-cost elementary
cells do not imply a gain. Unknown table traffic is not priced at zero.

## Remaining setup, memory and validation obligations

A conservative implementation computes required initial h values through the
accepted affine Miller chain and propagates thereafter. O(k+ell) initial values
can be evaluated separately in O((k+ell)logq) group work. No unverified
projective one-inversion shortcut is adopted. Charge q inverse, random sampling,
scalar labels, strides, initial centers/offsets and verification. H019's same
point schedule controls O(ell) exceptional dispatch; identity/inverse/tangent
h updates must be explicit. Slowly growing k,ell and kell=o(sqrtq) render
these terms lower order in the stated arithmetic regime, not automatically
small at finite sizes.

Baseline fairness: exact x keys need no random-generator s for their collision
bound. A shared-s diagnostic may isolate core operations, but a complete
comparison must charge candidate-specific random-s sampling/scalar multiplication
rather than force the baseline to perform unnecessary setup. Target blinding
for an all-input expected-prefix comparison is a separate baseline requirement.

Semantic storage is O(sqrtq) full key/index records plus O(k+ell) full active
point/h data. A duplicate-preserving multimap needs real navigation/capacity
metadata. Do not equate semantic key/index fields to two physical words or
force the optimized x comparator to use redundant buckets/archives.
Identical full keys versus truncated fingerprints must be explicit; a different
baseline representation needs its own verification/recomputation accounting.
Additional cheap curve automorphisms also strengthen the relevant comparator.

This variant is distinct from the frozen first diagnostic's archive-based
one-square reconstruction. That diagnostic remains a correctness/accounting
check, not a solver race. Later complete-work evidence requires competent matched
implementations, representative increasing sizes/seeds, peak bytes, all setup,
exceptional, lookup and verification costs, and exact success/stopping semantics.
Supported generic exponent remains1/2; verified complete-work improvement NONE.

Checkpoint validation: ./scripts/check.sh > /tmp/ecdlp-h028-archive-free-check.log
2>&1 exited0,366 existing audits. No Lean/Audit claim was added. These checks
do not validate the paper cost model or the still-unexecuted diagnostic.
