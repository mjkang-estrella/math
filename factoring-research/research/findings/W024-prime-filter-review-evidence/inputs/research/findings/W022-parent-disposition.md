# W022 parent disposition

Both reports were read in full. The 22 chart-review payloads and 27 entries
of the binomial review's SHA256SUMS match their local manifests; the latter's
four certificate-freeze hashes also match. Full records are in
W022-parent-intake-hashes.json. No external full-manifest hash anchor was
supplied in the terminal summaries. No numerical certificate was rerun.
Verified new complete factoring improvement: **NONE**.

## Root charts: accept the representation, retain its real cost

Accept the signed cover for 1<=U<M and V=ceil(M/U)<M, every common-weight
valuation stratum, canonical unit residue charts, deterministic odd-prime
Hensel lifting, quartic coefficient identity, both signs, the common carry
interval, and the strict nonzero-exponent guard. Exact signed endpoints are
as in the review. In particular H>V alone does not make a combined signed
v chart a singleton; H>2V suffices, or split the signs first.

Accept the canonical occurrence bound O(M+W/M). With the specified quartic
envelope the balanced enlarged occurrence bound is

    O(M+sqrt(N/M)+M^(7/5)),

when the chosen W has the usual Theta(sqrt(MN)) scale. An arbitrary smaller
W cannot be silently replaced by that Theta scale in a domination claim.
The explicit rooted chart list costs Theta(M^(4/5)) in large balanced
ranges. Its extra carries fit the ordinary-width scale for M<=N^(5/19).
The reviewer also verifies the guard in that regime. These are representation
and envelope bounds, not a product evaluator or a new splitter.

The ordinary chart/box representation supports exact subdivision and leaf
decoding. A future evaluator still has to pay for every restricted product,
binary exponent setup, chart setup and localization. W020's recovery is
imported only under its original coverage and nonzero-exponent contract.

The unbalanced failure is substantive: for U~M,V~1 the chosen bound is
Rmax~M^(22/5), and at M~N^(1/4) its guard fails on a growing family.
A finite-small-input fallback does not repair it. This is a failure of this
particular enclosure, not a proof of a zero leaf or a lower bound on tighter
representations.

Accept b^40 and b^70 as the specified generic dense boxes, including digit
segmentation after multiplication. They are not lower bounds on all special
root-series representations. The reviewed composition misses the one-fifth
budget badly. Even hypothetical square-root evaluation repeated separately
over all charts does not suffice; aggregate sharing is an essential cost
question. The review's 4/21 aggregate target is conditional bookkeeping only.

No chart experiment ran. Existing RootCharts.lean checks only three integer
residual identities; it does not prove the cover, acquisition or complexity.
Prior art is imported within the review's stated scope: Harvey--Hittmeir's
composite-modulus stationary congruence and standard Hensel methods. No
novelty claim is adopted.

## Binomial separator: accept the semiprime identity, correct broad exclusions

For N=pq, p=3 mod 4 and q=1 mod 4, let m=(N-3)/4. Accept

    gcd(binomial(2m,m),N) in {q,N},

with the value q exactly when p does not divide
binomial((q-1)/2,(q-1)/4). In particular q<2p suffices, but is unnecessary.
The labels need not be ordered and p=3 is legal. Accept the elementary
derivative identity, Lucas proof and the cleaner low-digit Kummer proof.

For general N=3 mod 4, the review establishes a PER-PRIME divisibility rule.
Interpret its claimed product of revealed primes as radical support only:
for nonsquarefree N it has not determined the prime-power multiplicities
in the gcd. N=1 mod 4 controls do not turn the construction into an all-input
splitter. The opposite-index analog has the stated opposite low-digit rule.

The frozen certificate completed all 26 cases in 11,335 charged events,
including the full-gcd failures 87,183,791,19171. It used exact math.comb,
with results up to 9,578 bits, so it supplies no timing or scaling evidence
for a fast modular algorithm. The parent did not rerun it.

Accept the cost objections to direct exact binomials, factorial quotients,
the ratio recurrence, and use of unknown-characteristic Frobenius as a free
operation. Do NOT adopt the review's exhaustive wording that every modular
method must divide by a nonunit or reveal a factor first. The explicit
unit-safe Newton series computation in W023-single-residue-computation.md
is a counterexample to that wording. It still costs roughly linear in N,
so the review's NO IMPROVEMENT conclusion survives with a narrower reason.

The table's assertion that m! is zero modulo both primes for every N>=15
also needs a condition: m>=max(p,q) holds when min(p,q)>=5, but fails for
the p=3 mixed family (including N=15). This does not rescue modular factorial
division; its denominator is still a nonunit. It is simply not always 0/0
in both CRT components.

Known factorial/block and holonomic methods remain comparators, not evidence
that every possible unit-safe algorithm is impossible. A complete factoring
algorithm such as Harvey's one-fifth algorithm is also not a free faster
implementation of every factorial-block query. The family gcd-oracle is
equivalent to factoring that family in the stated sense; that tautological
reduction is not a complexity lower bound or a reason to reject a concrete
future algorithm.

The review's CM/ECM background is not needed for acceptance. In particular,
an elliptic group and a norm-one group having order p+1 does not make their
group structure, sampling law, or methods literally identical. Bibliographic-
only sources on point counting and elliptic pseudoprimes are not promoted
to verified imported theorems. The primary-source read scopes and retrieval
failures stay attached to the review. No exact novelty match was found in
that bounded search; no novelty conclusion follows.

## Next research action

W023 records explicit alternative computations and their costs: direct
annihilators lose to a simpler cover; small-gap folding explains some toy
witnesses; rational roots pay for their denominators; unit-safe Newton
iteration pays for its coefficient prefix. A focused independent audit of
binary-decimation degree growth is active. The parent develops coefficient
consumers and shared chart computation independently rather than waiting.
