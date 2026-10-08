# H009 CRT sparse-Euclid selector v1: frozen operation, reviewed rejection

Disposition override: independently reviewed paper rejection of this literal
first-division schedule, under the asymptotic conditions in
findings/H009-first-quotient-obstruction.md. It needs Omega(B²) leading-term
iterations for all but O(B^-2) of uniform finite targets. The advertised uniform
collector's cap/yield tradeoff, including charged batch outputs, misses its
B^(3/2) per-query gate. The collector needs Theta(B) usable rows and has no extra
early-return screen; those are explicit scope conditions. No engine/pilot.
Keep the original frozen operation below for reproducibility; broader algorithms
and target-dependent shifts are not covered by this scoped result.

Proposer native Astra /root/h006_structured_relation_ideas. Root records its final
operation for independent review. No experiment, implementation or gain accepted.
Scope: classical full-range ECDLP on ordinary prime-field curves with full prime
order q comparable to p. Restrict public primes to a declared paid construction
with five pairwise-coprime B_i comparable to B=q^(1/5), N=product B_i dividing
p-1 and N comparable to q. Existence of a growing representative family and
efficient construction are assumptions, not proofs. No secp256k1 transfer.

## Executable operation and correctness obligations

Pay for factorization/subgroup generators. For declared public shifts u_i, enumerate
V_i=u_i+mu_(B_i), retain valid points and signs in a factor base of total size O(B).
Deduplicate actual points/signs correctly and charge all rejected coordinates.
The search may use the larger raw coordinate domains; invalid roots are rejected.

CRT gives a bijection mu_N -> product mu_(B_i) by
t -> (t^(N/B_1),...,t^(N/B_5)). Kernel triviality follows from the coprimality
of the B_i, and domain/codomain sizes agree. No scalar logarithm is needed here.
For each uniform-labelled target R=aG+bQ, handling infinity separately, build

    f_R(T)=S6(u_1+T^(N/B_1),...,u_5+T^(N/B_5),x(R)).

Use a sparse ordered map exponent -> nonzero field coefficient. S6 is the actual
summation polynomial, not a zero-test oracle. Its fixed-arity coefficient generation,
substitution, combining equal exponents and all constant-size-but-potentially-large
work count. Degree is O(N/B)=O(B^4); bounded initial support as q grows does not
bound intermediate support or establish feasible constants.

Compute gcd(T^N-1,f_R) by ordinary Euclid using ONLY leading-term long division:
copy dividend, find its leading nonzero term, subtract the divisor times the
leading-coefficient ratio and exponent shift, combine/delete coefficients,
repeat until degree drops below divisor, then advance the Euclidean pair.
No half-gcd, modular reduction oracle, coefficient-array scan, compressed power
or polynomial-factorization call is free. Zero f_R is a separate exceptional
case, not a constant-gcd empty output. The gcd input T^N-1 is squarefree since
N divides p-1. Normalize nonzero gcd monically, with normalization cost.

Constant gcd means no raw-grid root. Otherwise extract roots at actual gcd degree,
paying for the chosen factorization/root-finding algorithm. Map roots back to
five x coordinates, filter noncurve values, inspect signs and verify group sums.
Continue through rejected roots or count the whole capped query unsuccessful.
A constant number of coordinates/sign patterns does not make a large gcd cheap.
Relation and final scalar verification remain mandatory.

Cap exhaustion is inconclusive and a paid unsuccessful query, never emptiness.
Any later optimized algorithm is a new version with independent cost review.
The same CRT idea on a nonsplit torus N dividing p+1 is a variant, not a second
independent discovery; it needs its own extension arithmetic and extraction.

## Complete cost gate and missing claims

Let K include ALL per-query work, successful or failed: target generation,
polynomial construction, exponent comparisons/map traversal, term updates,
field arithmetic/inverses, copying/allocation, root extraction, sign/curve checks
and relation handling. Memory includes peak remainders, factor-base records,
witnesses and the relation system. Let sigma describe useful verified relation
yield INCLUDING rejected raw roots, cap failures, duplicate/dependent rows and
failure to obtain a dependency with nonzero Q coefficient. Do not infer sigma
from N~q or from low gcd degree alone.

The proposed conditional ledger is setup+~O(B*K/sigma+B²), assuming the declared
sparse linear-algebra bound and sufficient relation rank. At B=q^(1/5), need
K/sigma=o(B^(3/2)) and all other costs below sqrt(q); an exponent claim needs a
fixed power margin, not merely a finite constant. No such bound is known here.
No hidden precomputed S6 table, point inverse table or family advice is permitted.

Primary prior art: [PKM subgroup factor bases](https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf),
[Bi–Cheng–Rojas sparse finite-field root detection](https://epubs.siam.org/doi/10.1137/140990401).
Root verified the latter's stated deterministic exponent (t-2)/(t-1) for t terms;
it does not automatically give the required q^(3/10) per-query work. No novelty
claim for CRT encoding or Euclid; the application and remainder-cost hypothesis
need comparison with prior art.

Cheapest falsifier: a correctly scoped first-remainder/intermediate-update lower
bound, or a tiny independently reviewed capped diagnostic whose construction
fits the total-event cap. Degree alone is not a sparse representation lower bound.
An expensive dense engine to generate S6 is not automatically warranted.

## Other proposed routes: rejected without implementation

Exact semijoin support propagation that emits length-three witnessed prefixes
already pays Theta(B³), overlapping the H008 support materialization failure.
Locality does not provide a cheap relation producer.

For continuation with a fixed separable factor-base polynomial F(X), any formal
branch F(x(t))=0 through a simple root is constant by Hensel uniqueness. It cannot
adjust fixed factor-base coordinates to transport an arbitrary decomposition.
Allowing a fifth residual R-P1-P2-P3-P4 restores ordinary sampling: for uniform R
independent of the chosen four points, membership probability is |FB|/q, requiring
order-q trials for O(B) relations. Deforming the factor base or choosing points
dependently would change the algorithm and requires a new selector/cost argument.

Original submission status was unverified paper hypothesis. It has now failed
the named literal-operation screen above; verified improvement NONE, baseline
unchanged. No numerical pilot needed for this scoped rejection.
