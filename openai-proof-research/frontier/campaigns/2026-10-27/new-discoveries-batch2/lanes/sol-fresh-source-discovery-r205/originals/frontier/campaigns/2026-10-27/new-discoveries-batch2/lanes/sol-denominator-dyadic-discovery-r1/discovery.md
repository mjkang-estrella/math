# Full denominator conjecture: unresolved, with exact route obstructions

Research date: 2026-10-29 UTC. Solo assigned lane; no acceptance authority.
Counts remain 3/30 additional, 33/60 total. Credit from this lane: zero.
No full ordinary proof, counterexample to the source, Lean endpoint, or PROOF.md.

## Source, scope, and chronology

Target: Ballantine–Beck–Feigon–Maurischat, *Reciprocals of subsum
polynomials*, published Conjecture 4, Ramanujan Journal 70, article 46,
DOI https://doi.org/10.1007/s11139-026-01419-0. The actual cached published
body, Proposition 3.8 with its proof, Proposition 3.9 with its proof, and
Conjecture 4 were read. The publication date in that body is June 15, 2026.
The source is ordinary den(n,x), not the binary numerator.

For every integer n>=1, let

    P_m(x) = product_(i=1)^m (1+x^i),  P_0=1,
    D_n(x) = product_(j>=0) P_floor(n/2^j)(x).

The published Proposition 3.8 gives exactly this polynomial after regrouping.
Write D_n=sum_k a_(n,k)x^k. The full conjecture is that all internal
inequalities a_(n,k)^2 >= a_(n,k-1)a_(n,k+1) hold if and only if
n is not in {3,5,6,7}. The source already proves palindromicity and
unimodality in Proposition 3.9. Neither proves the desired inequalities.

A fresh public arXiv abstract read on this UTC date establishes the chronology:
2605.10512v1 was submitted May 11, 2026 13:04:47 UTC, and v2 on June 8,
2026 19:13:33 UTC. The fresh v2 actual HTML body retains the same Conjecture 4.
The cached v1 body was also read. Thus the target was compared to the current
source revision, not merely its old label.

Chen–Ono–Zhang, https://arxiv.org/html/2605.21718v2, was freshly body-read at
its statement of Conjecture 4 and its main theorem list. Its v1 was submitted
May 20, 2026 20:25:06 UTC; v2 May 22, 2026 04:40:20 UTC. Its ordinary
coprimality theorem and binary-numerator counterexample concern different
claims; it retains ordinary Conjecture 4 as a conjecture. The binary statement
has changed between its v1 and v2; this is not an ordinary D_n counterexample.
No previously published regrouping, convolution closure, or coprimality proof
is nominated for credit.

## Prior lane reconciliation and current-registry limits

Read root-denominator-logconcavity-r1/FINDINGS.md and every file in that lane,
including the complete 524-instance diagnostic receipt and exact code, along
with the completed sol-fresh-discrete-discovery-r6 reports and relevant primary
source/successor bodies. Root's supplied commit d6bc468904 is a handoff
identifier, not independently queried with git (git operations were prohibited).
The prior exclusions stand: generic sparse convolution fails; blocks with
at most three long P factors fail already at degree 2; arbitrary four lengths
fail, e.g. P_1^3 P_4 has coefficients 7,9,12 and determinant -3 at degree 3.
None is a source counterexample. No enlargement of the old finite sweep was run.

Fresh cached complete trees/current-head receipts in sol-fresh-analysis-
discovery-r7 were used first. Omega HEAD is
67b4fae085cf19003a33f8027410c383b49e5046 (commit 2026-10-29T04:37:11Z;
receipt 04:39:40.669289 UTC); its Problems and D5 subtree receipts are complete,
nontruncated, fetched 04:39:42.523358 and 04:39:41.417750 UTC respectively.
OpenAI HEAD is 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (Oct 26);
count-ex-machina HEAD is dbf673741a54c7dc9d88a6aec0e8148a538f4a3a (Sept 9).
Targeted filename screens of complete trees and text screens of the current
OpenAI catalogue and count registry found no exact subsum/Feigon/Maurischat/
denominator-log-concavity match. Broad partition/reciprocal filenames were
also inspected as candidates. This does not inspect the theorem bodies of
all registry files and cannot establish absence of an unnamed subsumer.

The root lane's subsequent GitHub API tree request returned HTTP429. No request
to api.github.com was made here; the fresh complete cached trees explain why
that root failure does not imply that no complete snapshot exists. They also
do not prove that HEAD remained unchanged after their retrieval. The unresolved
current-head/full-text access gap is retained. No acceptance-grade novelty
clearance or global priority assertion is made. Direct MathDB was not requested
because the preceding lane records access denial. Public web search was bounded
and did not supply a full finite-dyadic theorem; search silence is not proof.

## Exact mixed-curvature obstruction on the actual family

Extend every coefficient array by zero to all integers. Define

    Delta_a(k) = a_k^2 - a_(k-1)a_(k+1).

For b_k=a_k+a_(k-s), expansion gives the exact identity

    Delta_b(k) = Delta_a(k)+Delta_a(k-s)+C_a(k,s),
    C_a(k,s) = 2 a_k a_(k-s)
               - a_(k-1) a_(k-s+1) - a_(k+1) a_(k-s-1).

Thus a possible strategy is to prove each mixed term nonnegative on the actual
D_n family, in addition to ordinary log-concavity. This stronger strategy is
false even at the initial admissible dyadic block. Take

    A = D_8 = B_(4,8) = P_8 P_4 P_2 P_1,
    D_9 = B_(4,9) = A(1+x^9).

Exact multiplication gives (a_0,a_1)=(1,4),
(a_8,a_9,a_10)=(159,215,283). Consequently

    C_a(9,9) = 2*215 - 159*4 = -206,
    Delta_a(9) = 215^2-159*283 = 1228,
    Delta_a(0) = 1,
    Delta_(D9)(9) = 1228+1-206 = 1023.

All coefficients of both D_8 and D_9 satisfy log-concavity, checked exactly.
The failure is therefore a genuine mixed-term obstruction on the requested
sequence, not an artificial generic-convolution example, and NOT a failure of
Conjecture 4 or of root's all-order block assertions. A proof must control
negative mixed terms quantitatively against positive diagonal terms.

For the full direct recurrence, write n=2^v s with s odd and L=2^(v+1).
The previously derived identity is

    D_n = D_(n-1) sum_(u=0)^(L-1) x^(us).

For a the coefficients of D_(n-1), expansion gives

    Delta_(D_n)(k) = sum_u Delta_a(k-us) + sum_(u<v) C_(u,v)(k),
    C_(u,v)(k) = 2 a_(k-us)a_(k-vs)
      -a_(k-1-us)a_(k+1-vs)-a_(k-1-vs)a_(k+1-us).

These identities follow by separating diagonal and unordered off-diagonal terms
in the two products defining Delta; no sign inference is included. Starting
from D_8, a sufficient direct induction is the uniform inequality

    sum_(u<v) C_(u,v)(k) >= -sum_u Delta_a(k-us)

for every n>=9 and every internal k, with this exact a,s,L. That is the
remaining sign problem, not a proved invariant. It is essentially the original
inequality rewritten for the specified recurrence, and earns no credit.

## Ultra-log-concavity is also an overstrong invariant

Let t>=4 and m>=2^(t-1), and a be the coefficients of B_(t,m).
There are exactly t factors containing x and at least t-1 containing x^2.
If r is the number of layer lengths at least 2, then

    a_0=1, a_1=t, a_2=binom(t,2)+r, r>=t-1.

The first Poisson ultra-log-concavity inequality would require

    a_1^2 >= 2 a_0 a_2,

but its left minus right is t-2r <=2-t<0. This rules out that stronger
invariant for EVERY member of the four proposed families, not just at a small
sample. Normalization by binom(N,k), N=degree, requires the still stronger
first inequality a_1^2 >= (2N/(N-1))a_0 a_2 and also fails. Thus the usual
univariate homogeneous Lorentzian/Newton coefficient criterion cannot hold
for these literal coefficients. This does not exclude a different geometric
construction with additional transformations, nor ordinary log-concavity.

## Analytic route and its precise unclosed estimates

For F=B_(t,m), put m_j=floor(m/2^j). Under the probability law with mass
[x^k]F/F(1), the random variable is the sum of independent i times Bernoulli(1/2),
one for each pair (j,i), 0<=j<t, 1<=i<=m_j. Its mean is deg(F)/2 and

    sigma^2 = (1/4) sum_j sum_(i=1)^m_j i^2
            = sum_j m_j(m_j+1)(2m_j+1)/24
            = (2/21)(1-8^(-t)) m^3 + O_t(m^2).

Independence proves the exact variance formula; summing cubes gives the
asymptotic. The factors with i>1 have gaps and are not individually contiguous
log-concave probability laws. This representation supplies no closure proof.

A plain local Gaussian approximation with uncontrolled relative error is
insufficient. At three central sites the Gaussian values obey
G_0^2/(G_(-1)G_1)=exp(1/sigma^2). Perturb just G_0 to (1-epsilon)G_0.
The determinant becomes negative exactly when

    epsilon > 1-exp(-1/(2 sigma^2)).

Therefore even very small relative perturbations of order sigma^(-2) can
reverse its sign; a generic O(1/m) relative approximation is much too weak
against this central O(m^(-3)) margin. This is an exact perturbation argument,
not a claim that the actual coefficients have that perturbation. An analytic
proof must give an explicit bound for the second difference of log coefficients
(or sufficiently sharp coordinated errors), uniformly in m,k, before a certified
finite remainder can be used. No such bound or finite cutoff is established here.

For arbitrary r>0, exponential tilting gives independent parameters
r^i/(1+r^i) and probabilities p_k=a_k r^k/F(r). Since
p_k^2-p_(k-1)p_(k+1) = r^(2k)/F(r)^2 Delta_a(k), tilting preserves the sign.
It can move a desired k to the mean, but does not give a uniform large variance
near the endpoints. A central estimate still needs an endpoint argument.

There is an exact warning for fixed-depth endpoint work. For each integer K>=0,
if m>=2^(t-1)K, then modulo x^(K+1),

    B_(t,m) = (product_(i>=1)(1+x^i))^t.

Every layer contains all factors with i<=K, and factors i>K contribute only
1 to this truncation, proving the claim. Hence the four all-m block assertions
would in particular prove log-concavity at EVERY index k of the four infinite
colored-distinct partition series (take K=k+1). That necessary condition has
not been proved here, and even a proof of it would not cover moving k near
finite-layer cutoffs or the central regime. It is not asserted to be a new
open problem or a novel result.

## Validation and final obstruction

Run `python check.py` in this lane. The script uses standard-library exact
integers and rationals, a hard 512MiB address-space cap, a 30-second CPU cap,
and one BLAS/OpenMP thread. It validates the mixed-term identity at all indices
of two prescribed dyadic blocks and one small input, retains the exact -206
witness and old -3 witness, checks only source base cases n<=9, and checks the
first-coefficient/variance formulas on the initial block of each proposed
family. Four fixed degree-six truncations check the endpoint-stabilization
formula. These are algebra diagnostics, not a new large all-parameter sweep
and not a proof of any infinite family. checks.json records the execution UTC.

Strongest objection: neither a bound on the combined mixed terms nor a uniform
second-difference estimate was obtained. The one-step identity is a reformulation,
and the rigorous auxiliary obstructions do not settle or count toward the
source. No all-m block assertion has been falsified here. No certified finite
range can fill an absent infinite-range theorem. Conjecture 4 remains unresolved
in this lane, with no nomination and no formalization started.
