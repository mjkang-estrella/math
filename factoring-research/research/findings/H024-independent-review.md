# H024 independent symbolic review

2026-10-08. **ACCEPT the five claims within the scopes stated below.** No
mathematical correction to equations (1)–(10) is required. The probability
statement is accepted only as a conditional implication, with the explicit
quantifiers below; no law for the actual residuals has been established.
Verified full factoring complexity improvement: **NONE**.

I read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, both H024 documents in full, and the
accepted H021 construction, independent review, disposition and hypothesis.
This review concerns the submitted H024 report with SHA256
`8f510430d375c2dcc41507f583436edff5978eb3fbbb084402ffadf27323b5c8`.
An exact copy is preserved as
[H024-review-submitted-draft.md](H024-review-submitted-draft.md).

Other mathematical input hashes:

- H024 hypothesis: `976a50a5fcffe961270f0985927216f8536ebcf45cfcfe3f932d981eade7c5ad`.
- Accepted H021 construction: `655afec1540a6f59099ceef793dd0687405111540b84ee55db8854a9fc26131a`.
- H021 review: `fbf77260be74592643de25ac35655d5d1f94d3d4896f3ba46e123b01cfed3221`.
- H021 disposition: `60b8b96b2140658e9b9ad32ac2fad06a381d228425ee76f1dbcb8681a68ad9cd`.

This was a paper-and-pencil audit. File reading, copying and hashing were the
only nonauthoring operations. No mathematical executable, numerical check,
sample, sweep, benchmark, implementation, package, Lean refinement, delegation,
commit, publication or scheduler was used. Only this review and its adjacent
submitted-report copy were written. STATE and the parent report were not
edited. H022's model analysis and the live H023 construction were not reopened.

**1. Feasible cutoff and global-optimizer coverage — ACCEPT.**

The accepted objective is

    F(e) = sum_j f_j² e_j² + (sum_j a_j e_j - T)²,
    f_j = ceil(j/2), k = ell = bit_length(N), N > 1.

Here ell >= 2, ell <= C < 10ell and C >= 10. H021's certified errors imply
a_1 >= C log 2 - 1 > 0 and T >= C log N - 1 > 0. Thus the integer formula

    r = floor((2T+a_1)/(2a_1))

is defined and rounds T/a_1 to a nearest integer, with upward rational ties.
Consequently |a_1 r-T| <= a_1/2 and |r| <= T/a_1+1/2. This does not require
deciding a true-logarithm rounding tie: a_1 and T are already exact integers
from H021's specified changed rounding rule.

For an explicit bound covering every small input, use 1/2 < log 2 < 1:

    a_1 >= C/2-1 >= 2C/5,
    a_1 <= C+1 <= 11C/10,
    T < C ell+1,
    |r| <= (5/2)ell + 5/(2C) + 1/2 <= 3ell.

It follows, without an asymptotic small-input exception, that

    0 < E_star = r²+(a_1 r-T)²
      <= 9ell² + 121C²/400
      < (157/4)ell² < 40ell².                              (R1)

Positivity follows because F(e)=0 would force e=0 and T=0. The bounds on r,
a_1 and T also show that computing r and E_star from those supplied
coefficients needs only O(log²(ell+2)) schoolbook bit work. Constructing the
coefficients and reading N are separate, paid operations.

The vector e_star=(r,0,...,0) has exactly the displayed energy because f_1=1.
It belongs to the finite box |e_j| <= floor(sqrt(E_star)/f_j). Outside that
box a diagonal summand already exceeds E_star. Minimizing on the nonempty
box therefore proves both existence of a global minimizer and inclusion of
every global minimizer, without presupposing existence.

H021's corrected recovery rule applies: the box minimum is at most E_star,
so the capped suffix table can recover it by following minimizing
transitions. Uncapped prefix predecessors remain valid as well. This does
not revive the false general recovery claim for a box whose minimum exceeds
its cap. Following an arbitrary accepted suffix path would enumerate a
feasible vector, not necessarily an optimizer.

The bound is sufficient, not an assertion that r minimizes even the
one-coordinate quadratic. It preserves every global optimizer, not every
useful higher-energy vector. Those distinctions in the parent report are
correct. No required fix; (R1) is an optional explicit replacement for the
uniform O(ell²) estimate.

**2. Ranges, widths, preprocessing, memory and runtime — ACCEPT in the
declared models.**

Write g=log(ell+2). Since each positive integer weight occurs at most twice,

    sum_{j<=ell} 1/f_j <= 2 sum_{m<=ceil(ell/2)} 1/m = O(g).

With sqrt(E_star)=O(ell), this proves sum R_j=O(ell g) and
L=k+2 sum R_j=O(ell g). The accepted prime bound gives
max_j |a_j|=O(ell g), whence S=O(ell²g²) and Q=O(ell²g²).

H021's complete width b is O(g). In particular it covers kE_star, signed
shifts, sums outside a row during range tests, terminal squares as large as
(S+|T|)², all f_j, and addresses into the kQ tables and length-L lists.
These DP operands have O(g)-bit widths. Reading N and the rational logarithms
require larger operands and belong to setup.

Substitution in H021's exact bound yields

    O(kb³+(L+Q)b²+QLb) = O(ell³g⁴),
    rolling values and lists: O(ell²g³) bits,
    all prefix predecessors or suffix rows: O(ell³g³) bits,
    exponent-vector enumeration delay: O(Lb)=O(ell g²).

Two rolling value rows alone do not provide the stated predecessor recovery
or enumeration. Full retained rows/predecessors pay the larger storage.
The delay includes first output, interoutput gaps and final exhaustion, after
preprocessing; constructing u,v,w or imposing a useful-relation filter is
additional. No delay guarantee for outputs passing such a filter follows.

H021's unchanged trial-division setup remains O(ell⁴g²). The suggested sieve
is a correct replacement: a composite i has a smaller prime divisor whose
earlier marking loop has marked i, while a prime is never marked by a smaller
integer. The existing accepted prime bound makes U=4(k+1)² sufficient for the
first k primes. This is the only prime-distribution input; the loop-cost
argument does not assume any density estimate for primes.

The outer loop has U iterations, and the marking count is bounded by

    sum_{i=2}^U floor(U/i) <= U sum_{i=1}^U 1/i = O(U log(U+2)).

O(log(U+2))-bit indices, increments, comparisons and charged indexed bit
access give O(U log²(U+2)) time. The array uses O(U) bits; counters and the
retained first-k-prime list cost O(log U+k log U) further bits, within this
scale. Initialization is included. Declaring primes after the first k need
not retain them. On sequential tapes, even rescanning the entire array for
every access, with counter work charged, costs O(U² log²(U+2)); this is
O(ell⁴g²), below the displayed conservative DP bound.

For rational logs, the largest input width among N and p_1,...,p_k is O(ell),
including small ell. H021's series length is n=O(g), and its unreduced
rational intermediate width is d_x=O(ell g²). Using that largest width for
all k+1 logs gives

    (k+1) O(n d_x²) = O(ell³g⁵).

This deliberately loose bound is valid for the already specified incremental
power generation and rational addition. It does not substitute the DP's
O(g)-bit width for the larger log operands. Forming C, generating weights,
reading N, and constructing the cutoff are included or dominated. Optional
primorial construction and its conservative gcd costs also fit within this
scale if performed; neither is necessary for the optimizer.

Thus setup plus one exact optimizer costs O(ell³g⁵), or tilde-O(ell³), with
the explicitly charged indexed memory. H021's conservative table scan
factor O(1+kQ+L)=O(ell³g²) instead gives O(ell⁶g⁶) for the DP on its stated
multitape realization. This pays table addresses and payload scans rather
than granting unit-cost random access. It is a mathematical construction,
not an implementation, CPython timing claim or formal machine refinement.

Counting is a different runtime scope. For example, retaining H021's loose
beta=O(k log(E_star+2))=O(ell g) count width gives

    T_count = O(T_init+Q(E_star+1)L(b+beta)) = O(ell⁶g⁴),
    all count rows: O(kQ(E_star+1)(b+beta)) = O(ell⁶g³) bits,

with its further stated access factor on sequential tapes. These are
sufficient loose substitutions, not claims of optimal counting complexity.
The population proof below evaluates no count table and does not make that
algorithm cubic. Likewise the one-optimizer bound does not include printing
all low-energy vectors or testing arbitrary numbers of dependencies.
No required fix to the parent's ledger.

**3. Width of actually accepted integer outputs — ACCEPT.**

For q(e)<=E_star, Cauchy–Schwarz gives

    sum_j |e_j| log p_j
      <= sqrt(q(e)) sqrt(sum_j (log p_j/f_j)²).

The accepted estimate p_j=O(j log(j+2)), together with f_j>=j/2, bounds the
second sum by a constant multiple of sum_{j>=1} log²(j+2)/j². That series
converges, so its partial sums are bounded independently of k. The first
factor is O(ell) by (R1). Both positive and negative exponent contributions
are bounded by the same sum. Therefore u and v have O(ell) bits; multiplying
v by N adds ell bits, and |u-Nv|<=max(u,Nv) gives the same bound for |w|.
The sign and the conventional representation of zero add only constants.

The wider Cartesian box can contain vectors not satisfying q<=E_star; this
sharper width claim is for accepted vectors. Powers and partial products can
be formed within the actual output widths using H021's paid powering
procedure. Even the loose dense exponent cost B_e=O(ell g) gives
O(ell³g) schoolbook work to materialize one accepted u,v,w, so one such output
does not invalidate the optimizer setup bound. Retained outputs are additional
storage and all requested outputs must be paid for.

This is exclusively an upper size bound. It supplies neither a lower bound
on |w| nor a distribution for it. In particular it does not rule out |w|=1,
much smaller residuals than the upper bound, or w=0. No required fix.

**4. Uniform theta-product population bound — ACCEPT, including constants.**

For finite k, E>=0 and s>0, nonnegative summation gives

    M_k(E) <= exp(sE) sum_{e in Z^k} exp(-s q(e))
            = exp(sE) product_{j<=k} theta(s f_j²).

Here theta(t)=sum_{n in Z} exp(-tn²). Each one-dimensional Gaussian series converges;
factorization is justified by nonnegative sums. Since every weight occurs at
most twice and theta>=1, this product is at most the infinite product in
the parent report once convergence of that product has been established.

Put h(x)=log theta(x²) for x>0. Termwise comparison shows that h is positive
and decreasing. For every finite J and a=sqrt(s), monotonicity implies

    a sum_{m=1}^J h(ma) <= integral_0^(Ja) h(x) dx.

The bound near zero is legitimate: comparison of the decreasing Gaussian
with its integral gives

    theta(x²) = 1+2 sum_{n>=1} exp(-x²n²)
              <= 1+sqrt(pi)/x <= 3/x        (0<x<=1).

Thus integral_0^1 h <= log 3+1 < 3. For n>=1,
n²-[1+3(n-1)]=(n-1)(n-2)>=0. Consequently, for x>=1,

    theta(x²)-1 <= 2 exp(-x²)/(1-exp(-3x²)) <= 3 exp(-x²).

Using log(1+y)<=y and x²>=x gives
integral_1^infinity h <= 3/e < 3/2. Therefore the full integral is less
than 9/2. The finite-sum comparison bounds all partial sums of
sum_m h(m sqrt(s)) by this integral divided by sqrt(s); their monotone
limit is finite. This justifies convergence of the infinite product before
using it as a finite upper bound. Its logarithm is less than 9/sqrt(s),
and hence at most 10/sqrt(s), exactly as needed.

Taking s=E^(-2/3) for E>=1 proves

    M_k(E) <= exp(11 E^(1/3)), uniformly over every finite k. (R2)

For E=0 only the zero vector has q=0, so M_k(0)=1. Since F>=q, the exact
accepted F-population satisfies (R2) as an upper bound. Combining with (R1)
even gives the explicit, deliberately loose bound

    1 <= #{e:F(e)<=E_star}
       <= exp(11 * 40^(1/3) * ell^(2/3)).                    (R3)

The lower bound 1 here is merely feasibility. There is no matching lower
population theorem, density estimate, or relation-rank assertion. The
argument counts integer points directly and never infers their number from
real ellipsoid volume. Uniformity in k applies with the stated multiplicity
of weights, not arbitrary diagonals; a permutation preserves the count.
The feasible cutoff in claim 1 specifically used f_1=1.
No required fix.

**5. Conditional useful-supply implication — ACCEPT as an implication only.**

The parent's conclusion follows from a separately proved, strategy-valid
rarity law. The following precise formulation makes its requirements and
its limitations explicit and can be inserted into section 4.

Fix ell and a probability space specifying the input distribution, if any,
and every random choice of the actual strategy. Inputs have bit length ell.
Alternatively fix N and randomize only the strategy. Put

    B_ell = ceil(exp(11 * 40^(1/3) * ell^(2/3))),
    p_ell = exp(-kappa ell), with fixed kappa>0.

The strategy processes at most B_ell distinct vectors from its actual
S_N={e:F_N(e)<=E_star(N)}. Pad its stopped execution with zero-yield steps.
Let Y_t be the indicator of the specified new useful event at step t, zero
when no attempt occurs. The event must be defined, including what counts as
new and how retained rows or dependencies affect it. More general
nonnegative integer yields are allowed only with an expectation bound on
the whole yield, not just a probability bound for one of several events.

Let G_t be the actual preattempt information, including earlier outcomes,
the current state, stopping decision, and the chosen sampling policy. Any
information already used to choose that policy belongs in G_t. If the
attempt draws a fresh random vector, this filtration can be taken before
that draw. The extra hypothesis is, almost surely on every relevant history,

    E[Y_t | G_t] <= p_ell * 1_{attempt t is active}.          (R4)

The constants and inequality must hold uniformly over the histories and
input instances in the scope of the claimed law. Summing conditional
expectations gives

    E[sum_t Y_t] <= p_ell E[number of active attempts]
                 <= B_ell p_ell
                  = exp(O(ell^(2/3))-kappa ell).

Markov bounds P(sum_t Y_t>=1) by the same quantity, which tends to zero.
No independence or optional-stopping theorem is needed. A directly proved
aggregate expectation bound for this actual strategy is an alternative to
(R4). A law for one selector does not automatically apply to exhaustive
enumeration or a different selector. The phrase "even examining all vectors"
requires the law to remain valid for that exhaustive strategy.

The probability space and filtration matter substantially. For fixed N and
chosen e, u,v,w and their smoothness are deterministic. If conditioning
includes both N and the selected e and usefulness is determined by these
and the retained history, its conditional probability is zero or one. A
bound strictly below one would then exclude every useful selected vector;
it cannot be justified by treating unevaluated arithmetic as fresh random
noise. A nontrivial fixed-input sampler law must average over its actual
next draw, conditional on prior history. A random-input aggregate law must
name the input distribution and yields only that distribution's conclusion.
It does not become a worst-case statement for every composite N.

In particular, exhaustive enumeration for a fixed deterministic N finds
all of its accepted vectors. If a useful one exists, an exhaustive law
forcing expected total yield below one cannot hold for an integer-valued
deterministic total of at least one. This exposes the strength of the missing
hypothesis; it is not evidence that the hypothesis is true. Unconditional
smoothness density under a uniform draw is insufficient to establish (R4)
after adaptive selection, rejection of previous failures or stopping.

Counting distinct vectors bounds distinct vector attempts, not repeated
draws, repeated processing of one vector, or all combinations of already
obtained relations. Those operations and any multiple yields require their
own accounting. Injectivity into ordered pairs (u,v) also does not prevent
duplicate residuals or parity rows.

Equation (R3), by itself, is compatible with zero, one, polynomially many,
or a much larger number of useful vectors, subject to its upper bound.
Random-integer smoothness estimates would require a justified transfer to
these structured residuals. The O(ell) upper output width supplies no lower
size condition for such a transfer. Small or zero residuals, favorable
inputs, correlations and selection based on arithmetic information may
invalidate the proposed rarity law. For w=0, H021 correctly gives v=1 and
N=u supported on the factor base; zero is not an ordinary parity relation.

No probability theorem is silently adopted in accepting this implication.
There is no required mathematical correction, but inserting the formulation
above, or a shorter version specifying the same probability space and
filtration, would prevent a stronger interpretation of section 4.

**6. Stronger interpretations — REJECT.**

None of the accepted claims proves inverse-polynomial useful density,
exponentially small actual useful density, sufficiently many distinct usable
rows, the needed parity/dependency structure, proper splitting, or an
end-to-end factoring runtime. A cubic optimizer is not a cubic factoring
algorithm; an upper count is not a factoring obstruction. Successful
preprocessing or another factoring branch is not ruled out even by a
conditional failure statement for these vector attempts. There is also no
lower bound against all selectors, other cutoffs, other scales or bases.

The object remains H021's original exponent-coordinate objective with its
bounded-error rational-log coefficients. The post-LLL affine binary domain
and the perturbed tensor-network sampling distribution are distinct, as
already documented and reviewed in H021. Nothing here transfers the count,
delay or probability statement to them. This review uses H021's accepted
source and prime-bound premises and makes no new primary-literature or
novelty claim.

**7. One sharp next supply question, and disposition.**

A first concrete supply question is: does there exist a fixed A>0 such that,
for every sufficiently large composite N coprime to product_{j<=ell} p_j,
at least an ell^(-A) fraction of S_N has a nonzero residual whose absolute
value is p_ell-smooth? Here S_N uses exactly this cutoff and coefficient rule,
and smooth means all prime divisors are <=p_ell, including |w|=1. This is
a deterministic density question, equivalently a statement about H021's
uniform sampler; no random-integer law is assumed. The coprimality restriction
isolates the branch after small-prime factors have been excluded and also
rules out zero residuals. Even a positive answer would still leave novelty
of rows, adaptive yield and proper splitting to prove.

This supplies a named missing lemma rather than an implementation project.
No optimizer infrastructure or experiment is justified by the present
upper-count result alone. Accept the cutoff, model-qualified costs, output
width and theta-product bound; retain the useful-supply claim solely as the
conditional implication in item 5. No shared edits or Lean work are needed
for this disposition. Verified full factoring complexity improvement remains
**NONE**.
