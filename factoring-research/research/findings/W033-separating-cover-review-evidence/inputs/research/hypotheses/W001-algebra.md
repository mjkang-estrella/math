# W001 — Algebraic representations and zero-divisor mechanisms

Date: 2026-10-07 America/Los_Angeles. Bounded independent ideation pass.

**Verified factoring time-complexity improvement: NONE.** The strongest result of
this pass is an elementary coefficient identity and a scoped reduction from
factoring to a precisely specified coefficient-extraction primitive. Its
efficient implementation is missing. Four distinct mechanisms follow; none is
claimed novel on the basis of this literature search.

Read: `AGENTS.md`, `docs/SPECIFICATION.md`, `RESEARCH_LOOP.md`, `README.md`, and
the required checkpoint. The checkpoint's placeholder was not used as a
hypothesis. This report and the named adjacent scratch checker are the only
outputs. No shared solver, Lean, state, other research output, or infrastructure
was changed; no delegation or publication was performed.

## Accounting and comparisons

Let n = bitlength(N), R = Z/NZ, and M(n) denote n-bit multiplication cost.
All ring coefficients are reduced modulo N; products temporarily use O(n) bits.
An exponent with O(n) bits is cheap to **store**, but a polynomial of degree N is
not. A trial with cost T and independent success probability s has expected
restart cost T/s; a bounded r-trial version can fail with probability (1-s)^r.
When s has no positive bound, no finite expected-time guarantee is asserted.
The cards mainly analyze distinct odd semiprimes N=pq. Easy even/perfect-power
preprocessing does not extend their proofs to every composite.

Relevant baselines are different claims:

- Harvey–Hittmeir give a rigorous deterministic bound with exponent 1/5 in N,
  hence 2^(n/5+o(n)) bit cost. Beating an N^(1/4) toy baseline is insufficient.
  [Primary paper](https://arxiv.org/abs/2105.11105).
- Class-group relation factoring already has a rigorous expected
  L_N[1/2,1+o(1)] bound, where L_N[a,c] =
  exp((c+o(1))(log N)^a(log log N)^(1-a)). This is the relevant baseline for
  Card C, not exhaustive search.
  [Lenstra–Pomerance](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/rigorous.pdf).
- A general classical improvement must also be compared with the customary
  heuristic GNFS scale L_N[1/3,(64/9)^(1/3)], not just deterministic exponential
  bounds. This is a comparison scale, not a claim about the best constant among
  all variants. [Buhler–Lenstra–Pomerance, primary chapter](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/1993_Book_TheDevelopmentOfTheNumberField.pdf).
  Lee–Venkatesan rigorously analyze square-congruence production by randomized
  NFS variants; that result must not be silently upgraded to a proof that every
  congruence yields a proper factor.
  [Primary paper](https://arxiv.org/abs/1805.08873).

## Card A — Composite-index Hasse coefficients with translated CM curves

**Primitive and algorithm.** For an odd positive integer v and an integral cubic
f, define

    C_v(f) = [X^(v-1)] f(X)^((v-1)/2).

Choose t uniformly modulo N, construct f_t(X)=(X+t)^3-(X+t), compute
C_N(f_t) modulo N, and take gcd(C_N(f_t),N). Accept only a proper factor.
All curve generation takes O(M(n)) bit work and O(n) storage. No point counting,
unknown characteristic, modular square root, or factor is supplied to this
algorithm. **Fast extraction of the coefficient is the unsupported primitive.**

**Concrete identity, with proof.** For distinct odd primes p,q and deg f≤3,

    C_(pq)(f) ≡ C_p(f) C_q(f) (mod pq).                 (A1)

Indeed, (pq-1)/2 = (p-1)/2 + p(q-1)/2. Modulo p, the freshman's-dream identity
gives

    f(X)^((pq-1)/2)
      = f(X)^((p-1)/2) f(X^p)^((q-1)/2).

To contribute to X^(pq-1), an exponent from the first factor must be p-1
modulo p. Its degree is at most 3(p-1)/2 < 2p-1, so the only possibility is
p-1. This proves the product congruence modulo p. Interchanging p and q and
applying CRT proves (A1). The proof uses the factors only to analyze an
algorithm whose input is N. No claim of a new identity in the literature is made.

**Useful scoped separation lemma.** Suppose

    3 < p < q, p ≡ 3 (mod 4), q ≡ 1 (mod 4).

Then the algorithm returns p with probability at least

    1 - (p-1)/(2q) > 1/2.                             (A2)

Here is a direct proof, avoiding an assumed invariant oracle. For any odd prime
l, translating a cubic leaves C_l modulo l unchanged: the extra terms involve
binomial(k,l-1) for l≤k≤3(l-1)/2<2l-1, and these vanish modulo l. Thus
C_p(f_t)=0 modulo p. For q≡1 mod 4,

    C_q(X^3-X) = (-1)^((q-1)/4)
                  binomial((q-1)/2,(q-1)/4) ≠ 0 (mod q).

Put m=(p-1)/2, which is odd. C_p(f_t), viewed as a polynomial in t over F_q,
has degree at most m. Its coefficient of t is

    (-1)^((m-1)/2) p binomial(m,(m+1)/2).

This is nonzero modulo q because q>p and every prime divisor of the binomial
coefficient is at most m. Hence at most m values of t modulo q are roots.
Equation (A1) now proves (A2). Two independent trials give success >3/4 on this
family. If q>3(p-1)/2, a single trial has success >2/3.

**Important failure controls.** At t=0, C_N(X^3-X) is literally zero when
N≡3 mod 4; the apparently ideal CM invariant then kills both components.
Translation is essential. If both p and q are 3 mod 4, (A1) shows C_N(f_t)=0
modulo N for every t. This exact obstruction rules out this one curve family
as an all-input splitter; it does not rule out other algebraic constructions.

**Complete cost and proposed gain.** Write T_coef(n), S_coef(n) for the full
time and peak bits required to compute the stated coefficient, including any
preprocessing. On (A2)'s family the expected total cost is

    O(T_coef(n) + M(n) log n + n),
    peak space O(S_coef(n)+n), expected random bits O(n).

Thus a uniform polynomial-time extractor would give a polynomial expected-time
splitter on this family; an extractor of cost 2^(alpha*n+o(n)), alpha<1/5,
would beat the cited deterministic exponent **on this family only**. Any fixed
positive alpha still loses asymptotically to the GNFS subexponential scale.

The actual scratch implementation repeatedly multiplies by the cubic, taking
O(N^2 M(n)) bit work and O(Nn) bits of coefficient storage. Standard fast dense
polynomial powering can reduce this to roughly soft-O(N M(n)), still
exponential in n. Neither is an improvement. Exact integer coefficients need
up to O(Nn) bits, so computing them over Z before reduction also loses.

**Prior art and actual distinction.** Hasse/Cartier–Manin coefficients and
polynomial-coefficient recurrence acceleration are established machinery.
Bostan–Gaudry–Schost obtain square-root-characteristic-scale Hasse–Witt
computation and also treat integer factoring. Their field result is not a free
unknown-composite-characteristic oracle.
[Author-hosted primary paper](https://mathexp.eu/bostan/publications/BoGaSc04.pdf).
Doliskani–Narayanan–Schost already separate polynomial factors by vanishing
CM Drinfeld-module Hasse invariants over a **known** finite field.
[Primary paper](https://arxiv.org/abs/1712.00669).
Harvey–Sutherland compute invariants modulo all primes up to a bound in average
polynomial time per prime; generating that whole range is not polynomial work
for one hidden prime of size about sqrt(N).
[Primary paper](https://arxiv.org/abs/1402.3246).
The specific research object here is the translated, composite-index
coefficient (A1), not a claim to have invented vanishing-invariant factoring.

**Cheapest falsifiers and disposition.** A counterexample to (A1)/(A2) rejects
the structural reduction. Those checks survived the small screen below. Any
purported fast extractor must expose its degrees, coefficient widths, and
nonunit divisions. Calling Schoof at p, choosing a p-adic expansion, or using
the factors to select a characteristic is circular. Retain as a **focused
coefficient-computation question**, not as an efficient factoring candidate.

## Card B — Quadratic quotient norms and characteristic-free rank defects

**Algorithm.** Draw b,c uniformly modulo N. In the rank-two algebra
A=R[X]/(X^2+bX+c), compute h=X^N-X=s+tX using binary powering. The
multiplication matrix of h is

    H = [[s, -ct], [t, s-bt]],
    det(H) = s^2-bst+ct^2 = Res_X(X^2+bX+c, X^N-X).

Take gcd(det(H),N). When this is N, test gcd(N,s,t) to distinguish a zero
operator on one component from a nonzero singular operator on the other.
These are explicit, division-free constructions; no roots of the quadratic
are requested. Sampling costs O(n) bits; powering costs O(n M(n)); extraction
costs soft-O(M(n)); memory is O(n). Thus the hoped-for gain is polynomial
total time if the local rank mismatch probability is inverse polynomial.

**Exact local falsifier.** For a prime l dividing a squarefree N, set

    a_l = 1 + gcd(N-1,l-1),
    b_l = 1 + gcd(N-1,l^2-1).

The polynomial X^N-X is squarefree modulo l. It has a_l linear roots and
(b_l-a_l)/2 irreducible quadratic factors. A uniform monic quadratic therefore
shares a factor with it with exact probability

    pi_l = a_l/l - a_l(a_l-1)/(2l^2) + (b_l-a_l)/(2l^2).     (B1)

Proof: use inclusion–exclusion for its a_l possible linear factors; each
specified linear factor occurs with probability 1/l, each pair with 1/l^2.
Each specified irreducible quadratic occurs with probability 1/l^2. These last
events are disjoint from all linear-factor events.

For N=pq, CRT makes the two local quadratic draws independent. The determinant
alone succeeds with exact probability

    s_det = pi_p(1-pi_q) + pi_q(1-pi_p).

The stated rank refinement can only help when at least one local operator is
singular, so total success is at most pi_p+pi_q. On balanced inputs where both
gcd(N-1,l^2-1) are polynomial in n, this upper bound is
2^(-n/2+O(log n)). Restarts then cost at least 2^(n/2-O(log n)) trials for this
particular sampler. This is a conditional obstruction, not a universal lower
bound on algebraic factoring. Orders with exceptional divisibility can make
the procedure useful on special families.

**Comparison and distinction.** This is an explicit norm/rank extraction
variant of the finite-field/Frobenius viewpoint behind probable-prime tests,
not an unexplained replacement for Frobenius. Grantham develops that viewpoint
for polynomial-based pseudoprime tests.
[Primary paper](https://arxiv.org/abs/1903.06820).
The norm collects extension-field zeros; (B1) shows exactly when that adds
anything to scalar X^(N-1)=1 tests. No general improvement over existing
factoring methods is supported.

**Idempotent audit.** In R itself, a nontrivial idempotent e immediately gives
gcd(e,N). But an extension-algebra idempotent need not do so: X in
R[X]/(X^2-X) is a freely available nontrivial idempotent with rank one over
every prime component. More generally, if multiplication by an idempotent in
a rank-d algebra has unequal local ranks r_p,r_q and p,q>d, its trace tau
satisfies tau≡r_p mod p and tau≡r_q mod q. Testing gcd(tau-j,N), 0≤j≤d,
extracts a factor. The missing operation is **constructing unequal ranks**,
not computing the trace. Calling a semisimple-algebra decomposition routine
that assumes a known coefficient field reintroduces the hidden factorization.

**Disposition / cheapest test.** Evaluate (B1) before any timing experiment.
Reject inverse-polynomial success claims on any proposed input sequence whose
two local gcd parameters stay small. Retain only as a controlled norm/rank
baseline or an explicitly scoped order-divisibility attack.

## Card C — Collisions under class-group squaring, targeting ambiguous forms

**Algorithm.** Use primitive positive definite binary quadratic forms of
discriminant Delta=-4N, without first computing the maximal order. Enumerate
known small primes l≤B with (Delta/l)=1; a nontrivial gcd(l,N) is already a
factor. Solve the quadratic congruence modulo the known prime l to construct
prime forms, then generate classes c_i by products of these forms with random
n-bit exponents. Store the canonical reductions of c_i^2. A collision

    c_i^2 = c_j^2  gives  u=c_i c_j^(-1), u^2=1.

Reduce u and check whether it is a useful ambiguous form. Reduced ambiguous
forms have boundary symmetries b=0, |b|=a, or a=c; the discriminant identity
then supplies candidates from a,c,2a-b,2a+b for gcd extraction. Check every
returned divisor. Identity and unhelpful ambiguous forms count as failures.

**Why this representation is relevant.** Form reduction and composition use
O(n)-bit coefficients and have polynomial bit cost. One can perform these
operations without a factorization of Delta. This genuinely changes the
arithmetic representation. By contrast, asking for all genus characters, all
ramified prime forms, the class-group 2-torsion basis, or its invariant factors
is not free preprocessing; the requested objects may already encode the
factors of Delta. A maximal-order/conductor routine can also require integer
factorization and is unnecessary here.

**Complete cost and unsupported gain.** Generating the prime pool costs its
sieve, character tests, and square roots over known primes: call this
P(B,n), polynomial in B and n. With g generators, each random product costs
O(gn) form operations plus O(gn) random bits. Let F(n) be a conservative
polynomial bit bound for one form operation. K samples, sorting and retaining
their preimages cost

    P(B,n) + O(K g n F(n) + K n log K),
    O(B + K n + g n) bits of principal stored data.

If the generated subgroup H has order h and U is its set of useful 2-torsion
elements, independent uniform samples obey

    Pr(any useful collision in K samples)
       ≤ K(K-1)|U|/(2h).                              (C1)

For a fixed pair, c_i c_j^(-1) is uniform in H, which proves the bound.
Thus constant success needs K=Omega(sqrt(h/|U|)). On instances with
h=N^(1/2+o(1)) and bounded |U|, the birthday scale is N^(1/4+o(1)), already
worse than the class-group relation baseline and the deterministic 1/5
exponent. Pool generation, uniformity/mixing, and coverage of useful torsion
must additionally be proved; this sampler has no such general guarantee.

The proposed disruptive primitive would be a factor-blind sampler strongly
biased toward *distinct useful elements in the same square fiber*, with
polynomial generation and success costs. Simply naming that sampler is
equivalent to leaving the hard torsion-construction problem unresolved.

**Prior art / distinction.** Producing ambiguous forms to factor integers is
already part of class-group relation factoring, including the rigorous
Lenstra–Pomerance algorithm cited above. This card tests whether square-map
collisions can avoid relation collection. Under uniform sampling, (C1)
answers negatively at the desired scale; adding smoothness relations returns
to known machinery rather than establishing a different algorithm.

**Disposition / cheapest falsifier.** Reject the unstructured birthday version
as a general improvement. Before implementing any proposed biased sampler,
specify its probability distribution and prove how it evades (C1) without
using a torsion or genus oracle. No class-group package or infrastructure was
built for this rejected version.

## Card D — Public N+1 exponents in a quadratic norm-one torus

**Algorithm.** Let M_B=lcm(1,...,B), E=(N+1)M_B. Choose a unit D with
Jacobi(D,N)=-1, checking gcds during rejection sampling. In
A=R[X]/(X^2-D), choose a uniformly modulo N and form

    u=(a+X)/(a-X),  norm(u)=1.

Invert a-X using its norm a^2-D; a nonunit norm either yields a factor or
causes a recorded restart. Compute u^E=v+wX and test gcd(N,v-1,w).

For a prime p where D is nonsquare, the norm-one group has order p+1. For a
prime q where D is square, it has order q-1. The public multiplier supplies
the exact identity

    gcd(p+1,N+1) = gcd(p+1,q-1),

and therefore

    p+1 | E  iff
    (p+1)/gcd(p+1,q-1) | M_B.                         (D1)

This is a precise special-family opportunity: a large shared component of
p+1 and q-1 can be absorbed without finding or factoring it.

**Scope, success and all costs.** Assume N=pq with distinct odd primes,
(D1)'s quotient divides M_B, and q-1 does not divide E. With uniform D among
units of Jacobi symbol -1, half the choices have the useful orientation
(D/p)=-1,(D/q)=+1. For this orientation, u^E=1 modulo p. Conditional on a
unit denominator at q, the ratio parameter is uniform in F_q^* minus {1};
its failure probability is

    (gcd(E,q-1)-1)/(q-2) < 1/2.

A bad denominator at q already gives a proper gcd. Thus the conditional
family admits a constant success bound (at least 1/4 per accepted D with
one a draw), and constant expected restarts. Selecting D also has constant
expected cost on these semiprimes. Exact uniform integer sampling can use
rejection, with all rejected draws charged.

Constructing M_B by sieving and prime powers costs soft-O(B) bit work/storage;
log E=O(B+n). Exponentiation in the quadratic algebra uses O(B+n) operations
on O(n)-bit residues. Total expected bit cost on the stated family is

    soft-O(B + (B+n)M(n)), memory soft-O(B+n).

For B=n^c this is polynomial. The hypothesis requires prime **powers** in the
quotient to be covered by M_B, not merely primes ≤B. On arbitrary N the
quotient need not be small or smooth, both local groups may be annihilated,
and restarting D does not repair that obstruction.

**Comparison / distinction.** This is Williams p+1 with an inexpensive public
exponent multiplier and a mixed split/nonsplit interpretation, not a newly
established group-factoring paradigm. Bach–Shallit already generalize
p±1 methods to cyclotomic groups. The scoped distinction from the plain
stage-one exponent M_B is that only the quotient in (D1) needs coverage.
The relevant comparator must include p+1 with the *same* N+1 multiplier;
then no asymptotic distinction remains. No novelty is claimed for this
multiplier, and the bounded search does not establish priority.
[Williams, primary DOI](https://doi.org/10.1090/S0025-5718-1982-0658227-7);
[Bach–Shallit, primary paper](https://www.ams.org/journals/mcom/1989-52-185/S0025-5718-1989-0947467-1/S0025-5718-1989-0947467-1.pdf).
The primary titles, identifiers, and indexed paper text were verified; direct
AMS PDF retrieval failed in the web tool.

**Cheapest falsifier / disposition.** Prove (D1), then compare against that
matched Lucas/p+1 implementation before spending time on a torus library.
Reject any general polynomial claim that substitutes a presumed frequent
shared large divisor for an input-wise success proof. Retain only as a
transparent scoped control, with low novelty potential.

## Finite evidence for Card A

Scratch file: `W001-algebra-identity-check.py`, Python standard library only.
Each invocation used an external 60-second timeout. No factoring-library,
timing benchmark, or shared harness was used. This is a mathematical checker:
it deliberately knows p,q for checking identities; it is not a solver trial.

Initial screen: seed 1001; 42 cubic identity cases using the unordered pairs
from {3,5,7,11,13,17,19}, two random monic cubics per pair; zero failures.
The four initial CM pairs took approximately 0.475 seconds together with the
identity checks. After deriving the stronger q>p lemma, three close pairs
were added. The final invocation repeated the same 42 checks and included all
seven pairs, completing in approximately 7.583 seconds. Repeated checks are
not independent evidence; the added examples are not a holdout.

For each pair, every t modulo q was checked. This is sufficient to count
failures for the scoped family, since p always divides C_N and the remaining
condition depends only on t modulo q. Counts below are proper-factor gcds /
all shifts, followed by gcd=N failures:

- 7·13=91: 10/13, failures 3; at t=1, C_N mod N=14, gcd=7.
- 7·17=119: 14/17, failures 3; at t=1, coefficient 7, gcd=7.
- 11·17=187: 14/17, failures 3; at t=2, coefficient 143, gcd=11.
- 11·29=319: 24/29, failures 5; at t=1, coefficient 77, gcd=11.
- 11·13=143: 12/13, failures 1; at t=1, coefficient 88, gcd=11.
- 23·29=667: 28/29, failures 1; at t=1, coefficient 598, gcd=23.
- 31·37=1147: 36/37, failures 1; at t=1, coefficient 31, gcd=31.

Every failure count was ≤(p-1)/2. Every t=0 control returned gcd=N.
All 155 shifts, including 17 failures, are represented above. No timeout or
unstarted case occurred. These counts corroborate the stated identities, not
an asymptotic speedup. The checker is quadratic in the numeric size N.

## Ranking and recommended next step

1. **A: retain for mathematical follow-up.** It gives an explicit factor-blind
   invariant and a provable scoped separation probability. Its computation is
   the central unresolved cost, not an unmeasured success heuristic.
2. **D: retain as a scoped control only.** Complete costs are inexpensive on
   its promised family, but the mechanism is already a p+1 exponent variant.
3. **B: reject the generic success claim.** Equation (B1) is a cheap exact
   test of any claimed benefit; exceptional orders remain scoped possibilities.
4. **C: reject uniform square-collision search.** It needs a new explicit
   biased generator before more computation is justified.

**Recommended next step, falsifiable and bounded:** audit a normalized block
product for Card A's coefficient recurrence, with no new infrastructure.
At t=1, putting m=(N-1)/2 gives

    C_N(f_1) = [X^m](X+1)^m(X+2)^m = d_m,
    sum_(m≥0) d_m z^m = (1-6z+z^2)^(-1/2),
    (m+1)d_(m+1) = 3(2m+1)d_m - m d_(m-1).

These identities follow by taking constant terms and differentiating the
displayed generating function. Its being nonrational rules out a fixed-size
constant-matrix powering representation over Q for the whole sequence. This
does **not** rule out faster index-dependent or modulus-dependent algorithms.
The familiar sequence connection also reinforces the need for a broader
prior-art check before any novelty claim.

The next specific lemma to attempt is: **can a recurrence block spanning
nonunits modulo N be normalized using only O(poly(n)) bits of intermediate
data, returning either its exact action or a proper factor, without knowing
the factors?** Require an explicit transition formula and charge the number
of blocks. The displayed recurrence's naive denominator product contains a
factorial; dividing by it modulo N is invalid. Computing exact numerator and
denominator integers can require exponentially many bits. Merely finding a
nonunit by scanning indices is trial-division-scale work.

For any proposed block formula, allow one ≤60-second scratch check against
exact coefficients on N∈{91,143,187}, with blocks straddling indices
7,11,13,17. Reject it at the first wrong residue, unjustified inverse, or
unaccounted integer-width growth. A successful check would still need a full
total-cost bound and the general translated-t version for (A2)'s randomized
guarantee. Until such a formula exists, do not install Card A in the shared
solver or claim improvement. The coefficient oracle is the question, not the
answer.
