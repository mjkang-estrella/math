**W001 — Lifting, carries, small roots, and coordinate changes**

Independent bounded ideation pass, 2026-10-07 America/Los_Angeles.
Verified improvement: **NONE**. Evidence level: ideas, elementary deductions,
and explicit counterexamples; no factoring-performance experiment or formal proof
was performed. Read AGENTS.md, the specification, README, RESEARCH_LOOP, and STATE
for the contract. The mechanisms below were developed independently of H002; its
placeholder was not read. No shared code, Lean files, or checkpoint was changed.

**Accounting and a common obstruction**

Here n is bitlength(N), M(w) is the bit cost of multiplying w-bit integers, and
all modular arithmetic is charged at its actual width. Polynomial factors below
include parsing, exact bounds, witness verification, and explicitly described
preprocessing. A compact formula is not a charged implementation of its
existential queries.

Remove even factors directly. For the all-input versions of Cards 1 and 4,
enumerate O(n) dyadic boxes

    P <= p < 2P,  ceil(N/(2P)) <= q <= floor(N/P),

clipped to 2 <= p <= floor(sqrt(N)) and 2 <= q < N. These boxes contain a
nontrivial factor pair of every odd composite, including composites with more
than two prime factors. They require no supplied factor interval. Every product
in a box is less than 2N. Set K=n+1 and B=2^K>2N: within these boxes,
pq congruent to N modulo B implies pq=N. The occasional cofactor-bound slack
does not invalidate this implication. Balanced semiprimes are the difficult
reference case, with both interval widths on the scale 2^(n/2).

For odd N, the complete set of k-bit lifts is exactly

    L_k = {(a, N*a^(-1) mod 2^k): 0 <= a < 2^k, a odd}.

Thus |L_k|=2^(k-1). Each pair has exactly two children at the next bit: writing
the new bits as alpha,beta, their parity equation fixes alpha+beta modulo 2.
Computing one inverse and one lift is polynomial; enumerating them all is not.
This is an elementary count, not a complexity lower bound for factoring.
For a known odd prime ell not dividing N the analogous count is
phi(ell^k), with ell children per lift. If ell divides N, finding that fact
already gives a factor. Lifting at the *unknown* factor prime is not free.

Two comparison points prevent misleading claims. A useful established rigorous
deterministic reference is the Harvey–Hittmeir bound
O(N^(1/5) log^(16/5)(N)/(log log N)^(3/5)), hence 2^(n/5+o(n)); this is a
reference bound, not a claim that this limited search establishes the latest
optimal result. [Harvey–Hittmeir, 2021](https://arxiv.org/abs/2105.11105).
The general number field sieve has the familiar *heuristic* bound
exp(((64/9)^(1/3)+o(1)) (ln N)^(1/3)(ln ln N)^(2/3)). Any fixed positive
exponent 2^(c n) loses to that asymptotically, even if it improves the rigorous
deterministic reference. [Buhler–Lenstra–Pomerance, original GNFS analysis](https://www.cs.umd.edu/~gasarch/TOPICS/factoring/1993_Book_TheDevelopmentOfTheNumberField.pdf).

**Card 1 — Inverse Taylor patches with certified integer relaxations**

*Mechanism.* Cover all odd residues by classes a modulo 2^s. In one class write
p=a+2^s t. Let D=ceil(K/s)-1 and form, with coefficients reduced modulo B,

    P_a(t) = sum(j=0..D) N*(-1)^j*a^(-j-1)*2^(sj)*t^j  (mod B).

The geometric-series remainder contains 2^(s(D+1)); consequently
q=P_a(t) mod B is exact for every t, not a numerical approximation. Generating
each patch costs O((D+log K) M(K)) using an inverse and coefficient recurrence,
up to standard arithmetic logarithmic factors. Store only D+1 K-bit
coefficients. All 2^(s-1) patches must be generated or otherwise accounted for.

For a t-interval [L,U] from a factor box, introduce integer variables z_j in
[L^j,U^j], z_1=t, and q in the cofactor interval, and impose

    q = sum(j=0..D) c_j*z_j - B*h,       z_0=1.

Drop the nonlinear identities z_j=t^j to obtain an integer-linear relaxation.
Optionally strengthen it by the endpoint tangent lower bounds and secant upper
bound for each convex power on t>=0. Reject a patch interval only when this
relaxation is infeasible. If a returned point satisfies every power identity,
verify pq=N. Otherwise bisect [L,U]; singleton intervals are exact. This is a
specified, terminating classical branch-and-bound algorithm, not an assumed
small-root oracle. A deterministic fixed-dimensional integer-programming
algorithm implements the relaxation test when D is fixed.
[Lenstra, 1983, original paper](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1983i/art.pdf).

*Proposed complete gain.* Let V be the total interval nodes across all boxes and
patches, and Q_IP(D,K) include construction and solution of one relaxation.
Total time is

    O(n*2^s*(D+log K)*M(K) + V*Q_IP(D,K)),

plus polynomial witness extraction. A conservative implementation of the
fixed-dimension primitive costs 2^(O(D^3))*poly(D,K), rather than unit time;
the dimension dependence is documented in the contemporary
[Kannan paper](https://doi.org/10.1145/800061.808749).
Coefficients have K bits, power bounds and h have O(DK) bits, and a whole
relaxation has polynomial size in D,K. A depth-first search streams the patches
and needs polynomial stack space plus the integer-programming workspace, not
a stored exponential patch table. Exhaustive bisection gives only
2^(n/2)*poly(n) for fixed D, up to polynomial box overhead.

The concrete speculative gain is V=2^s*poly(n). For D=5 and s=ceil(K/6), it
would give deterministic 2^(n/6+o(n)) time on *all* composites through the box
cover, improving the cited 1/5 reference but not GNFS. This requires a new
uniform bound on the search tree; none is supplied. Choosing s=O(log n) makes
the patch description polynomial but D=Theta(n/log n): both the known IP cost
and the unknown tree cost then block a polynomial claim. A polynomial algorithm
for exact interval queries on these large-degree patches would imply a
polynomial splitter through the construction above; it cannot be assumed as a
primitive.

*Prior art and distinction.* Modular hyperbolas have already been used for
factoring; the retrieved paper studies quadratic-residue differences and point
distances. This card instead proposes finite 2-adic inverse expansions plus
sound integer relaxations and explicitly counts their search trees.
[Di Mauro, 2020, original paper](https://arxiv.org/abs/2001.09814).
Fixed-dimensional integer programming is established, not a proposed invention.
No novelty claim follows from this limited comparison.

*Cheapest falsifiers.* Separate residue/interval tests cannot help early: any
interval containing 2^r consecutive integers contains a representative of every
residue modulo 2^r. Hence if both intervals are that wide, every odd a survives
the tests p=a mod 2^r and q=N/a mod 2^r separately. A claimed low-bit pruning
advantage must use a genuinely joint constraint.

Even the quadratic convex relaxation is not exact. Take N=115, K=8, B=256,
s=3, a=1, t in [1,3], and q in [3,5]. Then

    p = 1+8t;   P_a(t) = 115+104t+192t^2 (mod 256).

The true q residues are 155, 67, 107, so this patch has no solution in the box.
Yet t=2, z_2=5, q=3, h=5 satisfies the relaxed equality. It also satisfies both
endpoint tangents z_2>=2t-1 and z_2>=6t-9, and the secant z_2<=4t-3.
The fake witness gives p*q=17*3=51, not 115. This immediately rejects any
proposal to accept relaxation feasibility as an exact answer. It does not
reject sound bisection. The remaining decisive issue is whether false feasible
points force essentially complete bisection.

*Disposition:* strongest conditional research survivor; specified algorithm,
but no established speedup, and substantial reasons to expect weak pruning.
It is deterministic and requires no restarts; a resource cap means incomplete
search, not an established success probability.

**Card 2 — Carry-frontier compilation with exact continuation equivalence**

*Mechanism.* Encode schoolbook multiplication by

    c_i + sum(j) p_j*q_(i-j) = N_i + 2*c_(i+1),

with missing bits zero, c_0=0, and the final carry zero. Carries have O(log n)
bits, but each factor bit participates in many later columns. Construct a
decision diagram by alternating low-bit and high-bit restrictions, conjoining
the column constraints and public interval bounds. Eliminate a factor bit or
auxiliary variable only after all constraints using it have been combined.
Merge nodes only if their *entire* continuation functions are identical.
The proposed gain is a small exact frontier under this variable order, not a
small list of carry values. A canonical ordered BDD is one concrete way to
implement and test the claim. Auxiliary partial products may be introduced but
their consistency constraints and elimination costs remain in the accounting.

*Cost and gain.* Generating a binary multiplier relation takes poly(n) space
and time. If every intermediate BDD, including Apply and variable elimination,
has at most S nodes under a fixed order, the usual pair-memoized operations give
a poly(n)*S^2 bit-time upper bound and poly(n)*S^2 conservative workspace;
node addresses and keys require log S bits. Extracting one satisfying factor
assignment is cheap *after* the fully constrained diagram exists. All input
length pairs can be covered with polynomial overhead. The speculative condition
S=poly(n) would imply a polynomial splitter; S<=2^(gamma n) would give a
2^(2 gamma n)*poly(n) target, which improves the cited deterministic reference
only for gamma<1/10. No such size bound is known here. Exhaustive branching is
still exponential. If order search is used, charge every order tried; there is
no unpriced choice of an optimal order and no justified random-restart success
rate.

*Prior art and distinction.* Branch-and-prune RSA reconstruction already uses
algebraic redundancy and leaked bits; that additional information is absent
here. [Heninger–Shacham, 2009, author page](https://hovav.net/ucsd/papers/hs09.html).
Factoring through BDDs has also been studied explicitly.
[Raddum–Varadharajan, original paper](https://web-backend.simula.no/sites/default/files/publications/files/raddum-varadharajan2018_article_factorizationusingbinarydecisi.pdf).
Word-level multiplication can have compact binary moment diagrams;
this is established representation work, not efficient inversion.
[Bryant–Chen, 1995, author-hosted paper](https://www.cs.cmu.edu/~bryant/pubdir/dac95a.pdf).
This card's particular test is alternating interval restrictions with a complete
live-variable frontier. It does not claim that BDD factoring or compact
multiplication is new. Nor does it assume a general BDD lower bound applies to
every representation of a fixed target N.

*Cheap counterexample and a stronger obstruction.* For k=4, prefixes (a,b)=(1,15)
and (3,5) both have ab=15, the same low product bits, and the same block carry
floor(ab/16)=0. For N=703 the suffixes (x,y)=(1,2) complete the second pair to
19*37=703, but complete the first to 17*47=799. Moreover the individual column
carry sequences inside these four-bit prefixes are also identical: all zero.
Thus even the full past carry history is not a valid merge key.

In general, after a,b are fixed, the remaining integer equation is

    2^k*x*y + b*x + a*y = (N-a*b)/2^k.

With ordered suffix variables, equality of these residual polynomials forces
both a and b to agree. Hashing the exact residual coefficients therefore yields
no merges between different ordered low-prefix pairs. Swapping factors only
provides a constant symmetry reduction. More powerful equivalence of the
*restricted solution sets* could merge empty branches, but discovering that
equivalence must be included in compilation cost. The final answer diagram for
a semiprime can be tiny even when constructing it is expensive.

*Disposition:* carry-only and residual-coefficient compression are rejected by
the examples/algebra above. A complete-frontier variable-order experiment remains
a lower-priority conditional lead, with no evidence that it beats known BDD
work. The equations are valid for arbitrary composites; favorable leaked-bit
or unusually structured-factor results must remain separately scoped.

**Card 3 — Block certificates for unknown residues before Coppersmith**

*Mechanism.* Restrict this card initially to balanced semiprimes, with no supplied
factor bits. Let k=(1/4+epsilon)n+O(1), 0<epsilon<1/4 fixed. Standard residue
enumeration tries every odd a modulo 2^k, then uses the monic polynomial

    f_a(x) = x + a*(2^k)^(-1) (mod N)

whose root x=(p-a)/2^k is modulo the unknown factor p. With an appropriate
factor-size bound beta=1/2-O(1/n), the usual small-root range is safely reached
using this epsilon slack. Wrong residues must cost a full attempted solve; no
factor bits have been acquired for free.

Try processing a block of residues at once. Fix only r<k bits a_0, write

    a=a_0+2^r*u,   0<=u<2^(k-r),
    F(u,x)=a_0+2^r*u+2^k*x.

Build scaled bivariate lattices from shifts
u^h*x^j*N^(m-i)*F(u,x)^i for 0<=i<=m and specified finite degree limits.
At the true factor these polynomials are divisible by p^m. A reduced polynomial
whose scaled coefficient norm is below N^(beta*m)/sqrt(number of monomials)
vanishes over the integers at every bounded candidate root. Seek enough
independent such polynomials to eliminate u,x. A certified empty common-zero
set rejects the whole block. Failure to find short polynomials or independent
relations is **inconclusive**, so split the block and ultimately run the usual
univariate solver at depth k. Roots always undergo division verification.

*Complete cost and proposed gain.* Let A count all visited blocks, L all terminal
residues, Q_lat the charged lattice construction and reduction cost, E the total
elimination/certificate cost, and Q_uni the univariate cost. Then

    T = poly(n) + A*Q_lat + E + L*Q_uni.

The lattice dimension, all row shifts, and coefficient sizes must be explicit
in an implementation; polynomial m and degrees give polynomial coefficient
width but not automatic root isolation or algebraic independence. Store the
current lattice and a depth-first search stack; storing all block bases would
multiply memory by A. Positive-dimensional common components cannot simply be
discarded. If zero-dimensional elimination fails, its work still counts and
the block must be split. Cap certificate work per block at a fixed explicit
polynomial budget and treat exhaustion as inconclusive; this preserves the
fallback bound rather than allowing one unsuccessful elimination to run forever.

The supported fallback is 2^((1/4+epsilon)n)*poly(n) time for fixed safe lattice
parameters, with polynomial streaming memory. This is already worse than the
cited deterministic reference and heuristic GNFS. The speculative gain would
be a uniform polynomial-cost block certificate at depth r=k-b, reducing the
residue acquisition cost to 2^r*poly(n); r<n/5 would beat the deterministic
reference on this scope. To beat GNFS asymptotically requires much more than a
fixed fractional reduction in r. Polynomial general factoring would also need
r=O(log n), polynomial certificate work, and a reduction covering other factor
sizes/composites; balanced results alone do not supply it.

*Prior art and distinction.* Small-root factoring given enough actual factor
bits is Coppersmith's established application, not the proposed gain.
[Coppersmith, 1996, original paper](https://static.aminer.org/pdf/PDF/000/192/858/finding_a_small_root_of_a_bivariate_integer_equation_factoring.pdf).
ROCA explicitly prices guesses of a constrained factor residue followed by
Coppersmith, exploiting a defective prime-generation family. It provides an
especially relevant warning against importing reduced residue entropy into
general factoring. [Nemec et al., 2017, author preprint, sections 2.3–2.4](https://crocs.fi.muni.cz/_media/public/papers/nemec_roca_ccs17_preprint.pdf).
The proposed difference is a sound certificate covering *all* residues in a
block, without such a family restriction; neither citation supplies one.

*Cheapest decisive falsifier.* Substitute

    z = u+2^(k-r)*x;     F = a_0+2^r*z.

For a rectangular digit range, z enumerates exactly the contiguous missing
suffixes; with physical factor bounds it covers the corresponding truncated
range. Its width is on the scale 2^(n/2-r), not 2^(n/2-k). Thus merely naming
unknown low bits u as a second variable recovers the old univariate uncertainty.
The standard balanced-factor root condition still asks approximately r>=n/4.
This algebraic check rejects an exponent improvement attributed solely to
symbolic batching. Any proposed lattice must exhibit independently vanishing
relations beyond this reparameterization, with proven norm bounds. In a small
implementation, one actual factor in a block discarded because LLL found no
root immediately falsifies that pruning rule.

*Disposition:* naive batching is rejected as an information-free coordinate
split. Certified block elimination remains logically possible but ranks below
Card 1 because its missing independence/certificate step is less concrete.
The conservative algorithm is deterministic; randomized lattice retries need
their own success analysis and cannot erase failed-block costs.

**Card 4 — 2-adic logarithm coordinates and exact interval correlation**

*Mechanism.* For K>=3, every odd residue has a unique representation

    x = (-1)^sigma * 5^u (mod 2^K),
    sigma in {0,1},  0<=u<H=2^(K-2).

Compute (sigma_N,v) for N by bit lifting. A uniform implementation precomputes
5^(2^j) and their inverses modulo 2^K by repeated squaring, then determines
successive exponent bits from the next residue bit. This takes O(K M(K))
arithmetic time up to logarithmic factors and O(K^2) bits for the optional
table; the table is generated during the run. This easy logarithm is modulo a
*known power of two*, never modulo the unfactored N.

Multiplication now imposes only sigma_q=sigma_N-sigma_p mod 2 and
u_q=v-u_p mod H. For one factor box define exact Boolean functions

    A_sigma(u) = [least residue of (-1)^sigma*5^u lies in I],
    C_tau(u)   = [least residue of (-1)^tau*5^u lies in J].

Find a nonzero term in sum_u A_sigma(u)*C_tau(v-u). One concrete proposed
implementation builds low-exponent-bit decision diagrams for A and C, composes
the modular subtraction circuit, intersects, and extracts a witness. Cheap
node tests use the residue class forced by the assigned exponent bits; stronger
nodes must preserve the full interval preimage. Sign choices and all factor
boxes are explicitly enumerated.

*Cost and gain.* Materializing both dense functions takes Theta(H) entries and
Omega(H) work before any transform: H=2^(n-1) here. A fast convolution on a dense
array does not remove that cost. Alternatively, generate the odd integers in
each balanced interval, compute each logarithm, and intersect complementary
exponents: 2^(n/2)*poly(n) time and 2^(n/2)*poly(n) memory, or the same exponential
time with polynomial memory by direct candidate validation. These are not
improvements. For the diagram proposal let S include the largest intermediate
diagram and let G include the work generating its interval preimages. The
conditional target is G+poly(n)*S^2 bit operations and corresponding charged
workspace. Neither G nor S is known to be small. If both were polynomial,
the exact box construction would yield a general polynomial splitter.

All powers use modular reduction, so operands have O(n) bits, not gigantic
ordinary exponents. Conversely the number of residues remains exponential.
There is no randomness in the exact method. Sampling u uniformly in the dense
group hits one of a bounded number of factor witnesses with probability only
O(1/H) for a semiprime; required restarts erase a polynomial claim. Approximate
correlation also needs enough accuracy to distinguish zero from a single
witness, i.e. less than 1/2 absolute error in the unnormalized count, not merely
a constant relative error against H.

*Prior art and distinction.* Efficient prime-power logarithm lifting is known.
[Bach, 1984, original report and abstract](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1984/5973.html).
An explicit bit-serial algorithm modulo 2^K, using sign/exponent coordinates
with base 3 and an O(K^2)-bit table, is also known.
[Fit-Florea–Matula–Thornton, 2005, author-hosted paper](https://s2.smu.edu/~mitch/ftp_dir/pubs/eleclet05b.pdf).
The proposed work lies only in constructing and querying interval preimages
without decoding every residue. The logarithm itself is not new, and replacing
base 3 with base 5 is not a novelty claim.

*Cheapest falsifiers.* Modulo 32, powers of 5 for u=0,...,7 are
1,5,25,29,17,21,9,13. The interval [8,18] pulls back to {4,6,7}, already
disconnected in exponent order. This refutes interval monotonicity; it does not
prove an exponential fragmentation theorem.

More strongly, fixing u modulo 2^h fixes the residue of 5^u modulo 2^(h+2),
and the remaining exponent bits range over every higher lift of that class.
Thus an interval of at least 2^(h+2) consecutive integers cannot reject that
node by independent class intersection. Both broad factor intervals therefore
keep such tests ineffective through many exponent bits. Logarithm coordinates
linearize multiplication but move the difficult condition into interval
membership. A polynomial-size arithmetic circuit for that membership is not
a polynomial-size searchable diagram or a polynomial exact correlation routine.

*Disposition:* retain only as a low-priority representation experiment. Simple
exponent interval pruning and dense Fourier/table approaches fail the cost
screen. A restricted family whose factor exponents occupy few cheaply
constructible intervals would be a scoped result; that property must not be
assumed for arbitrary N.

**Ranking and the bounded next step**

No mechanism survives as a demonstrated complexity improvement. Ranked as
conditional research leads: **1 > 2 > 3 > 4**. Card 1 has a sound explicit
algorithm and a measurable missing quantity, its interval search tree. Card 2
has a clear frontier metric but severe identity obstructions and extensive
prior art. Card 3 requires stronger lattice certificates beyond an exact
reparameterization. Card 4 presently relocates the decoding problem.

Recommended next step: a single **60-second maximum**, standard-library-only
screen of Card 1's quadratic relaxation, before implementing any general IP
solver or modifying the harness. This screen is proposed, **not run** here.

Use K=10,12,14,16 and s=ceil(K/3), D=2. Enumerate primes of bit length K/2 by
trial division solely in the test-data generator. Form the finite list of
products of two distinct such primes with bitlength(N)=K-1, shuffle that list
with generator seed 1001, and take at most eight distinct N per K. Small pools
may supply fewer than eight; report their actual size rather than retrying
indefinitely. Bound generation as part of the 60 seconds and report shortfalls.
Use the
public interval I=J=[2^(K/2-1),2^(K/2)-1], which needs no factor advice and has
all products below 2^K. Pass only N and this public size-derived interval to
the probe. It covers a balanced special family for diagnosis, not all inputs.

For each odd a modulo 2^s, recursively bisect its t interval. Decide relaxation
feasibility by a deliberately tiny reference enumerator over t and q, solving

    c_2*z_2 = q-c_0-c_1*t (mod 2^K)

using gcd and checking whether its arithmetic progression meets the tangent/
secant z_2 bounds. This enumerator is an explicitly exponential *diagnostic
oracle*, not the proposed efficient IP implementation; record its actual work
and time separately. At each node also compute true feasibility by direct
enumeration, without giving that answer to the pruning procedure. Search the
whole tree even if a factor is found, so easy early witnesses do not conceal
false-branch cost. Aggregate only completely finished instances; preserve all
timeouts, partial counts, and unstarted cases in the report denominator.

Record false feasible nodes, first rejection depth, total bisection nodes,
maximum integer width, and the node fraction versus the complete unpruned
bisection trees over the same residue intervals. Prespecified rejection of this
*cheap relaxation route*: if, on completed instances at the largest completed
K, the median node fraction is at least 0.8, do not invest in higher-degree IP
infrastructure. A smaller fraction warrants only a follow-up scaling test and
an attempt to bound V; it is not an asymptotic conclusion. Any discarded true
solution is an immediate soundness failure. Recheck the N=115 false-feasibility
example first as a hand-auditable control.

The mathematical obligation worth pursuing if that screen is favorable is a
uniform bound on V for **D=5**, including all dyadic boxes and empty patches.
The degree-two screen alone cannot improve the reference factoring exponents.
No result in this report establishes novelty, impossibility, polynomial
factoring, or any change to the current verified-improvement status.

Source checks used primary papers/author or institutional pages retrieved on
this pass. Some publisher/Simula full-text opens were intermittently unavailable;
the Raddum–Varadharajan title and original-paper abstract were retrieved, and no
unread runtime theorem from that paper is assumed. The literature check is
focused rather than exhaustive.
