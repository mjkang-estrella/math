# H006 independent review

Review date: 2026-10-08 (America/Los_Angeles). Original candidate:
Card 1 of `research/hypotheses/W001-lifting.md`. Current verified factoring
improvement: **NONE**. This is a new review round, with no delegation, commits,
publication, package installation, or shared-source edits.

**Disposition: close the independent-power tangent/secant implementation as a
route to the proposed small exhaustive search tree.** The frozen H006 experiment
remains **inconclusive under its preregistered finite threshold**; its result must
not be relabeled. Separately, the self-contained argument below gives
`Theta(R^3)` nodes for its full exact-relaxation tree, uniformly in odd N, as
`R = 2^s` grows. It also gives the same order of node growth on a broad input
range in the actual clipped Card 1 boxes. This contradicts a uniform bound
`V = R poly(K)` for these exhaustive trees. It is **not** a lower bound for
factoring with early stopping, a lower bound for general factoring, or a novelty
claim. The derivation here is a mathematical review result, not a Lean theorem.

I read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, the full Card 1, both H005 documents, and
the H006 protocol, source, and result. The only authored artifacts are this
report and the accompanying uniquely named H006-review-* files.

**1. Frozen evidence and independent replay.** The source and protocol hashes
match the hashes inside result.json:

- Source: `2ef3772294e3362e2952864e8ec8af322e34f2fc43d2a321cad4f1530b1ece28`.
- Protocol: `820ac9d1824c221fe5b4fb87f97302cc2c9935a32f9a484c06c279c2b8711727`.
- Result: `4d5055efbded2e00dbe5e696a7f4785b006a317ef980bde85cc1ea7cdc93a767`.

[H006-review-audit.py](H006-review-audit.py) loads the frozen source without
executing its main routine or writing an import cache. It replays all 20 inputs,
and independently checks every returned witness with rational secants, a
separate coefficient recurrence, the original power-box constraints, the full
congruence, and every ancestor's inequalities. All non-timing replay fields
match. All **53,108 witnesses** pass. Per K, the checked counts are
18, 177, 1,104, 7,943, and 43,866. The source, protocol, and result hashes remain
unchanged. The review script completed in about 5.39 seconds on this machine;
this timing includes the additional checks and enumeration, and is not a
factoring benchmark. Exact evidence is in [H006-review-audit.json](H006-review-audit.json).

The frozen run completed all 20 selected inputs with no generation shortfalls,
partial inputs, or unstarted inputs. Its reported median node fractions
0.4, 0.3571428571, 0.3009803922, 0.2466397849, and 0.1704594017 are correct.
At K=36, the median visited count is 22,337 and the four inputs have 43,863
spurious certificates. The rejection threshold 0.5 was not met. These finite
numbers neither prove nor disprove an asymptotic bound.

**2. Certificate soundness, input boundary, and accounting.** Set
`R=2^s`, `B=R^6`, and, separately, `M=R^3`. Thus B is the full Taylor modulus;
M is the modulus used to choose q. Let N and a be odd. Multiplying the
six-term geometric series by `1+Rt/a` proves the stated degree-five inverse
identity modulo B, because its remainder is divisible by `R^6`.
Reducing c_j modulo B preserves both `R^j | c_j` and the oddness of
`c_j/R^j` for j=0,...,5. In particular, the inverses modulo R used in the
certificate exist.

After fixing z_2=t^2 and q modulo R^3, the induction invariant is
`R^j | q - sum(i<j)c_i z_i`. Selecting the required residue of z_j modulo R
makes the new residual divisible by `R^(j+1)`. For j=3,4,5 this yields the
complete congruence modulo B. Python's integer division is exact at these
steps, including for a negative residual; the divisibility assertions check
the necessary precondition. The tangent expressions are integers, and the
secant is floored exactly by integer division. No floating-point arithmetic
decides feasibility. Floats appear only in timing, ratios, and summaries.

The bounds are legitimate on t>=0, where each power t^j is convex. They also
imply the original box `L^j <= z_j <= U^j`: the lower tangent at L is at least
L^j, and the chord is at most U^j. A singleton is checked using the exact
Taylor polynomial. Feasibility means that an integer h exists with
`sum c_j z_j - q = B h`; the code's congruence verifies this without needing
to store h.

There is no observed hidden-factor leakage. The generator uses factors to
construct inputs, but `probe` receives only N, K, and a public deadline. The
certificate receives only public patch data and coefficients. Neither reads
corpus factors, consults a factor table, or calls the prime generator. On every
recorded input K equals bitlength(N)+1, so K is public size information. The
balanced-box restriction is openly part of the diagnostic, not evidence that
this public box covers arbitrary composites. The deterministic public corpus
is not a blind holdout.

Unknown certificate outcomes are counted as uncertified boundaries and are
never labeled infeasible. The subtree includes each root and the two children
of every certified nonsingleton node. It is contained in exhaustive traversal
using an exact feasibility oracle. This assertion requires the comparison
traversal to expand feasible nonsingletons even after finding a factor. It is
not true for a search that terminates globally on its first factor, or one that
resolves a whole interval after extracting a factor from it.

The deadline is cooperative, with checks between nodes and generation attempts;
the command also has an outer timeout. Actual partial/unstarted records and
generation shortfalls would be retained if main reaches result writing. A hard
kill before that final write would not preserve in-memory partial counters.
That is a limitation of possible future interrupted runs, not a missing outcome
in this completed frozen run. `peak_certificate_bits` measures selected
successful-witness values and the partial sum, not every intermediate value,
failed attempt, coefficient-construction product, or Python allocation. It must
not be called a complete arithmetic-width or bit-cost measurement.

**3. Two explicit corrections.** First, an uncertified node can contain factors.
For N=2021=43*47, K=12, R=4, a=3, and t in [10,11], the two endpoints give
(p,q)=(43,47) and (47,43). The frozen certificate returns None because this
nonsingleton interval has no strictly interior integer. Consequently the probe
is not a complete factoring search, and the absence of a returned factor has
no negative correctness meaning.

Second, the parent's proposed reduction to `N/(a+Rt) mod R^3 in J` applies to
the restricted construction with z_2=t^2. It is not an equivalence for the
whole relaxation. An explicit counterexample uses N=2021, K=12, R=4, a=1,
[L,U]=[8,11], and J=[32,63]. The two interior inverse residues modulo 64 are
1 and 29, both outside J. Nevertheless the unrestricted relaxation accepts

    t=9, q=49, z=(1,9,80,706,6146,53251), h=42229.
    c=(2021,108,3664,1728,1280,3072).
    sum(c_j z_j) = 172970033 = 49 + 4096*42229.

For j=2,3,4,5 the allowed integer bounds at this t are respectively
[80,83], [704,785], [6144,7611], and [53248,75529]. Every inequality holds.
Here z_2=80 differs from t^2=81 and p*q=37*49=1813 differs from N.
This example also shows why the restricted construction supplies a lower
bound rather than an exact description of feasible nodes.

An exact “half the positions” identity is false at small sizes. For s=2,
N congruent to 3 or 29 modulo 64 has zero qualifying interior positions in
the four-integer nodes. Exhaustive checks over all odd residues of N give
minimum/maximum qualifying counts 0/8 at s=2, 16/48 at s=3, and 204/308 at
s=4. The respective averages are 4, 32, and 256. The asymptotic statement
below is uniform with an error term; it does not assume an exact pairing or
an average over N.

**4. Interior digit freedom is provable.** Let L>=R^2/2, U-L>=2, and let
t be a strictly interior integer. For f(x)=x^j, j>=3, put

    mu = j(j-1)L^(j-2), d=t-L, e=U-t.

On [L,U], f''>=mu. Integrating this inequality twice gives

    f(t)-T_L(t) >= mu*d^2/2,
    f(t)-T_U(t) >= mu*e^2/2,
    C_LU(t)-f(t) >= mu*d*e/2,

where T denotes the endpoint tangent and C the chord. The last inequality
also follows by applying convexity to `f(x)-mu*x^2/2`. Thus

    C_LU(t)-max(T_L(t),T_U(t))
      >= mu*(d*e+min(d^2,e^2))/2 >= mu.

The lower bound is an integer, so flooring the chord still leaves
`upper-lower >= mu`. For j=3,4,5 and s>=2, mu>=3R^2>=R. Hence the integer
interval contains every residue class modulo R. This proves that the three
high-digit choices are automatic for **any** such interior t once a suitable
q modulo M has been chosen. Three integers in the interval suffice; “width”
must distinguish integer cardinality from U-L. At an endpoint every power
is instead forced exactly. With two integers every integer is an endpoint.

For the restricted construction, its initial residue equals N/p modulo M:
the geometric remainder after degree two is divisible by R^3. Since J is
[M/2,M), there is exactly one eligible q when the least residue lies there,
and none otherwise. This is an equivalence for this restricted construction
at the chosen interior t. The full relaxation can have additional witnesses,
as shown in section 3.

**5. Nested relaxations make those nodes reachable.** Suppose [l,u] is
contained in [L,U] and t lies in [l,u]. For a convex differentiable f,
the tangent at l is at least the tangent at L at such a t; the tangent at u
is at least the tangent at U. For example, their first difference is

    T_l(t)-T_L(t)
      = f(l)-f(L)-f'(L)(l-L) + (f'(l)-f'(L))(t-l) >= 0.

The corresponding right-endpoint identity is analogous. The outer chord
is above f at both l and u, hence above the inner chord on [l,u]. Flooring
preserves that inequality. Original power boxes are nested as well. The
coefficients and q interval do not change within a patch.

Therefore the same (t,q,z,h) feasible in a descendant is feasible in all its
ancestors. Every feasible descendant is reached by the full exact-relaxation
bisection, regardless of whether the frozen three-point procedure would
certify those ancestors. No randomness or independent-success assumption is
used here.

**6. A self-contained uniform count for the four-integer nodes.** Write
`m=3s`, so M=2^m. Each H006 patch has exactly

    t in [R^2/2, R^2-1].

Its root has R^2/2 integers, a power of two. Four-integer nodes are therefore
aligned as [4b,4b+3], with interior t congruent to 1 or 2 modulo 4. The
eligible p positions are exactly the odd p in [M/2,M) with
`p mod 4R in [R,3R)`. Their count is M/8. Define

    C_N = #{such p : (N*p^(-1) mod M) in [M/2,M)}.

I will show, uniformly for every odd N and every s>=2,

    |C_N-M/16|
      <= 4*2^ceil(3s/2) * (2+ln M)^2 * (2+ln(4R)).        (1)

The error is `O(sqrt(M)*(log M)^2*log R)=o(M)`. The proof uses only finite
sums and the following elementary estimates.

Use normalized Fourier coefficients
`fhat(u)=M^(-1) sum_x f(x) exp(-2*pi*i*u*x/M)`. The indicator of any cyclic
interval has Fourier l1 norm at most `2+ln M`. Indeed its nonzero
coefficients have absolute value at most `1/(2*min(u,M-u))`, by the
geometric-sum formula and `sin(pi*d/M)>=2d/M` for 0<=d<=M/2. Summing these
bounds proves the claim. A periodic indicator with period d dividing M has
the same Fourier l1 norm as on modulus d. The l1 norm of a product is at
most the product of the norms, by the convolution identity.

For integers u,v with v odd, consider the complete sum

    S_M(u,v) = sum(x odd mod M) exp(2*pi*i*(u*x+v*x^(-1))/M).

Put ell=ceil(m/2) and h=floor(m/2). Write x=y+2^ell*z, with y odd modulo
2^ell and z modulo 2^h. Exact expansion modulo M gives

    x^(-1) = y^(-1)-2^ell*z*y^(-2) (mod M).

Summing over z gives zero unless `u-v*y^(-2)=0 mod 2^h`, and otherwise has
absolute value 2^h. If u is even this condition has no solutions. If u is
odd it asks `y^2=v/u mod 2^h`. There are at most four roots modulo 2^h:
given one root, divide any other by it and use
`(w-1)(w+1)=0 mod 2^h`; for odd w, one of w-1,w+1 has exactly one factor
of two and the other must be divisible by 2^(h-1). Hence
`w=+1 or -1 mod 2^(h-1)`, with at most four lifts modulo 2^h. Here h>=3.
Each root has 2^(ell-h) lifts modulo 2^ell. Thus

    |S_M(u,v)| <= 4*2^ell.                                (2)

Let H be the indicator of [M/2,M), E the period-4R indicator of [R,3R),
and A=H*E (pointwise product). Then

    C_N = sum(p odd mod M) A(p) H(N*p^(-1)).

The constant Fourier coefficient of H is 1/2. Every other even-frequency
coefficient is zero, since H has exactly M/2 consecutive entries. Thus the
constant contribution is `(1/2)*sum(p odd)A(p)=M/16`. All remaining second
frequencies are odd, and multiplication by odd N preserves their oddness.
Expand A and H and apply (2). Their Fourier norm bounds are
`||Ahat||_1 <= (2+ln M)(2+ln(4R))` and
`||Hhat||_1 <= 2+ln M`. This proves (1).

This is a fixed-input count: N is never averaged, assumed random, prime,
squarefree, or coprime to anything beyond the power of two. As a conservative
explicit threshold, (1) implies C_N>=M/32 for every s>=20. For example the
error divided by M is at most
`192*sqrt(2)*s^3/2^(3s/2)` using `2+ln M<=4s` and
`2+ln(4R)<=3s`; this is below 1/32 at s=20 and decreases thereafter.
These constants are not optimized, and that asymptotic threshold is far
beyond the frozen experiment's sizes.

The underlying stationary-phase method is standard. I checked the primary
paper [Erdelyi, Toth, and Zabradi, Matrix Kloosterman sums modulo prime powers
(2024), Proposition 1.1 and section 2](https://real.mtak.hu/191564/1/s00209-024-03467-y.pdf).
Several stronger statements there treat odd primes separately. The proof
above supplies the needed power-of-two estimate directly, with a conservative
constant, and does not import an odd-prime bound at p=2. No external
incomplete-Kloosterman theorem is assumed.

Each qualifying p yields a feasible four-integer node by section 4. A node
has only two interior p positions, so there are at least C_N/2 such nodes.
They are reachable by section 5. They and their two immediate children are
distinct visited nodes. Consequently

    V_full >= 3*C_N/2 >= 3M/32-o(M).

There are exactly `(M-R)/2` nodes in the complete unpruned forest, giving
`V_full=Theta(M)=Theta(2^(K/2))`. The lower bound alone gives an asymptotic
visited fraction at least 3/16-o(1), not the preregistered finite threshold
0.5. A constant-fraction rejection threshold is not the right asymptotic
falsifier: `V/R` grows at least on the order of R^2, which rules out
`R poly(K)` even if the fraction is well below 0.5.

For finite checks independent of ancestor sampling, the four K=36 inputs
have respectively 16,430, 16,492, 16,396, and 16,352 qualifying positions.
They certify 12,306, 12,350, 12,284, and 12,282 distinct four-integer nodes.
Those nodes and their children alone give visited lower bounds 36,918,
37,050, 36,852, and 36,846. These are constructive finite lower bounds,
not estimates of the full node counts and not replacements for the frozen
threshold outcome.

**7. The obstruction also applies to actual clipped Card 1 boxes.** A large
diagnostic box alone would not refute the original all-input proposal: its
p interval is clipped at sqrt(N). Here is a separate argument that pays
attention to that distinction and avoids any assumption about four-integer
alignment after clipping.

First extend the finite-sum bound. For arbitrary v!=0 modulo M, divide out
`g=gcd(u,v,M)` to obtain

    S_M(u,v)=g*S_(M/g)(u/g,v/g).

At least one reduced coefficient is odd. Inversion of x interchanges the
coefficients if necessary. The proof of (2), with a trivial estimate for
the smallest moduli, then gives

    |S_M(u,v)| <= 8*sqrt(M*gcd(v,M)).

For an arbitrary interval J in [0,M), its Fourier coefficients obey

    sum(v!=0) |Jhat(v)|*sqrt(gcd(v,M))
      <= (1+ln M)/(1-1/sqrt(2)).

To see this, pair frequencies v and M-v, write the smaller as 2^d*w
with w odd, and apply the geometric-sum coefficient bound. The contribution
for each d is at most `2^(-d/2)*(1+ln M)`; the geometric series over d
converges. Expanding an interval indicator I in the other variable yields,
uniformly for odd N,

    #{p odd in I : N/p mod M in J}
      = (|J|/M)*#{p odd in I} + O(sqrt(M)*(log M)^2).       (3)

For clarity an admissible absolute error in (3) is
`8*sqrt(M)*(2+ln M)*(1+ln M)/(1-1/sqrt(2))`.

Now take any odd N with

    5*M^2/16 <= N <= 3*M^2/8.

It has bitlength K-1, so the original prescription K=bitlength(N)+1
matches K=6s. Its actual dyadic box with P=M/2 has

    I=[M/2, floor(sqrt(N))],
    J=[ceil(N/M), floor(2N/M)].

Both are contained in [0,M), the p width is at least
`(sqrt(5)/4-1/2)M-O(1)`, and |J|/M>=5/16-O(1/M). There are
`T=Theta(M)` odd positions in I, each belonging to one of the R/2 patches.
By (3), at least `T/4-o(M)` positions have their inverse residue in J.

For sufficiently large R, every root patch has at least 16 integers.
Bisect it until each frontier interval has between 16 and 31 integers:
stop below 32; splitting any interval of length at least 32 makes children
of length at least 16. There are at most T/16 such frontier nodes, hence
at most T/8 endpoint positions. Removing all endpoints leaves at least
`T/8-o(M)=Omega(M)` qualifying interior positions. Every such position
has L>=R^2/2, so section 4 constructs its certificate with q in this actual
J. Each frontier node contains at most 31 positions. Thus
`Omega(M)` distinct frontier nodes are feasible and reachable in the actual
clipped full tree. Its unpruned forest has O(M) nodes, proving `Theta(M)`
full-tree nodes here too. There is no assumption of independent behavior
between nodes, patch residues, or N values.

This input interval contains composites at arbitrarily large sizes; for
example `(M/2+1)*(5M/8+1)` lies in it for sufficiently large M and has two
odd nontrivial factors. This example supplies a nonempty infinite family,
not a hard factoring family or a factoring lower bound. The statement
above applies to every odd N in the stated interval when that box is
exhaustively searched, regardless of its factorization type.

[H006-review-clipped-check.py](H006-review-clipped-check.py) independently
checks the actual clipped boxes for all four K=36 frozen inputs. It constructs
and verifies the frontier certificates and every ancestor. The numbers of
certified frontier nodes are 510/512, 512/512, 1024/1024, and 1024/1024.
Their qualifying interior-position counts are 2,337, 3,722, 7,417, and 7,817.
All checks pass; exact inputs, intervals, counters, and sample witnesses are
in [H006-review-clipped-check.json](H006-review-clipped-check.json). This
finite extension is diagnostic enumeration, not an implementation of fast IP.

**8. Spurious witnesses, repeated factors, costs, and limits.** The count and
reachability results hold for every odd N, including repeated factors and
prime controls. To count nodes containing no true factor at all, subtract
at most tau(N), the number of positive divisors, from the certified bottom
or frontier nodes. Their p intervals are disjoint. For semiprimes this removes
at most two nodes, and for a prime square at most one nontrivial-factor node
in these boxes.

More generally tau(N)=o(M) when N=Theta(M^2). An elementary justification,
without a divisor-estimate citation, is that for any fixed epsilon>0,
`tau(N)<=C_epsilon*N^epsilon`: for prime factors p>=2^(1/epsilon),
`e+1<=2^e<=p^(epsilon*e)`; for the finitely many smaller primes,
`sup_e (e+1)/p^(epsilon*e)` is finite. Multiply these bounds over the prime
factorization. Taking epsilon=1/4 gives O(sqrt(M))=o(M). Thus the lower
bound includes Omega(M) nodes without true factor pairs. Repeated factors
do not invalidate it. A perfect-power precheck may of course finish a
particular input before this search; no lower bound is asserted for it.

One certificate attempt uses a fixed number of exact operations on O(K)-bit
integers and has polynomial bit cost. Patch preparation costs
`R poly(K)` in total. Exhaustive node processing with a polynomial-cost
fixed-dimensional IP oracle would cost at least Omega(M) merely to process
the nodes and at most `M poly(K)` with the conservative full enumeration
bound; the exact IP cost and its dimension-dependent constant are additional,
not free. A depth-first implementation can still use polynomial memory.
For N in these size ranges, M=Theta(sqrt(N)), whereas the proposed
`R poly(K)` tree cost is `N^(1/6) poly(log N)`.

The review enumerators themselves cost `M poly(K)` per fixed input for the
position checks, and the all-residue small-size check costs O(M^2) elementary
modular tests. The main audit additionally checks each certificate against
O(K) ancestors. It stores inverse lists and diagnostic sets of O(M) entries.
These are explicitly exponential diagnostics. They supply neither a new
factoring algorithm nor an efficient substitute for IP. The Fourier sums
above prove a count; they are not proposed preprocessing whose computation
is being omitted from an algorithm's runtime.

The conclusion concerns independent per-power tangent/chord bounds and an
exhaustive feasible-node bisection. It does not show how long a particular
deterministic ordering needs to reach its first factor. An IP solver might
return a factor early in a large feasible node, or a different algorithm
might exploit information without enumerating the tree. Even many spurious
descendants can lie below an ancestor where the actual factor is found.
An early-stop lower bound would need a separately specified ordering, solver
witness rule, preprocessing, and adversarial family; none is established here.

Adding more supporting tangents alone does not remove this obstruction:
all such tangents at a chosen t remain at or below t^j, while the same chord
lies at least `mu*d*e/2` above t^j. The interval from t^j to the chord still
contains every residue modulo R for j>=3 in these nodes. Coupled constraints
between different z_j, a different exact query, or a justified early-stop
argument would change the mechanism and require a new costed proposal.
No concrete revision with a complete improved bound survives this review.

**9. Handoff and validation.** Keep the frozen H006 disposition and hashes as
they are. Close its small-full-tree tangent/secant route on the mathematical
obstruction above, subject to the coordinator checking this new derivation;
do not infer a general factoring lower bound or a complexity improvement.
There is no reason to implement a generic IP engine solely to test this
already obstructed full-tree hypothesis. A new proposal must identify which
specific certificates it excludes and price the new primitive, or replace
the full-tree claim with a separately justified early-stop theorem.

The review scripts and witnesses passed. `./scripts/check.sh` also passed:
12 Python tests, the Lean source screen, the pinned Lean build, and the
existing assumption audit. No Lean theorem was added. Validation output is
retained in [H006-review-checks.log](H006-review-checks.log). Verified
factoring improvement remains **NONE**.
