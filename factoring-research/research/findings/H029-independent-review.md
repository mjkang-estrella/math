# H029 — Independent review of capacity, construction, and full costs

2026-10-08. Reviewer role, independently of the proposer. **Verified full
factoring complexity improvement: NONE.** Symbolic review and primary-source
inspection only; no finite experiment, sweep, replay, candidate implementation,
Lean change, shared check/build, package installation, delegation, registry or
checkpoint edit, commit, publication, or scheduler.

**Verdict:** ACCEPT P1–P8 within their stated quantifiers. ACCEPT the restricted
Card A menu obstruction and Card B's coverage, padding, small-leaf invariant,
current complete cost, and conditional implication. CORRECT Card A's unrestricted
parameter-width wording; make the pair order and root initializations explicit
as below. These are local scope/specification repairs, not changes to the parent
capacity constants or Card B's inequalities. REJECT any claim that either card
currently improves complete factoring. Retain one proof-only question about one
realization of the exact RootProduct interface; no fast realization is supplied.

## 1. Frozen review target and access limits

I read all **300 lines** of [H029-submitted-draft.md](H029-submitted-draft.md).
Its SHA-256 is
`dbf3036111778eb9837aba21195265765b9af576d4925eca49b45aba744d7a0e`.
Line references below refer to those unchanged bytes. The live completed report
matched them when frozen. All **21** input-manifest entries and both **2**
delivery-manifest entries independently matched before the audit.

I also read the original intake, construction intake, full H029 hypothesis,
source notes/manifests, AGENTS.md, README.md, docs/SPECIFICATION.md,
RESEARCH_LOOP.md, RESEARCH_TEAM.md, STATE, all of H004's reduction review and
disposition, its original hypothesis and failed construction, the deterministic
W001 baseline discussion, and W001-dynamics Card 1. The user's task-state
correction supersedes STATE's stale proposer labels: H027/H028 reviews are live
and H029's proposer completed. I neither polled nor duplicated those tasks.

[H029-review-sources/](H029-review-sources/) freezes 40 input files, including
the original source snapshots and manifests. Their identities are in
[H029-review-inputs.sha256](H029-review-inputs.sha256), whose SHA-256 is
`fc40fe5601501329dd123f174cc4e63788fc14c000530a2863994c20a23b84c7`.
The original hypothesis hash is
`e94f714ce7520822e8ddfb7d4431d0b3ef4159301c3cc1088682154176b3e533`;
the original parent-intake hash is
`220db361b0921244d787e4b3875d63024f3e74d06aba1a91866966c9892da154`.
Hashes establish byte identity, not mathematical correctness.

I inspected the actual frozen primary HTML/PDF documents, not just the
proposer's summaries. Hittmeir's printed p. 2001 and Rosser–Schoenfeld's printed
p. 69 were also rendered and read visually to disambiguate inequalities and
fractions. Public primary pages for Umans–Wang, Hittmeir, Harvey, and
Harvey–Hittmeir were opened during this review. The retained source identities,
derived reading aids, and access limits are documented in
[H029-review-source-notes.md](H029-review-source-notes.md).

Lehman's original publisher PDF was unavailable with HTTP 403 in the retained
proposer retrieval record. I did not read that original proof and do not claim
to have audited it. Hittmeir's primary paper is the checked authority for the
exact Lehman statement and the representation used here. This is a mathematical
review using cited theorems, not a Lean proof or a machine refinement.

## 2. Parent claims P1–P8

**P1 — ACCEPT (draft 22).** For real R>=2 and L>=ln 2, a finite set B of
integer bases a>=2 with ln a<=L has integer H_a=floor(L/ln a)>=1.
There are finitely many permitted exponent pairs. Selecting a subset,
repeating leaves, changing signs, or selecting B using N cannot enlarge support
beyond all permitted same-base pairs. The implication requires coverage of
*every* prime <=R at the scale under discussion. Empty B cannot provide it.
No assertion about the cost of finding B follows.

**P2 — ACCEPT (24–32).** Swap x,y if necessary. For h=x-y in [1,H_a],

    |a^x-a^y| = a^y(a^h-1).

Every prime divisor therefore divides the positive integer
P_a=a product_(h=1)^H_a(a^h-1). The factor a handles arbitrary valuations in
a^y at the level of support only. It is harmless when y=0. A factor equal to
1 is harmless too. Neither a whole leaf nor its full prime powers need divide
P_a. This distinction is essential.

**P3 — ACCEPT (34–44).** Universal support implies that the squarefree
primorial through real R divides product_(a in B) P_a. Put t=ln a. Then

    ln P_a <= t + t H_a(H_a+1)/2
           <= t + L^2/(2t) + L/2
           <= L^2/(2 ln 2) + 3L/2.

The second inequality uses H_a<=L/t and positivity; the last uses
ln 2<=t<=L. Thus the exact claimed theta(R) bound holds, including all floor
boundaries. The primorial is a proof device and is never algorithmic input.

**P4 — ACCEPT (46–50).** Because L>=ln 2, the right-hand summand is at most
(2/ln 2)L^2. Hence |B|L^2 >= (ln 2/2)theta(R), which implies Omega(R).
This is a necessary support-capacity condition, not a sufficient cover law.

**P5 — ACCEPT (52–57).** The visually checked primary inequalities are
pi(x)>x/ln x for real x>=17 and pi(x)<1.25506 x/ln x for real x>1.
Counting the primes in (sqrt R,R] therefore gives, for every real R>=17,

    theta(R) >= (ln R)/2 [pi(R)-pi(sqrt R)]
             > R/2 - 1.25506 sqrt R.

The strict first interval endpoint avoids any problem when sqrt R is a prime.
The draft's sufficient R>=101 threshold for a lower bound >R/4 is valid
(and deliberately loose): it is enough that sqrt R>4(1.25506).
No numerical prime experiment is used.
[Rosser–Schoenfeld, Corollary 1, (3.5)–(3.6), p. 69](https://doi.org/10.1215/ijm/1255631807).

**P6 — ACCEPT (59).** On any unbounded sequence of successful covered scales,
upper bounds |B|<=R^(kappa+o(1)) and L<=R^(alpha+o(1)), with errors tending
to zero on that sequence, yield |B|L^2<=R^(kappa+2alpha+o(1)). A fixed gap
1-kappa-2alpha>0 contradicts the linear lower bound. The contradiction excludes
successful unbounded subsequences as well as all sufficiently large scales.
It says nothing decisive at equality. In particular kappa=0, alpha=1/3 fails.

**P7 — ACCEPT (61).** Same-base support, universal prime coverage, and a runtime
bound are three different objects. This proof does not cover independent-base
differences or a construction required only to hit divisors of its own input.
The leaf (N+1)-1=N illustrates input-divisor coverage without separation. No
general factoring lower bound or obstruction to all compressed covers follows.

**P8 — ACCEPT (63), with the source's own qualifications retained.** The actual
Umans–Wang text has infinitely-many-scale conjectures, adds prefactoring in
Conjecture 5.1, requires d<=N in Theorem 5.2, and prints d<=R in Lemmas 5.3–5.4
(their parameter n is R). Its prime-progression criterion is a CRT
characterization; §7 already discusses addition sequences. These statements
do not supply H029 with a uniform constructor, dense usable scales, or Leaf.
Theorem 5.5 is conditional despite the preceding paragraph's use of
“unconditional.” The project must independently discharge its stronger
all-input/all-modulus interfaces.
[Umans–Wang v1, §§3,5–7 and Appendix A.2](https://arxiv.org/html/2511.10851v1).

## 3. Contract C and arbitrary composite rings

**C1 — ACCEPT the H004 reduction; make root initialization explicit
(draft 69–80, 158, 231).** For a current input D and a specified nonzero-leaf
family, set

    g = gcd(D, Prod(full interval, D)).

Only if g>1 call Visit(g,full interval). For an interval I let Q_I be its
ordinary integer product, used only in the proof. The invariant is
d|D and d|Q_I. Given left/right products Q_L,Q_U, write
e=v_p(d), a=v_p(Q_L), b=v_p(Q_U). For u=gcd(d,Q_L),

    v_p(u)=min(e,a),
    v_p(d/u)=max(e-a,0)<=b.

Thus both children satisfy the invariant and their divisors multiply to d,
even when they share prime support. An equality gcd shortens the interval.
It does not certify primality. Initializing with D itself without first
establishing D|Q_I is invalid for a support cover with insufficient valuations.
The draft imports the correct H004 algorithm; the displayed recurrence alone
should not be used as a replacement for its root step.

At each depth the product of active divisors divides g. Each nontrivial node
accounts for at least one bit of log2(g), so fewer than n such nodes occur.
The same product argument across terminal divisors bounds their total number
by n, including repeated support. Balanced interval splitting gives depth
ceil(log2 k). Every discarded unit branch still pays for the query producing
it; root products and unsuccessful queries are charged.

**C2 — ACCEPT costs and memory in the cards' polynomial-index regime; qualify
the general wording (67–80).** Let ell=ceil(log2(k+1)). A fully explicit safe
version is

    C_gen + O(n ell (P_*+n^3+ell))
          + O(n L_* + n Pr(n) + n^4 + n ell).

This absorbs the full root query too. It reduces to (C) when ell=O(n), as in
Card B and Card A with the parameter restriction below. For a purported
arbitrary descriptor with much longer indices, keep the ell control cost or
include it explicitly in the primitive bounds. The depth-first stack uses
O(n ell+ell^2) bits, in addition to the descriptor, output and live primitive
workspaces. Discard workspaces before recursing unless their retained storage
is separately charged. Merely controlling scalar residue widths is insufficient.

Deduplicate returned prime labels, validate primality with a fixed deterministic
algorithm of cost Pr(n), and divide **the original input** repeatedly by each
prime. Leaf-list completeness can be checked by exhausting its assigned d.
There are O(n) factor occurrences to strip and at most O(n) prime labels to
validate. Restoring powers from the root quotient instead is wrong. The usual
final-prime conclusion only follows with the original sqrt(D) cutoff; Card B's
smaller cutoff requires its different remainder argument below.

**C3 — ACCEPT the monic polynomial tools with full widths (67).** To multiply
degree-at-most-s polynomials whose coefficients are represented in [0,d),
choose a binary packing slot b with

    2^b > (s+1)(d-1)^2.

Then b=O(w+log(s+1)), where w=bitlength(d), and the packed operands and their
product have O(s(w+log(s+1))) bits. There is no inter-slot carry; unpack the
integer convolution and reduce coefficients modulo d. A fixed quasi-linear
integer multiplier, with the tree levels and traffic paid, gives the stated
soft-O(s M(n+log s)) majorant. It does not multiply s coefficients by a single
n-bit unit-cost operation. Harvey explicitly gives the Kronecker-substitution
width and the product-tree construction in §2.2; no fast field operation is
being silently imported. [Harvey, Lemmas 2.1–2.3](https://arxiv.org/html/2010.05450v1).

For monic remainder trees, reverse the monic divisor: its constant coefficient
is 1. Its formal reciprocal can be computed by precision doubling with
h <- h(2-fh), using additions and multiplications only. The error squares;
there is no division by 2 and no inversion of a nonunit, even modulo an even
composite. Reducing modulo the linear leaf polynomial X-c then evaluates at c.
Repeated evaluation points are permitted. Interpolation requiring inverses of
point differences is neither needed nor authorized. Streaming/recomputing
trees permits the claimed soft-O(s(w+log s)) workspace, with those recomputations
included in time. These algebraic arguments apply to every integer d>=2.

## 4. Card A: product order, real Leaf, and the menu screen

**A1 — CORRECT the parameter scope; ACCEPT the costs within the screened
regime (95–103, 107–117).** The draft initially says only m>=3, but its
O(n^3) common-base arithmetic assumes log m=O(n). An arbitrary N-dependent
m need not meet that assumption. Local repair: restrict this card to
3<=m<=R, with m<R/2 in the obstruction, and a nonempty explicit menu
Q subset [Q_0,R] of distinct certified primes. Alternatively retain arbitrary
m but replace relevant n-bit arithmetic by arithmetic on
w=O(n+log(m+1)) bits and carry its indexing/parameter costs. The first repair
preserves the entire proposed target and the rejection. No unrestricted
m claim with unchanged n^3 factors is accepted.

Parameter selection must be a finite paid procedure, not just a statement
that parameters are functions of N. For supplied computable m,Q_0, scanning
the desired integer interval and deterministically testing each candidate
implements the proposed default menu in its charged O(R(Pr(n)+n^3)) time.
A shorter scan pays its length; any analytic selector pays its own cost.
The explicit list costs O(sn) bits and at least s output operations (indeed
Omega(s log Q_0) output bits). Storing primality-test outcomes does not give
free factorization of the power differences. Empty menus cannot be covers.

**A2 — ACCEPT after fixing a precise order (97–103).** The following completes
the draft's recursive-order description without changing its leaves or bound.
For a consecutive base interval I split at its integer midpoint into I_0<I_1.
List Tri(I_0), then Tri(I_1), then Rect(I_1,I_0). A rectangle is row-major:
u in its upper interval increases in the outer loop, v in its lower interval
increases in the inner loop. Tri on fewer than two bases is empty. Concatenate
these triangle lists for q in increasing menu order. This specifies every pair
2<=v<u<=m exactly once for each q. Cardinalities binomial(|I|,2) and |U||V|
permit index descent using O(n)-bit integers under A1's restriction.

For a rectangle U x V put r_a=a^q mod d. Form

    F_V(X)=product_(v in V)(X-r_v).

Then product_(u in U) F_V(r_u) equals the required product of u^q-v^q modulo d,
with its correct sign. A row-major subinterval is either one partial row or
a suffix of the first row, a block of full intervening rows, and a prefix of
the last row. There is no double counting when both endpoints share a row.
Each piece is a rectangle and has a monic product/evaluation realization.

A contiguous interval of a triangle list has at most two partial children
at any recursion depth. Its fully included pieces are complete triangles or
rectangles; the partial rectangles use the preceding decomposition. A complete
triangle of b bases costs soft-O(b) coefficient work: each level's cross
rectangles use total O(b) coordinate length over O(log b) levels. The boundary
decomposition contributes only logarithmic factors (even summing the generous
O(m) bound at each of O(log m) depths suffices). Therefore every partial or full
pair interval costs soft-O(m) coefficient work per exponent. An interval across
menu blocks has at most two partial blocks and complete blocks between them,
so summing over at most s exponents yields (A-P).

Generate the r_a by repeated squaring for all bases, paying O(log q)
modular multiplications per base in every query/modulus where they are needed.
All residue arrays, polynomial coefficients, menu reading and boundary decoding
are charged. Exact q-th powers have Theta(q log m) bits at the largest bases;
their logarithmic-size exponents do not license expanding those powers for
free. C3 proves validity for all 2<=d<=N, including composite/nondivisor moduli.
No field interpolation or inverse of u^q-v^q is used.

**A3 — ACCEPT actual Leaf, including exceptions and powers (105–117).** Factor
gcd(u,v) and u-v by ordinary complete trial division, then strip every power
from d of their prime divisors and of the known prime q. Factoring integers
<=m, forming the gcd, and stripping powers have the corrected width bound
from A1. If a prime p divides the residual, then it divides neither u nor v:
dividing one and the difference would force it to divide the other, which was
already handled. It also divides neither u-v nor q. Hence u/v has exact order
q in F_p^*, so p=1+jq for a positive integer j.

Try these integers in increasing order through the square root of the changing
residual, dividing each successful one to exhaustion. If a successful candidate
c were composite, a prime r<c dividing c would divide the current residual.
That prime also lies in the progression, and r<=sqrt(c)<=sqrt(residual), so it
would already have been stripped. Contradiction. Thus successful candidates
are genuine primes. If the loop ends with residual h>1 composite, its least
prime factor <=sqrt h would likewise have been tried. The final residual is
therefore prime. All powers are stripped, not just one occurrence. A candidate
or final prime is proper whenever the current integer being split is composite;
returning a prime input as itself is appropriate for prime-factor output.

There are at most R/q failed progression candidates, and O(n) successful
divisions/labels. Thus (A-L) holds within A1's corrected regime, with optional
deterministic output validation charged in C. No nonunit inversion is used by
the algorithm; the ratio argument takes place only in the proof over F_p.
For arbitrary query d, modular powering first obtains gcd(d,u^q-v^q), and the
same routine factors that gcd. Equality of a leaf gcd with d is not a failure.

**A4 — ACCEPT necessary coverage and explicit supply (121–136).** If p>m,
it cannot divide a base or u-v, so the draft's relaxed necessary alternative
p=q or q|p-1 holds. In fact p=q>m cannot occur either, by Frobenius
u^p-v^p=u-v modulo p, but generously allowing that exception only weakens the
valid upper count. No sufficient collision law for the short base interval is
asserted.

For m<R/2 and q>=Q_0 each exponent can account for at most
1+floor((R-1)/q)<=1+R/Q_0 upper-half primes. The primary bound (3.8) is

    pi(2x)-pi(x) > 3x/(5 ln x),       real x>=20.5.

Thus, for real R>=41 and 2<=Q_0<=R, a universal cover requires

    s(1+R/Q_0) >= pi(R)-pi(R/2) > 3R/(10 ln(R/2)),
    s > 3Q_0/(20 ln(R/2)) > 3Q_0/(20 ln R).

This proves the claimed uniform Omega(Q_0/log R), with explicit range and
constant. Overlap and unrealizable potential collisions only strengthen the
obstruction. No assumption on safe-prime infinitude or progression density
enters. [Rosser–Schoenfeld, Corollary 3, (3.8), p. 69](https://doi.org/10.1215/ijm/1255631807).

**A5 — ACCEPT the restricted rejection; REJECT broader interpretations
(138–150).** To certify the displayed progression-search majorant at
R^(gamma+o(1)), this proposal chooses all q>=R^(1-gamma-o(1)) and
sqrt m<=R^(gamma+o(1)). Supply then forces s>=R^(1-gamma-o(1)). For
gamma<2/5, merely outputting this explicit menu already exceeds R^gamma.
This rejects the high-order explicit-menu representation and its chosen
uniform Leaf certificate, before the slower default prime generation is used.

An upper runtime bound containing R/q does **not** prove that a smaller q
forces that much actual runtime: a particular leaf may strip immediately or
be recognized prime. Nor does this count exclude an implicit menu, a different
leaf algorithm, or a different coverage theorem. The draft states these limits
correctly. The power-map/order mechanism is already present in W001-dynamics
Card 1; cyclotomic names do not supply prime factors. No improved Card A
factoring algorithm survives.

## 5. Card B: all-input reduction, padding, and factor extraction

**B1 — ACCEPT with explicit root initialization (158–172).** For N_0>=2 set
K_0=ceil(N_0^(1/3)), and take the consecutive leaves 2,...,K_0. Initialize

    g_0 = gcd(N_0, Prod(2,...,K_0; modulus N_0)).

Descend only on g_0 when it exceeds 1. This captures the support of every
prime <=K_0 dividing N_0, without assuming the factorial contains enough
copies of each prime to contain N_0 itself.

For any queried interval [a,b] of r integers choose h=ceil(sqrt r), form
F(X)=product_(j=0)^(h-1)(a+X+j), evaluate at X=0,h,... for the complete
h-term blocks, and multiply the fewer than h trailing terms. This uses
soft-O(sqrt K_0 M(n+log K_0)) time and soft-O(sqrt K_0 n) bits, by C3,
for every 2<=d<=N_0. There is no prime enumeration through the cutoff.
At singleton i, the visited divisor d divides i, so d<=i<=K_0; ordinary trial
division fully factors it in O((sqrt K_0+n)n^3) time. C's traversal and output
charges give the stated N_0^(1/6)poly(n) preprocessing bound.
This is a known factorial-product method; Harvey's Proposition 2.5 supplies
the same small-factor scale. [Harvey, §2.3](https://arxiv.org/html/2010.05450v1).

Collect the returned primes and strip **all** their multiplicities from original
N_0. The remaining M has no prime divisor <=K_0. Three remaining prime factors,
counted with repetition, would have product >K_0^3>=N_0, impossible. There
are therefore at most two. It would be illegal to call this remainder prime
using H004's sqrt(N_0) final-prime argument; the draft correctly avoids doing so.

Handle M=1, a deterministically tested prime, a square p^2, and bounded M<4096
separately, recording and checking multiplicities. In the square case p is
prime because M has at most two prime factors with repetition; it may also be
validated directly. Otherwise M=pq with distinct odd primes K_0<p<q.
No uncovered large prime is discarded. All-input factorization is reduced to
this case, not assumed at input.

**B2 — ACCEPT exact theorem application (168–181).** The theorem actually read
in Hittmeir's Theorem 2.1 has these hypotheses, with its eta renamed K:

    M is a positive odd integer; K is an integer with 1<=K<sqrt M;
    M=pq for primes p,q, with sqrt(M/(K+1))<p<=sqrt M.

Its conclusion is the existence of integers x,y>=0 and 1<=k<=K with

    x^2-y^2=4kM,
    0<=x-2sqrt(kM)<=sqrt M/[4sqrt k(K+1)],
    x=ap+bq, y=|ap-bq|, k=ab,       a,b positive integers.

The representation is explicitly included in Hittmeir's statement; his
following paragraph attributes it to equation (4.6) of Lehman's proof, while
distinguishing it from the original theorem's formulation.
[Hittmeir, Theorem 2.1, printed p. 2001](https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf).

For the actual input set K=ceil(M^(1/3)). Monotonicity gives K<=K_0<p.
For M>=4096, K<=2M^(1/3)<sqrt M. Finally
K>=M^(1/3)>sqrt(M/(K+1)), since K+1>M^(1/3). Every hypothesis holds,
including integrality and strictness. The distinct-prime restriction is an
additional preprocessing property, not a hidden omission in the cited theorem.
Local exposition repair: put the full hypotheses above alongside B-Lehman
instead of referring only to “the last inequality.” The application is correct.

**B3 — ACCEPT padding, including endpoints (185–202).** For a band with
l=2^j<=k<=h=min(2l-1,K), define

    B_j=sqrt M/[4(K+1)sqrt l],  T_j=1+ceil B_j.

Let x_* be the theorem's integer and c_k=ceil(2sqrt(kM)). Since x_* is an
integer at least 2sqrt(kM), t_*=x_*-c_k is a nonnegative integer, and

    t_* <= x_*-2sqrt(kM)
        <= sqrt M/[4(K+1)sqrt k] <= B_j <= T_j.

Thus the row t=t_* is included. If the lower endpoint itself is integral,
t_*=0 remains included; equality in the theorem's upper bound is included as
well. No open-interval rounding or floating-point assumption occurs. At that
row z=x_*^2-4kM=y_*^2, so floor(sqrt z)=y_*. The two linear leaves are
{2ap,2bq}; hence both actual prime divisors of M are covered.

The ceiling defining T_j is computable as the smallest integer z>=0 with
16(K+1)^2 l z^2>=M, followed by adding 1. It is an ordinary integer comparison,
not a modular root. Extra padding and nonsquare rows do not alter coverage.

**B4 — ACCEPT volume and indexing (200–211).** Write c_j=h_j-l_j+1 and
w_j=T_j+1. Since w_j<=3+B_j and c_j<=l_j,

    V=sum_j c_j w_j
      <=3K + sqrt M/[4(K+1)] sum_j c_j/sqrt(l_j),
    sum_j c_j/sqrt(l_j)
      <=sum_(j=0)^J 2^(j/2) <=(2+sqrt 2)sqrt K.

Consequently

    K<=V<=3K+(2+sqrt 2)/4 * sqrt(M/K),

so V=Theta(M^(1/3)) for the chosen K. The potentially truncated last band,
including a singleton last band when K is a power of two, satisfies the same
bound. All K rows have at least one t, so the lower bound is genuine.

For completeness, an exact zero-based decoder for leaf i is as follows. Set
F_j=2c_j w_j and P_j=sum_(h<j)F_h. Find the unique j with
P_j<=i<P_j+F_j; put delta=i-P_j, sign=delta mod 2, r=floor(delta/2), and

    k=l_j+floor(r/w_j),    t=r mod w_j.

Sign 0 is minus and sign 1 plus. This specifies all partial/full interval
endpoints without a root table. There are O(n) bands. Prefix counts, endpoints,
widths and denominators have O(n) bits. Computing each width by binary search
uses O(n) exact O(n)-bit comparisons/squares, hence O(n^3) schoolbook time;
O(n) bands give O(n^4) Gen and O(n^2) descriptor bits. Scanning the descriptor
and dividing to decode one index fits O(n^3), including sequential access.
These are charged finite algorithms described symbolically, not executed code.

**B5 — ACCEPT strict positivity and height (215–225).** Put v=M^(1/6)>=4.
Because y=floor(sqrt(x^2-4kM))<x, both leaves are positive and
A_+<2x. The draft's inequalities give

    T_0<=2+v/4,
    2x<=4sqrt(2) M^(2/3)+6+v/2.

Here 4sqrt(2)<6 and 6+v/2<=2v<2v^4=2M^(2/3). Thus

    1<=A_-<=A_+<8M^(2/3)<M,

since M^(1/3)>=16>8. All bounds are valid at M=4096 as well as above it,
without a finite check. Products kM, x^2 and root arguments may have more
than n bits, but only O(n) bits: k=O(M^(1/3)), x=O(M^(2/3)), and
16(K+1)^2 l=O(M). The integer computations and binary searches therefore
fit their O(n^3) conservative arithmetic charges. They are not unit-cost
operations on M-sized values.

**B6 — ACCEPT cheap visited Leaf and complete recovery (227–231).** For this
second descent initialize

    g_1=gcd(M, RootProduct(M,full interval,M)).

The proved support includes p and q, and M is squarefree, so g_1=M. Writing
the root gcd is nevertheless useful for keeping the interface and paid root
query explicit. Every terminal d divides both M and its assigned positive
leaf A<M. Since the only nontrivial divisors of M are p,q,M, it follows that
d is p or q. Recompute A, check d|A, test d deterministically for primality,
and return d. The cost is O(n^3+Pr(n)); it does not factor an arbitrary A or
invoke trial division on the visited path.

For a total query on arbitrary 2<=d<=M, first take h=gcd(d,A), return the
empty list if h=1, use deterministic primality testing for prime h, and otherwise
trial-divide h completely. Since h<=A<8M^(2/3), this fallback costs
O((M^(1/3)+n)n^3+Pr(n)). It is a valid total routine, but is not the cheap
visited bound. Preprocessing and the invariant prove that its composite-h
branch is unreachable in the actual squarefree-semiprime descent. An invariant
failure should be reported as an error in a checked realization, not excused
by silently invoking this expensive fallback in its complexity theorem.

Internal gcd=M is allowed: each such recursion shortens the interval. It
cannot persist to a terminal node carrying M because A<M. Terminal divisors
multiply to M, so both primes are recovered; indeed there are at most two
nontrivial terminal nodes in this special case. Repeated leaves, including the
two equal signs when y=0, are allowed. They do not manufacture multiplicity
in the partitioned input. Restore original N_0's exponents, combine with the
preprocessing output, validate prime labels and reconstruct N_0. This gives
full prime factorization for every initial input, with no final unvalidated
large-prime assertion.

**B7 — ACCEPT current all-modulus product, total time, and memory (235–248).**
For every M>=4096, arbitrary 2<=d<=M, and every valid interval, decode indices,
compute the ordinary integer roots, form each actual A, reduce it and multiply
modulo d. Every output is the specified residue, without using a semiprime
promise. Sequential index decoding and the two exact roots fit O(n^3) per
leaf. Both signs, nonsquare rows, duplicates and full-root queries are paid.
The full query costs O((K+sqrt(M/K))n^3)=O(M^(1/3)n^3) and can be streamed
in polynomial space.

Combining this with C and preprocessing proves the supplied upper bound
N_0^(1/3)poly(n) for a mathematically specified finite complete method.
The full root query in this particular enumeration algorithm already visits
Theta(M^(1/3)) rows. This is a cost of that supplied algorithm, not a lower
bound for RootProduct or factoring. Peak space is
soft-O(N_0^(1/6)n)+poly(n): discard preprocessing buffers before the
polynomial-space second stage, and charge any retained data. No implementation
or timing theorem is asserted. This upper bound is worse than the established
deterministic exponent-1/5 full-factorization benchmark.

## 6. Conditional primitive, prior art, and one next question

**B8 — ACCEPT the exact interface and conditional implication; REJECT any
unconditional speedup (252–273).** RootProduct must return the product of the
ordered leaves in B3 for **every integer M>=4096**, with
K=ceil(M^(1/3)), **every arbitrary integer 2<=d<=M**, and any nonempty valid
inclusive interval, including singletons and the full interval. If empty
intervals are offered, define their result as 1 mod d. M need not be prime,
squarefree or semiprime for this interface. The parameters and descriptor use
M only. After reduction the core input is M, so its all-modulus domain is
d<=M; the earlier preprocessing separately satisfies d<=N_0. There is no
modulus-domain loophole in that two-stage composition.

Let C_P charge all once-per-M preparation, including producing reusable data,
and let P charge each query, including any modulus-specific preparation and
data access. Let S_P and retained-data size be explicit. A reusable object may
not be built without charge when the recursion changes modulus or interval.
With these conventions the draft's B-target follows directly from C. For
fixed tau>=0 and a uniform bound

    C_P(M,n)+P(M,n)<=M^(tau+o(1))poly(n),

the all-input complete bound is
N_0^(max(1/6,tau)+o(1))poly(n). Uniformity absorbs small M into the polynomial
term and ensures M<=N_0 can be used in the majorant. The root query, all later
queries, preparation, leaf work, primality, powers and output are included.
Space is the maximum of the two phases, conservatively bounded by their stated
sum plus retained data. A fixed tau<1/5 would improve the deterministic power;
tau=1/6 reaches the stated aspiration. No such uniform product algorithm is
provided, proved, or accepted by this review.

**B9 — ACCEPT the shortcut exclusions with a precise scope (277–284).** Integer
squaring itself *does* commute with reduction. Taking an ordinary floor or
ceiling square root generally does not: a residue does not determine the
integer root or the inequalities defining it. Thus one cannot compute the
nested-root leaves by reducing their arguments first.

For an actual row, z=x^2-4kM, y=floor(sqrt z), and e=z-y^2 is an integer with
0<=e<=2y. Therefore

    A_- A_+ = 4kM+e.

Replacing this by e modulo d is valid exactly when d|4kM (in particular when
d|M), not for arbitrary d<=M. A square row has e=0. Treating that zero as an
indivisible replacement leaf with no retained linear decomposition leaves
gcd=M and removes the stated cheap-leaf proof. Pairing is not intrinsically
forbidden: retaining the row and an explicitly paid recovery of its two
linear factors could justify a different Leaf. It would still need its own
all-modulus products and cost proof. The present proof uses the two positive
linear leaves and grants no speedup from the small error e alone.

An explicit root list, scalar product tree over it, or fully interpolated
coefficient list already pays Theta(M^(1/3)) items. A resultant label does not
remove its degree, coefficients, preparation or access costs. The rejection
applies to such explicit realizations, not all possible representations.

**B10 — ACCEPT attribution and benchmark (82, 284–300).** Harvey's Lemma 3.3
and Remark 3.4 discuss the O(r+sqrt(M/r)) Lehman candidate count and explicitly
raise a full square-root speedup at r approximately M^(1/3) as a possible
route to exponent 1/6. Neither that ambition nor square-difference search is
new here. This review makes no priority claim for the padded leaf interface.
[Harvey, §3, Remark 3.4](https://arxiv.org/html/2010.05450v1).
The matched established deterministic full-factorization bound is
O(N^(1/5)(log N)^(16/5)/(log log N)^(3/5)) bit operations in the finite-tape
model, as stated in Harvey–Hittmeir's Theorem 1.1. That is not a heuristic
GNFS comparison. [Harvey–Hittmeir, Theorem 1.1](https://arxiv.org/html/2105.11105v1).

**Next question — ACCEPT as one bounded proof-only attempt, not a promised
algorithm.** For one specified algebraic realization of the exact B8 interface,
can the proposer prove a uniform identity and complete bound
C_P+P<=M^(tau+o(1))poly(n) for a fixed tau<1/5, ideally tau=1/6, with every
interval, composite modulus, index and intermediate width charged? The attempt
must expose its finite operations and any retained data. A root oracle,
factor/order advice, explicit Theta(M^(1/3)) preparation, or validity only for
d|M rejects that realization under this interface. Failure of one realization
does not prove the interface impossible. No finite timings or exponent fit
would discharge these obligations, and none is selected or authorized here.

## 7. Localized disposition for the coordinator

The following edits would make an acceptance version self-contained while
preserving the reviewed draft:

1. At Card A's parameter declaration (95), impose 3<=m<=R and a nonempty menu,
   charge parameter selection, and retain m<R/2 for the screen. Alternatively
   carry log m in every arithmetic/index bound. This is the actual scope
   correction required for the displayed n-bit Leaf costs.
2. At the pair-order paragraph (97), specify the triangle/row-major rectangle
   order and its same-row interval case as in A2. The soft-O product bound
   remains unchanged.
3. At C/B1/B4 (69–80, 158, 227–231), spell out g_0 and g_1 and the invariant
   before descent. Qualify the simplified C envelope by log k=O(n), or retain
   the explicit index charges from C2. The imported H004 proof already has the
   correct initialization; this prevents an incomplete standalone transcription.
4. At B-Lehman (176), display all the theorem's hypotheses from B2. At the menu
   supply citation (136), adding R>=41 and the explicit constant in A4 makes
   the real-boundary statement directly checkable. Neither changes the result.

No correction to P1–P7's constants, Card B's dyadic width/volume/height formulas,
the visited-prime shortcut, or the conditional max(1/6,tau) exponent is needed.
The completed mathematical core is accepted at the scope proved here. Card A's
high-order explicit-menu certificate is rejected, Card B's faster product is
unresolved, and **verified full factoring complexity improvement remains NONE**.

Only this review and adjacent H029-review-* evidence were written. Existing
findings, hypotheses, primary snapshots, shared code, Lean, STATE and registries
were left unchanged. Input freezing, document extraction/rendering and hash
verification are evidence handling, not a factoring experiment or replay.
