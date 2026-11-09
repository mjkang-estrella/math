# H021 independent mathematical review

2026-10-08. Disposition: **REVISE one optimizer-recovery sentence; accept the
core constructive lemmas in the restricted scopes below.** Verified full
factoring complexity improvement: **NONE**.

The prefix optimizer, suffix enumeration, count/unranking construction,
bounded-error rational log generator, and precision inequalities survive
independent mathematical review. There is one localized correctness issue:
the suffix table capped at E+1 cannot generally recover the box optimizer
when the minimum exceeds E. The uncapped prefix table and its predecessor
recovery already give a correct implementation at the stated cost. This
correction does not invalidate global minimization using E=T².

Reviewed source: [H021-structured-lattice-generator.md](H021-structured-lattice-generator.md),
all 577 lines, SHA256
`bba886b8995f0020cc22e28c8a8fc51f59b162a7008068bd6ed9dede8d664915`.
Line references below refer to these bytes. I also read AGENTS.md, README.md,
docs/SPECIFICATION.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md, research/STATE.md,
[H021](../hypotheses/H021.md), and the
[literature follow-up](2026-10-08-literature-followup.md).
STATE is live coordinator context, not frozen mathematical evidence.

This was an analytic review. No executable mathematical check, finite
experiment, benchmark, useful-yield sample, package installation, Lean work,
recursive delegation, commit, publication, or scheduler was performed.
Only this review file was created; the proposer report and all shared files
remain outside this reviewer's write scope. No implementation or formal
machine refinement is certified by this review.

**1. Original domain and primary-source interpretation — ACCEPT.**

The January 26, 2026 revision's equations 20–21 give the stated diagonal
weights and rounded logarithm row. Equations 25–28 concern reduced-basis
corrections. Equation 29 omits sweep count based on convergence observations;
equations 30–31 add transverse fields. These support the report's domain
distinctions, without supplying a complexity or useful-supply theorem.
[Tesoro et al., Methods](https://arxiv.org/html/2410.16355v3).

For supplied integer data, the reviewed problem is exactly

    F(e) = sum_j f_j² e_j² + (sum_j a_j e_j - T)²,
    e in Z^k, k>=1, f_j>=1 integers, a_j,T integers.

If D=BU with U unimodular, reduced coefficients c+diag(sigma)x map to
Uc+U diag(sigma)x. This affine binary image generally couples the original
coordinates. Nothing in the DP identifies that image with its independent
coordinate box. Filtering accepted DP outputs for another domain need not
preserve output delay or uniformity. The DP also does not sample the perturbed
Hamiltonian's measurement distribution. Generic CVP hardness and product
eigenstates of the unperturbed Hamiltonian do not invalidate this construction
or settle the actual sampler.

**2. Box, prefix minima, and global minimization — ACCEPT, with the recovery
correction in item 3.**

Nonnegativity gives f_j²e_j²<=E for every accepted vector. Since f_j is a
positive integer,

    R_j = floor(isqrt(E)/f_j) = floor(sqrt(E)/f_j).

Indeed an integer x satisfies f_j|x|<=sqrt(E) precisely when it satisfies
f_j|x|<=isqrt(E). Signed or zero a_j do not affect this reasoning. The
triangle inequality puts every length-j prefix sum in [-S_j,S_j], where
S_j=sum_{i<=j}|a_i|R_i. The signed partial sums need not be monotone.

Partitioning the possible prefixes by their last coordinate proves recurrence
(1). Infeasible states require a flag, rather than a finite value that might
be confused with an attainable cost. Every attainable prefix cost is at most
jE. For every attainable final sum, its least diagonal cost combined with
(s-T)² gives the least F at that sum. Minimizing over s therefore computes
the minimum on the whole box, even when it exceeds E.

The zero vector has cost T². At E=T², every vector capable of attaining or
improving that cost is in the finite box. Its box minimum is thus a global
minimum; no separate existence assumption is needed. For T=0, positivity of
the f_j makes zero the unique minimizer. For E=0 and T!=0, the box is just
zero and its minimum T² exceeds the cutoff; enumeration and counting must
return an empty accepted set. The proposed recurrences do so.

**3. Recovery using the capped backward table — REVISE; reject its unrestricted
use for arbitrary-cutoff box optimization.**

Lines 79–81 offer either minimizing prefix predecessors or "the backward
table below" to recover a minimizing vector. The prefix option is correct.
The backward table in (4), however, is capped at E+1. It loses comparisons
between completion energies above E. This is relevant because lines 82–89
explicitly allow a box minimum above E.

An analytic family shows the loss without an experiment. Take k=1, f_1=a_1=1,
E=1, and any integer T>=3. The box is {-1,0,1}. Every terminal residual
square is at least (T-1)²>2, so V_2(x)=2 for all three choices. Minimizing
x²+V_2(x) selects x=0. The true box objective is x²+(x-T)² and selects x=1:
its difference from the value at zero is 2-2T<0, while the value at -1 is
larger than the value at zero. Thus the proposed capped completion costs
cannot justify the claimed alternative recovery in this regime.

Required replacement for the sentence at lines 79–81:

> Store a minimizing predecessor at every reachable prefix state to recover
> an actual box minimizer. The capped backward table in section 3 can instead
> recover an optimizer by following minimizing transitions when the minimum
> is at most E, in particular when E=T². It is insufficient for general
> box-optimizer recovery above the cutoff.

It is enough to retain the report's prefix-predecessor route. No new algorithm
is needed. Removing the cap from the backward recurrence is another possible
repair, but is unnecessary for accepting the existing correct route. The
threshold DFS in section 3 itself enumerates accepted vectors; an optimizer
obtained from V must follow minimizing transitions, not merely the first
accepted lexicographic path.

This is a local statement correction, not a failure of the global optimizer,
its complexity, or the enumeration theorem.

**4. Bit widths, initialization, storage, and memory access — ACCEPT.**

The report's b includes input coefficient and weight widths, log(k+1),
log(E+1), log(|T|+1), and log(S+1). Constant multiples of b accommodate all
of the following:

- R_j and each signed exponent; L_j and the list offsets, since
  L<=k(2sqrt(E)+1).
- Signed shifts a_jx, sums in [-S,S], and predecessor expressions even when
  they fall outside the permitted interval.
- Diagonal costs up to kE and terminal squares up to (S+|T|)². The latter
  are not bounded by E and must be formed before terminal comparison/capping.
- Addresses in the kQ tables, input/list positions, and the extra budget
  dimension in the counting tables. The logarithm of kQ(E+1) is O(b).
- A supplied large f_j even when R_j=0. Its input bits must still be read;
  precomputing (f_j x)² respects the bound.

Exact binary-search square root and divisions fit O(kb³). The L precomputed
choices cost O(Lb²) time and O(Lb) bits. Terminal squares cost O(Qb²), and
the at most QL transitions use O(b) time each with the declared indexed
memory model. Initializing all rows costs O(kQb), already covered since
L>=k. Thus equation (3),

    O(kb³ + (L+Q)b² + QLb),

is a valid bound in that model. The rolling-value memory and the retained
predecessor memory are correct. Recovery by scanning prefix values assumes
all needed rows were retained; just two rolling rows do not provide that
recovery. Storing predecessor choices gives the stated O(kb) recovery;
scanning all choices along one recovery path gives O(Lb).

The report explicitly charges address/data access instead of claiming free
unbounded RAM operations. Its conservative tape factor is also sufficient:
the retained table, lists, and input occupy O((kQ+L+k)b) bits. Scanning them
per logical access is bounded by multiplying the indexed cost by
O(1+kQ+L), since Q>=1 absorbs the k term. This realizes a loose polynomial
bit bound on fixed multitape machinery. It is not a verified implementation,
a Python runtime bound, or a Lean refinement.

**5. Capped suffix invariant and worst-case enumeration delay — ACCEPT.**

For each j and prefix sum s, let W_j(s) be the exact least remaining diagonal
cost plus terminal residual square over the remaining coordinate box. By
backward induction, (4) stores min(E+1,W_j(s)). The induction uses
nonnegative transition costs: c+min(E+1,w), when capped again, equals
min(E+1,c+w). Domains [-S_{j-1},S_{j-1}] are correct because
|s+a_jx|<=S_{j-1}+|a_j|R_j=S_j. Unreachable prefix sums are harmless.

At an actual prefix with spent diagonal cost q, condition (5) is equivalent
to existence of an accepted completion through that choice. If the stored
value is E+1, the nonnegative spent cost makes descent impossible. Otherwise
the completion value is exact and attained in a finite suffix box. Therefore
every entered child has an accepted leaf, and every accepted vector passes
every test on its path. Leaves are unique coordinate sequences, so the
enumeration is complete and has no duplicates.

The delay argument is worst-case, not amortized. Between consecutive outputs,
DFS first retreats along one ancestor path and then descends along one path
to the next output. At each depth, only the untried children on the retreating
path and the children tested on the descending path can be scanned. There
are at most 2L_j such trials. Entering a feasible child cannot lead to a
completed traversal with no intervening output. Stack changes and exponent
output fit O(kb)<=O(Lb).

Before the first output only the descending part is needed; after the last
only the retreating part is needed. If there are no outputs, V_1(0)>E
certifies that immediately after preprocessing. Consequently O(Lb) covers
each of these delays, with total T_DP+O((M+1)Lb). The stated full-scan tape
delay O((1+kQ+L)Lb) is valid. Retained outputs are additional storage, and M
can be exponential. The order is lexicographic, with no cost-order claim.
An extra membership or smoothness filter does not inherit this delay bound.

**6. Counting, unranking, and random bits — ACCEPT.**

The terminal indicator in (7) is correct for each remaining budget h. At
earlier levels, choices of x partition the suffixes and subtract precisely
their diagonal cost. Repeated sums or zero a_j create no overcounting: the
coordinate choice, not just the weighted sum, distinguishes vectors. Thus
A_1(0,E)=M exactly.

Every stored count is at most P_box=product_j L_j. With

    beta = 1 + sum_j ceil(log2 L_j),

P_box<2^beta, including when all L_j=1. Partial accumulated counts have the
same bound. A count addition/copy costs O(beta), while sums, budgets, and
addresses cost O(b). Initialization of the terminal budget cells and all
zeroed rows is covered by Q(E+1)L(b+beta), since L>=k. The extra E+1 factor
is necessary and is present. Equation (8)'s time and storage bounds are valid.
Only counting M permits rolling rows; the unranking procedure retains all
needed suffix rows. Its tape multiplier also correctly counts cells with
b+beta payload bits rather than treating a large count as a unit word.

At each unranking step, child completion counts partition the current rank
interval into contiguous blocks. Subtracting entire blocks and entering the
unique containing block proves a bijection between [0,M-1] and accepted
vectors. Zero blocks are skipped and all ranks terminate in an accepted leaf.
At most L choices are inspected, giving O(L(b+beta)) extra indexed work and
O(kb+beta) scratch, as claimed.

For M>1, d=ceil(log2 M) bits give an acceptance probability M/2^d>1/2,
or 1 when M is a power of two. Rejection preserves uniformity on the valid
ranks. Expected draws use at most 2d bits and O(beta) rank-generation work.
Adding deterministic unranking gives the total expected sampling work after
preprocessing. M=0 and M=1 are handled correctly.

The uncapped rejection scheme has no finite worst-case time/random-bit bound
in general. Capping at t attempts uses at most td random bits, has rank
generation work O(t beta), and fails with probability at most 2^(-t). Every
successful returned rank is exactly uniform even after this cap. The report
correctly keeps failure explicit; an expected-time sampler is not promoted
to the repository's worst-case bounded randomized factoring contract.

**7. Prime construction, primorial, and rational logarithms — ACCEPT.**

The corollary to Theorem 3 gives p_k<k(log k+log log k) for k>=6, as cited.
[Rosser–Schoenfeld, 1962, printed p. 69](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).
For those k, log log k<log k<k makes this less than 2k²<4(k+1)². The first
five primes handle the remaining k. Thus the integer cutoff U used by the
proposer is sufficient without numerically evaluating logarithms. Exhaustive
candidate trial division makes O(U²) divisions of O(log(U+2))-bit integers;
the claimed time and prime-list storage follow. This factors small candidate
primes during setup, not N or a supplied factorization of N.

The optional primorial's bit length, sequential multiplication cost, and
conservative gcd cost are valid. Neither construction nor the gcd supplies
uncharged advice or a guaranteed proper split. Computing C by repeated
multiplication by 10 and generating the concrete weights are also paid.

For the log series, t in [0,1/3] implies the tail bound

    2 t^(2n+1)/((2n+1)(1-t²))
    <= [3/(4(2n+1))] 3^(-2n) <= 3^(-2n).

This proves (9) including the endpoint used for log 2. Decomposing
x=2^m y yields log x=m log 2+log y, so q_x is a lower rational bound with
error at most (m+1)9^(-n). The integer stopping rule for n bounds that error
by 1/(4C). Exact rational rounding differs from Cq_x by at most 1/2; hence
its distance from C log x is at most 3/4. No test for the true logarithm's
side of a half-integer is needed. x=1 causes no exception.

To justify the width claim, generate each power of t incrementally. Its
numerator and denominator widths grow linearly in the power, not by repeated
resquaring of an unnecessarily unreduced expression. Term r then has width
O((r+1)b_x+log(r+2)). Multiplying term denominators when summing gives width
bounded by their sum, O(n²(b_x+log(n+2))). Numerators have at most this width
plus the logarithm of the sum's magnitude. Combining the two series,
multiplying by m and C, and forming the rational interval add the displayed
logarithmic terms. This supports d_x and O(n d_x²) work with O(d_x) scratch.
Choosing n and reading x fit inside the bound. Retaining all certificates
would require additional storage, as the report says.

This establishes the specified changed generator. Literal nearest-log
rounding, equality with the paper's coefficients, and equality of candidate
distributions are not established or needed for this result.

**8. Polynomial magnitude scope and materialized outputs — ACCEPT.**

The coefficient bounds in (12) follow from p_k=O(k log(k+2)), the rounding
error, and log N=O(ell). They imply the bounds on S,L and beta. Numerical
k,C,E bounded by polynomials in ell, polynomial input weight widths, and
polynomial-time parameter generation suffice for the complete construction.
Finitely computable but arbitrarily slow public parameter rules would not
suffice; the report charges these costs and supplies a concrete efficient rule.

For k=ell, the smallest power of ten C>=ell, and f_j=ceil(j/2), one has
C<10ell, T=O(ell²), E=O(ell⁴), max|a_j|=O(ell log(ell+2)), and R_j=O(ell²).
Summing these bounds gives the stated S=O(ell⁴ log(ell+2)) and L=O(ell³).
The looser bounds suffice; exploiting larger f_j is unnecessary. Prime/log
setup, the DP tape factors, and beta are polynomial for this N-only rule.
Thus the reviewed primitive exists for every N>1 under these parameters.

The distinction between coefficient magnitude and precision bit count is
essential. c=O(log ell) gives polynomial C=10^c, whereas log C=poly(ell)
alone does not make Q or the counting budget range polynomial. No logarithm
algorithm can remove this DP's explicit numerical ranges merely by computing
their endpoints efficiently.

For an output e, log2 u and log2 v are bounded by the relevant portions of
sum_j R_j bl(p_j). Multiplication by N adds at most ell bits, and
|u-Nv|<=max(u,Nv). The report's H safely bounds all four output magnitudes.
Binary powering uses O(B_e) multiplications of O(H)-bit integers, and the
subtraction and multiplication by N fit the same bound. Skipping zero
exponents avoids unnecessary powers. Thus O((B_e+1)H²) work, O(H+kb) scratch,
and the stated exponent and retained-integer output costs are valid in the
given construction. Unique prime factorization proves both gcd(u,v)=1 and
injectivity of e -> (u,v); it does not prove distinct parity columns.

**9. Log error, integer cancellation, and sufficient precision — ACCEPT.**

Write d_j=a_j-C log p_j and d_T=T-C log N. Direct substitution gives

    C delta = z - sum_j d_j e_j + d_T.

The triangle inequality yields (13) with h=epsilon(1+sum|e_j|).
Exponentiating an interval is order-preserving and gives (14), including
the signs of its endpoints. Equation (15) follows; in particular the exact
relative difference |u-Nv|/max(u,Nv) is 1-exp(-|delta|).

Condition (16) is sufficient for |w|<=W. Replacing v and |z|+h by upper
bounds V and J only strengthens it. For 0<=t<=1, exp(t)-1<=2t; for
0<=x<=1, x/2<=log(1+x)<=x. These prove the rational sufficient conditions
and the interval [JNV/W,2JNV/W] for the sufficient threshold in C. There
is no converse conclusion about actual cancellation. J and V also depend
on the chosen vector/cutoff; this criterion does not establish their
favorable behavior when C is changed.

The diagonal-energy inequality and Cauchy–Schwarz prove all three bounds
in (17). For the stated duplicated weights, sum f_j^(-2) is at most
2 sum_{m>=1}m^(-2)<=4 using the integral upper bound. Thus the stated
2sqrt(E) bound on sum|e_j| is valid. The looser rational/integer certificates
are computable under the chosen epsilon=1 rule.

With fixed positive epsilon, J>=epsilon, V>=1 and W=exp(o(ell)), N/W
grows exponentially in ell. The sufficient sign-independent certificate
therefore has an exponentially large threshold. This limits that guarantee;
it is not a necessary lower bound on C for a vector with small actual w.
Conversely, at E=T² the zero vector always has delta=-log N. Increasing C
cannot give uniformly shrinking error across that entire accepted set.

Integer w is directly computable at the already charged output cost. If
|w|<1, then u=Nv and gcd(u,v)=v=1; N=u is supported on the chosen primes.
Zero has no finite prime valuation vector for an ordinary smooth relation
and needs this separate treatment. The report makes that distinction.

**10. Precision refinement — ACCEPT in its explicitly limited form.**

For C_1=rC_0, coefficient errors give |a_{1,j}-r a_{0,j}|<=epsilon(1+r)
and the analogous target bound. Summing against e proves (18). On the
coarse accepted set, q<=E_0, |z_0|<=sqrt(E_0), and sum|e_j|<=D_0, proving
(19). The same coefficient inequalities with fixed R_{0,j} prove (20).

Use the report's rational alternative with ceil(sqrt(E_0)) to construct an
integer E_1 without any hidden algebraic rounding problem. The explicit
old box and new cutoff retain every old accepted vector, possibly along
with additional ones. Its coordinate costs remain bounded by E_0<=E_1,
so the previous width/time ledgers apply with the substituted parameters.
Dependence on r is in magnitude; the new range and budget can grow linearly
and quadratically in r. No polynomial-in-log(r) rebuild bound follows.

Rescoring M retained coarse vectors costs O(M k b_1²) plus coefficient
construction and preserves their unchanged integers u,v,w. The full M cost
is indispensable. Sampling some coarse vectors, or imposing a tighter fine
cutoff, does not establish retention of any useful vectors. This is the
whole accepted preservation claim; it provides no new relation supply.

**11. Relation processing and factoring scope — ACCEPT with explicit unit and
storage conventions; reject any inference of a factoring speedup.**

For nonzero |w|, repeated trial division over m supplied/generated base
primes has at most m failed divisions and H successful ones. Division cost
O(H²) gives O((m+H)H²), with the stated larger-width substitution when a
base prime exceeds H bits. The conservative gcd cost O(H³) is absorbed.
Generating the first m primes is a separate charged setup operation.

The unit condition means gcd(u,N)=gcd(w,N)=1, since w is congruent to u.
A nonunit is checked for a proper gcd first; gcd=N is not a successful
factor and does not authorize division modulo N. Such a row must not be
used as a unit relation. A gcd with v can also be checked, but invertibility
of v is not required by the ratio w/u. This makes precise the report's
instruction to handle nonunits first.

Write each unit ratio as (-1)^sigma product p_j^alpha_j. Each alpha_j is
a difference of valuations bounded in magnitude by H. For a binary kernel
vector, the selected sign sum and all selected exponent sums are even.
Let A_j be those exponent sums, and form

    X = product_{A_j>0} p_j^(A_j/2) mod N,
    Y = product_{A_j<0} p_j^(-A_j/2) mod N.

The sign disappears from the squared ratio and X²=Y² mod N follows from
the unit relations. This construction avoids negative modular powers.
It explains why the sign coordinate, exact signed valuations, and unit
checks are all needed. A proper divisor still requires checking gcd(X-Y,N)
or gcd(X+Y,N); a nonzero dependency need not provide one.

Dense binary elimination on an (m+1)-by-r matrix, including dependency
tracking, fits O((m+r)³) bit operations. Contiguous row scans and row XORs
realize this bound without granting arbitrary per-bit memory access for
free. Dense matrix/dependency storage is O((m+r)²) bits. If all original
integer valuation rows are retained for later sums, their additional dense
storage is O(rm log(H+2)) bits; otherwise obtaining them again must be paid.
This is ordinary processing storage, not part of the DP's working memory.

For one supplied dependency, |A_j|<=rH. The stated
O(rm log(rH+2)) exponent-summing cost and
O(m log(rH+2) ell²) modular-powering cost are valid, along with prime-base
reduction and gcd costs. These bounds are per chosen dependency. Trying many
dependencies requires paying for all of them.

r>m+1 guarantees a nonzero kernel vector but says nothing about proper
splitting. Neither pair injectivity nor matrix rank establishes sufficiently
varied square roots. The report correctly declines to import smoothness or
square-root success probabilities from unrelated random distributions.
An inverse-polynomial event probability would give the stated expected
geometric waiting time only as an additional per-input theorem. Obtaining
successive useful rows and a split needs corresponding conditional guarantees
and, for a bounded-time algorithm, explicit time/randomness caps.

**12. Scalar-Lagrange shortcut — ACCEPT the stated obstruction only.**

For one coordinate, integer x minimizes x²-lambda a x exactly when
2x-1<=lambda a<=2x+1, including ties. Thus the supplied vector (0,4)
requires both -1<=69lambda<=1 and 7<=110lambda<=9. These intervals are
disjoint since 110<7*69. Its supplied objective value is
16+(440-434)²=52. Scalar-supported-vector enumeration consequently omits
an accepted vector at E=52. This checks the paper-and-pencil argument, with
no execution or parameter search. It does not establish global optimality
of that vector, failure of every scalar-based optimization method, or literal
rounding equivalence at N=77.

**13. Required action and retained scope.**

The only required proposer correction is item 3's restriction on capped
backward-table optimizer recovery. Keep uncapped prefix predecessors for
arbitrary-cutoff box optimization. No shared source change or new experiment
is necessary to resolve it. The full proposer report was not edited here.

After that correction, the supported result is an exact pseudo-polynomial
optimizer and low-energy generator for the original integer objective,
with paid output delay, exact counting/unranking, and the stated expected
or capped-failure sampling guarantees. The specified bounded-error log
construction gives a uniform polynomial-scale family for every N>1.
These are reviewed mathematical constructions, without an executable,
formal semantics refinement, novelty claim, or useful-relation theorem.

No finite test is needed for this disposition and none is preregistered by
this review. A later implementation should be checked under its own frozen
correctness protocol; a useful-yield sample would be a different task and
would still not supply an all-input asymptotic theorem. The next substantive
research requirement remains a costed per-input mechanism producing useful
relations/dependencies, with the precision, density, and proper-splitting
obligations kept explicit. Verified full factoring complexity improvement
remains **NONE**.
