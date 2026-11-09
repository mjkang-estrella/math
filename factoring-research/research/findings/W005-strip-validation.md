# W005 C — exact strip validation and a node obstruction

2026-10-08. Independent symbolic review of **C only**. New deductions below
remain subject to parent review. Verified end-to-end factoring improvement:
**NONE**. No candidate, mathematical program, numerical search, benchmark,
Lean invocation, or experiment was executed.

**Disposition:** C is an exact, terminating splitter, but its literal
empty-wedge/left-first search cannot improve the deterministic one-fifth
baseline. A conservative upper bound is O(sqrt(N) log^3 N) bit operations;
an unconditional family requires Omega(N^(1/4)) visited nodes, even if every
floor sum were free. This is a bound for this pruning rule, not for geometric
factoring or exact hyperbola counting. One conditional state-reuse identity is
given below, followed by a different, explicitly costed line-intersection
primitive that escapes the identified local failure.

## 1. Exact enclosure and count

Let N >= 4, M = floor(sqrt(N)), and 2 <= a <= b <= M. Write h = b-a and
k = h+1. For a < b the specified lower tangent and upper secant are

    L(x) = (N-1)(2a-x)/a^2,
    U(x) = N(a+b-x)/(ab).

Thus their slope/intercept pairs are
(-(N-1)/a^2, 2(N-1)/a) and (-N/(ab), N(a+b)/(ab)).
No coefficient reduction or floating approximation is required. Directly,

    (N-1)/x - L(x) = (N-1)(x-a)^2/(a^2 x) >= 0,
    U(x) - N/x     = N(x-a)(b-x)/(abx) >= 0.

For integer x > 0 and integer y,

    (N-1)/x < y <= N/x  iff  N-1 < xy <= N  iff  xy = N.

Every divisor-strip point therefore lies in L(x) < y <= U(x). The exact
wedge count, including both integer x endpoints, is

    C_N(a,b) = sum_{x=a}^b (floor(U(x)) - floor(L(x))).             (1)

The lower boundary is **strict**, so floor(L), not ceil(L), is subtracted.
An integral upper boundary is included. Each summand is nonnegative. Wide
intervals can have L(x) <= 0; (1) then also counts nonpositive y. That only
adds false positives and does not invalidate pruning. This review analyzes
the stated count without an unmentioned positivity clip.

Define the signed, exact floor sum

    F(k,m,A,B) = sum_{i=0}^{k-1} floor((Ai+B)/m),  m > 0, k >= 0.

Putting x = a+i gives the actual computation

    C_N(a,b) = F(k,ab,-N,Nb)
               - F(k,a^2,-(N-1),(N-1)a).                       (2)

At a=b use the constants U=N/a, L=(N-1)/a, rather than taking a secant
through coincident points. Then

    C_N(a,a) = floor(N/a)-floor((N-1)/a) = 1_{a divides N}.

The rational expressions in (2) also specialize to this value, but the
singleton definition removes any division-by-zero ambiguity in construction.
A divisor at a or b, including a=b=M for a square input, is retained.

Empty intervals have count zero and need no floor sums. N=2,3 have an empty
search range and no factor; N<2 is outside the input contract. Composite
N>=4 has a divisor in [2,M]. A positive nonsingleton count is only a reason
to refine, never evidence of an actual divisor.

## 2. A finite Euclidean computation, with signed arithmetic

Here is sufficient pseudocode for (2), not an assumed counting oracle.
All `divmod` operations use the mathematical floor quotient and a nonnegative
remainder, even when A or B is negative.

    F(k,m,A,B):
        if k == 0: return 0
        s = 0
        repeat:
            (q,A) = divmod(A,m)
            s += q*k*(k-1)/2
            (q,B) = divmod(B,m)
            s += q*k
            Y = A*k+B
            if Y < m: return s
            (k,B) = divmod(Y,m)
            (m,A) = (A,m)       # simultaneous assignment

The normalization removes integer parts of slope and intercept. For the
remaining 0<=A,B<m, if Y>=m then A>0. Put t=floor(Y/m), r=Y-mt.
Count the points by horizontal levels j=1,...,t: their counts are

    k-ceil((mj-B)/A).

The last count may be zero, which is harmless. Reversing j yields

    F(k,m,A,B) = F(t,A,m,r).

This proves the update, including exact divisibility boundaries. The
successive denominators follow Euclid's algorithm, so there are O(log m)
iterations; m=1 and A=0 terminate without swapping into a zero denominator.
This is the usual Euclidean floor-sum computation, also exhibited by
[AtCoder's primary implementation](https://github.com/atcoder/ac-library/blob/master/atcoder/internal_math.hpp)
(`floor_sum_unsigned`). Its machine-word/modulo-2^64 interface is **not** the
interface required here: use signed normalization and unbounded exact integers.

The tree starts at [2,M]. A zero count returns EMPTY. A positive singleton
is checked by N mod a and returns a. Otherwise set c=floor((a+b)/2), search
[a,c], then, if necessary, [c+1,b]. These disjoint intervals partition the
parent integer range. Any actual divisor remains in a positive-count child.
Interval length strictly decreases, proving termination; every composite
eventually returns a proper divisor. Exhaustion certifies absence of divisors
in [2,M]. No probabilistic success assumption is present.

## 3. Conservative unconditional bit cost

Write ell=bit_length(N). There are D=M-1 candidate integers and at most 2D-1
visited nodes (when D>=1). Depth is O(ell). Each nonsingleton needs two floor
sums and O(1) coefficient operations. The unreduced denominators are <=N;
initial numerators have magnitude O(N^(3/2)). Even at a very wide node,
signed sums and normalization terms are bounded by N^O(1), so all intermediate
integers have O(ell) bits. In particular, a negative tangent does not create
an unpriced large-integer operation.

With schoolbook multiplication and division, O(ell) Euclidean iterations
cost O(ell^3) bit operations per floor sum. An elementary binary-search
integer square root also costs O(ell^3). Singleton remainders cost
O(ell^2). Thus, for V actual visited nodes,

    T_C(N) = O((V+1) ell^3) = O(sqrt(N) ell^3).                 (3)

A depth-first implementation retains O(ell) interval records of O(ell)
bits, plus O(ell)-bit arithmetic workspace: O(ell^2) working bits suffice.
There is no need to materialize a tree or a divisor list. These are generous
schoolbook bit-machine bounds, not unit-cost big-integer bounds or claims
about Python timing.

**Saved computation:** a zero node replaces all individual remainder tests in
that interval by two logarithmic-length Euclidean counts. **Paid work:**
integer square root, every visited node, coefficient construction, both sums,
all false-positive descendants, and the final verification. No distributional
estimate for V has been proved. Even relative to trial division, no finite
wall-clock advantage is claimed here.

## 4. A deterministic obstruction stronger than the heuristic

The affine wedge width W=U-L has endpoints

    W(a) = 1/a,
    W(b) = 1/b + (N-1)h^2/(a^2 b).                            (4)

Any half-open real interval (L,U] of length at least 1 contains an integer.
Consequently **C_N(a,b)=0 implies W(b)<1**, whatever the fractional parts
of the boundaries. For h>0 this gives

    h^2 < a^2(b-1)/(N-1) <= M^2(M-1)/(N-1).

Set H_N = M*sqrt((M-1)/(N-1)). This real expression is used only in the
proof, not by the solver. Every discarded interval contains fewer than
H_N+1 = O(N^(1/4)) integers. This also bounds a discarded singleton.

If p is the smallest prime divisor, the literal left-first program must
finish certifying **all p-2 integers in [2,p-1]** before returning p. Its
completed empty terminal intervals partition this prefix. Therefore their
number, and hence V, is at least

    (p-2)/(H_N+1).                                            (5)

For N=pq with distinct primes p<q<2p, p>sqrt(N/2), so (5) is
Omega(N^(1/4)). There are arbitrarily large such inputs by Bertrand's
postulate, applied to each prime p. These are not perfect powers, and a
fixed small-prime screen does not dispose of this family. Prime squares
give an additional obstruction to the completely literal program, but are
unnecessary for the distinct-semiprime conclusion. Prime controls similarly
force a full-prefix search unless an independent primality test is added.

This disproves a uniform O(N^(1/5) polylog(N)) time bound for **this explicit
node-by-node empty-wedge program**. Constant-time floor_sum, Euclidean-state
caching, or faster integer multiplication cannot remove the node bound.
Finding factors at internal nodes, accepting stronger nonempty-wedge
certificates, or executing a whole family of nodes implicitly would change
the analyzed program and require new accounting.

The obstruction is independent of H012's per-residue certificate count,
H030's explicit polynomial/root blocks, and W002 A's dense hull polynomial.
None of those representation lower bounds is imported into this proof.

## 5. Area audit, including an actual resonant strip family

Because W is affine, its real area for h>0 is exactly

    area = h/2 * (1/a + 1/b + (N-1)h^2/(a^2 b)).               (6)

For h<=a this is O(h/a + N h^3/a^3), validating the stated **area** estimate.
The sum of column widths is

    S = (h+1)/2 * (W(a)+W(b)) = ((h+1)/h)*area.

But the actual count is

    C = S + sum_{x=a}^b ({L(x)}-{U(x)}),   |C-S| < h+1.        (7)

Thus an O(1) area does not bound C by O(1), and cannot certify emptiness.
The heuristic scale h~a/N^(1/3) predicts about N^(1/3) log N blocks across
the range after a small-x cutoff; it supplies neither a deterministic upper
bound nor a deterministic lower bound for this search.

More sharply, take any integer H>=2, k=H^4, N=k^2+1, and the valid interval
[a,b]=[k-H,k]. Here M=k. With h=H, (6) gives area=O(1/H), tending to zero.
For each integer 0<=t<=floor(H/2), set x=k-t, y=k+t. These are wedge points:

    xy = k^2-t^2 < N,
    y-L(x) = H*(kH-t*(2k-H))/(k-H)^2 > 0,
    y <= N/x <= U(x).

Hence C >= floor(H/2)+1 despite area tending to zero. All these points
are spurious (N-xy=t^2+1). This is an exact symbolic family, not a numerical
experiment or a claim about the full solver's path on these inputs.

## 6. One reuse rule: translate a fixed rational-line window

For fixed k>=1,m,A, retain (B,S) with S=F(k,m,A,B). The neighboring state has

    B' = B+A,
    S' = S - floor(B/m) + floor((Ak+B)/m).                     (8)

Cancellation of the overlapping k-1 summands proves (8), for negative A
and all boundary equalities as well. Maintain Ak+B or compute it once.
Within the original O(sqrt(N)) x-range, after one O(ell^3) initialization,
K unit window shifts cost
O(K ell^2) bit operations and O(ell) state, using two exact endpoint
divisions per shift. This is actual reuse of the sum, without replaying the
Euclidean descent. It applies to adjacent windows **of the same rational
line**; inherited parent envelopes can use it within their parent domain.

It does not automatically update the specified neighboring *wedges*.
For [a,b] -> [a+1,b+1], the upper denominator changes from ab to
(a+1)(b+1), and the lower denominator changes from a^2 to (a+1)^2.
Their normalized slopes/Euclidean chains need not be identical. Bisection
also changes lengths and, except for the left child's lower tangent, the
lines. Keeping inherited lines remains sound but does not tighten them;
crossing a large offset by unit shifts costs that many updates. Testing
identity of line coefficients is cheap; silently assuming it is not valid.

**Conclusion for this one rule:** it saves a logarithmic factor for genuine
fixed-line sliding queries, but provides no general same-cost update for C's
new tangents/secants. Even a hypothetical stronger per-node update would
still face (5). No further reuse scheme or empirical claim is proposed.

## 7. A materially different paid computation that avoids the failure

Instead of requiring an empty wedge, group its possible divisor points by
the integer level c=u*x+v*y, for explicitly chosen positive coprime integers
u,v. This is a rational line of slope -u/v. Define exact rational endpoints

    alpha = min(u*a+v*L(a), u*b+v*L(b)),
    beta  = max(u*a+v*U(a), u*b+v*U(b)).

Every divisor in the interval has an integer level in

    floor(alpha)+1 <= c <= floor(beta).

Strictness at the lower boundary justifies the +1, including integral alpha.
Let K=max(0,floor(beta)-floor(alpha)). Enumerate these K levels. At each,
the exact equation xy=N becomes

    u*x^2-c*x+v*N = 0,
    Delta_c = c^2-4uvN.

If Delta_c<0 or is not an integer square, there is no solution. Otherwise
test x=(c+sqrt(Delta_c))/(2u) and x=(c-sqrt(Delta_c))/(2u) for integrality,
[a,b] membership, and N mod x=0. These tests cover all actual divisors;
failed extraneous candidates cause no error. Include both signs and handle
Delta_c=0 once. This is a finite exact *interval decision/recovery* primitive,
not a polynomial-strip oracle and not a full proposed factoring program.

If u,v have O(ell) bits, construction plus enumeration costs
O((K+1)ell^3) using schoolbook arithmetic and binary-search square roots,
plus the charged cost of choosing u,v. Exact continued fractions can select
a rational approximation in O(ell^3) for O(ell)-bit data, but no favorable
bound on the resulting total K is asserted. Enumerating all K is paid even
when the interval has no divisor.

For the family in section 5 choose u=v=1 (no search). Its level range
contains exactly c=2k: the lower minimum is

    2k-kH^2/(k-H)^2 > 2k-1,

and the upper maximum is

    2k+(H^2+1)/(k-H) < 2k+1.

Both strict inequalities hold for H>=2, and the wedge includes level 2k.
Here Delta_(2k)=-4. One exact line test rejects the entire interval in
O(ell^3) bit time while C counts Omega(H) points. This removes that specific
false-point resonance rather than merely computing its count faster.

The weighted-sum discriminant test is already prior-art territory:
Harvey–Hittmeir's introduction describes recovery from a weighted sum of
the factors and credits Lehman's rational-approximation approach. It is
used here as a concrete escape from the failed pruning assumption, with
no novelty claim for the line test.

The constructive question left open is precise: **can one uniformly choose
and schedule rational slopes/intervals so that the sum of these explicitly
tested levels, plus every selection, coverage and recovery cost, beats
N^(1/5) polylog(N) on every composite?** Rational tangents and quadratic
intersection tests alone do not establish this. No such schedule is supplied
here. This is the different computation needed to reopen the failed
empty-wedge representation, not a claim to have solved its remaining cost.

## 8. Primary prior art and exact read scope

- [Sladkey, arXiv:1206.3369v1](https://arxiv.org/html/1206.3369v1),
  *A Successive Approximation Algorithm for Computing the Divisor Summatory
  Function*. Read abstract, sections 1–2, section 3 through equations
  (22)–(26), and section 7 through the Stern–Brocot denominator discussion
  (HTML lines 503–552); section 6 Algorithms 2–3 appeared in the returned
  excerpt. It supplies prior art for Farey-neighbor rational tangents,
  determinant-one lattice transformations and recursive exact hyperbola
  counting. Theorem 1 states O(N^(1/3)) time and O(log N) space; its region
  count treats local arithmetic as constant cost. This is not imported as
  an O(N^(1/3)) **bit** bound, and the full algorithm/proof was not audited.
- [D. H. J. Polymath, arXiv:1009.3956v4](https://arxiv.org/html/1009.3956v4),
  *Deterministic methods to find primes*. Read abstract, introduction's
  prime-interval discussion, section 2 Theorem 2.1/Proposition 2.2 and proof,
  and section 2.1 (HTML lines 131–212). Continued fractions approximate
  hyperbola slopes; rational-function crossings partition progressions.
  Section 2.1 sketches O(N^(1/3+o(1))) divisor-summatory computation via
  rational linear sums and exceptional corrections. These are prior exact
  counting mechanisms, not a novelty claim for C. Their global summatory
  result does not by itself supply a faster strip splitter. The exact
  identity D(N)-D(N-1)=tau(N) gives a divisor **number**, not the location
  of a divisor; restricted counts and recovery must also be charged.
- [Harvey–Hittmeir, arXiv:2105.11105v1](https://arxiv.org/html/2105.11105v1),
  *A log-log speedup for exponent one-fifth deterministic integer
  factorisation*. Read abstract and introduction through the description
  following Theorem 1.1 (HTML lines 29–59). The theorem gives complete
  deterministic factorization in O(N^(1/5) log^(16/5)N /
  (log log N)^(3/5)) bit operations on a fixed multitape Turing machine.
  This established comparator suffices to reject C's proposed asymptotic
  gain; no claim that this search exhausts all literature current in 2026
  is needed or made. Its subsequent algorithm/proof was not re-reviewed.
- AtCoder source above: read `floor_sum_unsigned`, including its parameter
  and modulo-result comments (returned HTML lines 917–968), on 2026-10-08.
  No library was installed or executed. The signed identities and bit costs
  in this report are proved here rather than inferred from that interface.

Repository reads: all of AGENTS.md (26 lines), RESEARCH_LOOP.md (77),
RESEARCH_TEAM.md (initial 63 lines, then its complete appended parent-mode
update reread at final verification), README.md (73), docs/SPECIFICATION.md (122),
H012-disposition.md (41), H030-disposition.md (67), and
W002-residual-disposition.md (82); research/STATE.md lines 1–180 only;
research/hypotheses/W005.md section C through end, plus a heading/keyword
index. The full parent brief was supplied in the task. Directory listings
were used for discovery only; other reports and live A/B work were not read
substantively. Input identities are in the adjacent
[minimal digest record](W005-strip-validation-inputs.sha256). Versioned arXiv
identifiers and precise passages above identify the primary literature. The
substantive [parent C excerpt](W005-strip-validation-parent-C.txt) is preserved;
digest entries are read-time identities, with both observed team-file versions
recorded rather than attributing a concurrent parent edit to this child.

This cheap analysis decides the literal C asymptotic-speedup question, so
no numerical screen is needed to reach the disposition and none is proposed
or run. The general line-selection question is a separate future proof or
preregistered primitive task. Shared STATE, registries, harness, Lean,
original reports and parent development are unchanged by this child.
