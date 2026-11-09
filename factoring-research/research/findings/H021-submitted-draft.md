# H021 — An exact generator for the original structured logarithm lattice

2026-10-08. Analytic proposal; independent review **pending**.
Disposition: **promising as a costed generation primitive; useful relation supply unresolved**.
Verified full factoring complexity improvement: **NONE**.

This note derives the proposed single-sum dynamic program. It gives exact
minimization, complete low-energy enumeration with bounded delay, and exact
counting/unranking. Exact uniform sampling has an expected random-bit bound,
not an unconditional bounded-time guarantee. These constructions are
pseudo-polynomial; they become polynomial in the input bit length only under
explicit numerical magnitude bounds. No executable, finite experiment, package,
LLL implementation, or Lean change was made. This work is independent of the
H019 certificate and H020 resultant-population branches.

## 1. Domain and primary-source check

[Tesoro et al., January 2026 revision, Methods equations 20–21 and 25–31](https://arxiv.org/html/2410.16355v3)
specifies a lattice with a positive diagonal and a rounded logarithm row,
targeting a rounded logarithm of N. Its scale is C = 10^c; diagonal weights
are a permutation of 1,1,2,2,... . The reduced-basis binary correction search
in equations 25–28 is a different domain. Equation 29's resource estimate
omits the optimization sweep count based on observed convergence. Equations
30–31 introduce transverse fields, so the actual sampling Hamiltonian is
nondiagonal. Product eigenstates of the unperturbed Hamiltonian do not refute
that sampler. Its numerical resource fits are not used as proofs here.

In our notation the original objective is

    F(e) = q(e) + z(e)^2,
    q(e) = sum_j f_j^2 e_j^2,
    z(e) = sum_j a_j e_j - T,
    e in Z^k, f_j >= 1 integers, a_j,T integers.

The DP below applies to signed or zero a_j and any integer T. It requires no
unproved property of logarithms once these integer inputs have been supplied.
Section 5 constructs them uniformly from N without factoring advice.

For precision about the domain distinction: if B is the original basis and
D = BU its reduced basis, then U is integral unimodular. A reduced correction
e' = c + diag(sigma)x, x in {0,1}^k, becomes

    e = Uc + U diag(sigma)x.

This is generally a coupled affine subset of original exponent space. The
independent original-coordinate box used below contains all vectors below
the chosen energy cutoff; it is not asserted to equal this transformed set.
Filtering our output for membership could have arbitrarily many rejected
outputs before one passes. The enumeration delay theorem does not transfer
to such an extra filter, nor does our uniform distribution reproduce a TN
measurement distribution. Generic CVP hardness does not settle this family.

## 2. Exact minimization with explicit integer costs

Assume k >= 1 and E >= 0 is an integer. Set

    R_j = floor(isqrt(E)/f_j) = floor(sqrt(E)/f_j),
    L_j = 2 R_j + 1,                  L = sum_j L_j,
    S_j = sum_{i<=j} |a_i| R_i,       S = S_k, S_0 = 0,
    Q = 2S + 1.

**Box lemma.** Every e with F(e) <= E satisfies |e_j| <= R_j. This follows
from f_j^2 e_j^2 <= F(e) <= E, since all terms are nonnegative. In the box,
each prefix sum lies in [-S_j,S_j]. This conclusion holds with negative
coefficients; there is no assumption that signed sums grow monotonically.

Define a prefix minimum with infeasibility represented by a separate flag:

    D_0(0) = 0; D_0(s) = infinity for s != 0,
    D_j(s) = min_{-R_j <= x <= R_j}
                 [D_{j-1}(s-a_j x) + f_j^2 x^2].                 (1)

Out-of-range predecessor states are infeasible. Induction on j proves that
D_j(s) is exactly the minimum diagonal cost of a prefix with weighted sum s.
Consequently

    min_{s in [-S,S]} [D_k(s) + (s-T)^2]                         (2)

is the exact minimum over the entire box. Store a minimizing predecessor
at every reachable state, or use the backward table below, to recover an
actual minimizing vector. Uncapped finite diagonal costs are at most kE.
Do not cap D at E when claiming the box minimum for an arbitrary cutoff E:
that minimum might exceed E. Capping is safe for a threshold decision only.

**Global minimum.** The zero vector has F(0) = T^2. Taking E = T^2 therefore
includes every global minimizer and makes (2) a global minimum over Z^k.
Existence follows as well: all vectors that could improve zero lie in this
finite box. For T = 0 the answer is e = 0. For arbitrary E, (2) also decides
whether there is any F(e) <= E, even if its box minimum exceeds E.

Here is a bit-cost ledger, rather than a unit-cost arithmetic claim. Write
bl(t) for the nonnegative integer bit length, with bl(0) = 1, and use

    b = 4 + bl(k+1) + bl(E+1) + bl(|T|+1) + bl(S+1)
          + max_j [bl(|a_j|+1) + bl(f_j+1)].

Every exponent, shift, signed sum, state address, diagonal cost, and squared
terminal residual has O(b) bits. In particular |s-T| <= S+|T|, and it is its
square, not just the energy cap, that must fit during initialization.
The input occupies O(kb) bits. The following bounds use indexed memory with
O(b) charged for accessing/copying a b-bit cell by a b-bit address, O(b)
addition/comparison, and O(b^2) schoolbook multiplication/division. None is
an unbounded-integer unit-cost operation.

* Compute isqrt(E), all R_j, S_j, and widths within O(kb^3) bit operations;
  binary search with exact squares already gives this conservative bound.
* Precompute a_j x and f_j^2 x^2 for all L choices in O(Lb^2) time and
  O(Lb) bits. Computing f_j x before squaring avoids an unnecessary large
  intermediate; the stated input width also pays for large f_j with R_j=0.
* Initialize and scan the terminal residuals in O(Qb^2) time.
* There are at most QL transitions in (1), costing O(QLb) bit operations.

Thus one valid overall bound, including initialization, is

    T_DP = O(kb^3 + (L+Q)b^2 + QLb).                            (3)

The minimum value alone uses O((Q+L+k)b) working bits with rolling rows.
Saving a minimizing predecessor per reachable state uses O((kQ+L+k)b)
bits and permits recovery in O(kb) additional bit work in this memory
model. Saving only the values and scanning predecessor choices instead
costs O(Lb) for recovery. The prime and logarithm setup in section 5 is
additional.

These are explicit indexed-memory bounds, not a claimed formal machine
refinement. A conservative ordinary multitape realization can implement
each logical table access by scanning its retained table. Multiplying (3)
by O(1+kQ+L) bounds that extra access cost, including the choice lists.
This is intentionally loose but still polynomial under the numerical
bounds below. Faster sequential
shift-and-merge row implementations are possible but unnecessary here.

## 3. Complete enumeration without exponentially many failed prefixes

A prefix minimum table alone loses nonminimal prefixes having the same sum.
Enumerating only minimizing predecessors would therefore miss accepted
vectors. Instead compute the following backward completion minima. State
j means that coordinates 1,...,j-1 have been fixed, with weighted sum s:

    V_{k+1}(s) = min(E+1, (s-T)^2),
    V_j(s) = min(E+1,
                 min_{x in [-R_j,R_j]}
                    [f_j^2 x^2 + V_{j+1}(s+a_j x)]).           (4)

For V_j use all s in [-S_{j-1},S_{j-1}]. The transition is always within
the next row's interval. Some states may be unreachable as prefixes, which
does not affect this recurrence or its use on actual prefixes. Induction
proves that V_j(s) is the minimum future diagonal cost plus final residual
square, capped at E+1. Nonnegative costs make capping sound.

Start with prefix (s,q)=(0,0). At level j try x=-R_j,...,R_j, and descend
exactly when

    q + f_j^2 x^2 + V_{j+1}(s+a_j x) <= E.                    (5)

At a leaf output the exponent vector. Every accepted vector follows a path
passing (5), and every visited child has at least one accepted descendant.
Thus the traversal is complete, produces no duplicates, and explores no
subtree without output. This is the missing nondead-prefix guarantee.

The backward table has the preprocessing bound (3), with O((kQ+L+k)b)
retained bits. After preprocessing, time before the first output, between
consecutive outputs, and after the last output is O(Lb), including exponent
output, in the indexed-memory model. To see the delay bound, between two
outputs the traversal backs up along at most one path and descends along
one path. At each level it tries at most a constant times L_j children;
an entered child cannot be fully searched without an output. Outputting
the k signed exponents itself costs O(kb) <= O(Lb).

If M is the number of accepted vectors, total time is

    T_DP + O((M+1)Lb),                                       (6)

before constructing their u,v values. Working memory beyond the table is
O(kb); retained output is additional. A full-scan multitape implementation
has delay O((1+kQ+L)Lb). The number M can be exponential. Polynomial delay
is not a polynomial bound for printing the whole set. This enumeration is
lexicographic in e, not in F; no first-K-by-energy claim is needed here.

E=0, a_j=0, negative a_j, and empty accepted sets need no exceptions beyond
the definitions. If V_1(0)>E, report an empty set immediately.

## 4. Exact counting, unranking, and uniform sampling

Let

    P_box = product_j L_j,
    beta = 1 + sum_j ceil(log2 L_j).

Every count below is at most P_box and has at most beta bits, including
when it is exponentially large. Counts are not fixed-width unit-cost values.

For the same prefix-sum domains as in (4) and remaining budget h=0,...,E,
define

    A_{k+1}(s,h) = 1 if (s-T)^2 <= h, else 0,
    A_j(s,h) = sum_{x in [-R_j,R_j], f_j^2 x^2 <= h}
                    A_{j+1}(s+a_j x, h-f_j^2 x^2).             (7)

Induction counts each suffix exactly once. M=A_1(0,E) is the exact number
of vectors F(e)<=E. With T_init=O(kb^3+(L+Q)b^2), a conservative bound is

    T_count = O(T_init + Q(E+1)L(b+beta)),
    memory = O(kQ(E+1)(b+beta) + (L+k)b) bits.                 (8)

Implicit array coordinates can save the b term in cell storage. Two rolling
rows suffice to obtain just M; retain all rows for unranking and sampling.
Full-scan tape access multiplies the displayed time bound by at most
O(1+kQ(E+1)+L). The added numerical E factor is explicit.

Given an integer r in [0,M-1], unrank lexicographically: at each level scan
the allowed x, subtracting their completion counts until r lies in one
child's block; enter that child and update s,h. Zero-size blocks are skipped.
There is a unique output for every r, with deterministic additional cost
O(L(b+beta)) and O(kb+beta) working bits. This proves the bijection needed
for sampling without enumerating rejected prefixes or other outputs.

For M>1 draw d=ceil(log2 M) unbiased bits, reject the resulting integer if
it is >=M, and unrank the accepted rank. Each attempt succeeds with
probability >1/2, except the power-of-two case which succeeds surely.
Expected random bits are at most 2d and expected rank-generation bit work
is O(beta). For M=1 use rank zero; for M=0 report emptiness. The returned
vector is exactly uniform. Rejection means the worst-case running time and
number of random bits are unbounded. A cap of t attempts gives failure
probability at most 2^(-t), with exact uniformity conditional on success;
failure must remain an explicit outcome. This distinction matters to the
repository's worst-case randomized factoring contract.

Uniformity is over exponent vectors for this one fixed integer objective.
It is not uniformity over smooth residues, relation parity columns, or
successful factor splits. Low-energy counting does not count useful rows.

## 5. A uniform N-only input construction and all output widths

Let ell=bit_length(N), N>1. The choices k>=1, integer c>=0, weights f_j,
and E must be public, finitely computable rules, with their costs charged.
Set C=10^c. Computing C by repeated multiplication by 10 takes at most
O((c+1)^2) elementary bit work and O(c+1) bits. There is no need for N's
factors, an oracle, an LLL basis, or a precomputed size-dependent table.
Reading N and determining ell costs O(ell); for the concrete rule below,
generating its k weights costs O(k log(k+2)) additional bit work.

**Primes and primorial.** One elementary implementation enumerates all
integers through U=4(k+1)^2, certifying each candidate prime by trial
division by integers from 2 through one less than the candidate, and keeps
the first k primes. This is deliberately slow but fully charged:
O(U^2 log^2(U+2)) bit work and O(k log(U+2)) storage. There are enough
primes: the corollary to Theorem 3 in
[Rosser–Schoenfeld, *Approximate formulas for some functions of prime numbers*, 1962, p. 69](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)
gives p_k < k(log k+log log k) for k>=6; the first five primes cover the
remaining cases. This also gives p_k=O(k log(k+2)). No floating-point
evaluation of this theorem is needed for the integer cutoff U.

The primorial P_k=product_{j<=k}p_j is optional, not an input or advice.
If materialized, its bit length is at most

    H_p = 1 + sum_j bl(p_j) = O(k log(k+2)),

and sequential schoolbook multiplication costs O(k H_p^2) bit operations
and O(H_p) additional working bits. A gcd with N costs conservatively
O((ell+H_p)^3) bit work. A proper gcd is a verified factor; gcd=1 or N is
not a proper split. The generator does not assume such a gcd succeeds.

**Exact rational logarithm bounds.** Literal nearest(C log x) requires
resolving which side of a half-integer the true value lies on. This note
does not assert a polynomial precision cap for that separation problem.
Instead it specifies a changed rounding rule with a certified error.

For integer x>=1, let m=bl(x)-1, y=x/2^m in [1,2), and t=(y-1)/(y+1).
Both y and t are exact rationals and 0<=t<1/3. Set

    L_n(t) = 2 sum_{r=0}^{n-1} t^(2r+1)/(2r+1).

Integrating the geometric series gives

    0 <= log((1+t)/(1-t)) - L_n(t)
       <= 2 t^(2n+1)/[(2n+1)(1-t^2)] <= 3^(-2n)              (9)

for 0<=t<=1/3. Therefore the rational

    q_x = m L_n(1/3) + L_n(t)

satisfies 0<=log x-q_x <= (m+1)3^(-2n). Choose n>=1 by multiplying 9
until 9^n >= 4C(m+1). This supplies an exact rational interval of width
at most 1/(4C), with

    n = O(1 + log(C+1) + log(bl(x)+1)).

Use the deterministic rule

    round_star_C(x) = floor(C q_x + 1/2).                    (10)

The rational rounding in (10) is exact, including its rational ties, and

    |round_star_C(x) - C log x| <= 3/4 <= 1.                 (11)

Take a_j=round_star_C(p_j), T=round_star_C(N), and throughout use epsilon=1
unless a sharper certified error is explicitly carried. This is a bounded
error change of generator, not a claim of equality to literal nearest-log
rounding or to another generator's candidate distribution.

For a concrete bit bound, let b_x=bl(x). Compute the n rational terms
sequentially with integer numerator/denominator arithmetic, without any
floating values. Even multiplying denominators rather than exploiting
common factors keeps all intermediate widths within

    d_x = O(n^2(b_x+log(n+2)) + log(C+1) + log(b_x+2)).

Indeed term r has numerator/denominator width O((r+1)b_x+log(r+2)); their
sum of widths bounds the denominator of their unreduced sum. Numerators
add only the size of the sum. The two series and multiplication by m obey
the same bound. O(n) schoolbook rational operations, the final integer
division, and computing the remainder interval cost O(n d_x^2) bit work
and O(d_x) scratch bits. Multiply by k+1 using the largest b_x for a
conservative total; storing all rational certificates separately is extra.
This elementary construction is intentionally less efficient than fast
logarithm algorithms, but proves a polynomial bit bound without a
near-tie assumption. Equation (9) is its exact certificate.

**Magnitude scope.** With these coefficients,

    |a_j| <= C log p_k+1 = O(C log(k+2)+1),
    |T| <= C log N+1 = O(C ell+1),
    R_j <= sqrt(E),
    S <= k (max_j |a_j|) sqrt(E),
    L <= k(2sqrt(E)+1),
    beta = O(k log(E+2)).                                   (12)

Thus k,C,E of polynomial numerical magnitude in ell, and polynomial input
bit widths for the chosen weights, make (3), (6)'s delay, and (8) polynomial
in ell. Setting E=T^2 preserves this scope if C and k have those bounds.
A large f_j only shrinks R_j, but its input bits still have to be read.

For C=10^c, the sufficient scale restriction is c=O(log ell). The condition
log C=poly(ell) alone allows C exponential in ell and supplies no polynomial
bound on S or the DP. Fine logarithms can be cheap in their *precision bit
count* while this DP is expensive in their *coefficient magnitude*.

For example, k=ell, C the smallest power of ten at least ell, and
f_j=ceil(j/2) are completely specified N-only rules. They have C<10ell,
T=O(ell^2), E=T^2=O(ell^4), S=O(ell^4 log(ell+2)), and
L=O(ell^3). These loose bounds already prove a polynomial exact optimizer,
enumeration delay, and count/unranking algorithm for every N>1. They say
nothing about this example rule's relation yield. Other public rules may
be substituted only with their parameter-generation costs included.

**Constructing u,v and the signed residual.** For an output e define

    u = product_j p_j^max(e_j,0),
    v = product_j p_j^max(-e_j,0),
    w = u-Nv,
    H = 2 + ell + sum_j R_j bl(p_j),
    B_e = sum_j [1+bl(R_j+1)].

Then u,v,Nv,|w| each have at most H bits, up to the separate sign bit.
In particular these integers are not charged unit cost. Binary powering
and multiplication construct u,v,w in O((B_e+1)H^2) schoolbook bit work,
with O(H+kb) scratch, in addition to the enumeration delay or unranking
cost. Signed exponent output itself costs O(B_e) bits. Writing retained
u,v,w values costs O(H) bits per vector; retaining M of them costs O(MH).
No pseudo-inverse or recovery of exponents from an LLL vector is required.

Unique factorization gives gcd(u,v)=1 and distinct exponent vectors give
distinct ordered pairs (u,v). This does not make their parity rows distinct.

## 6. Precision-to-cancellation implications, with the right quantifiers

Suppose more generally |a_j-C log p_j|<=epsilon and
|T-C log N|<=epsilon. Write

    h(e) = epsilon (1+sum_j |e_j|),
    delta(e) = log(u/(Nv)),
    z(e) = sum_j a_j e_j - T.

Expanding the errors, including the target error with its sign, proves

    |C delta(e)-z(e)| <= h(e),
    (z-h)/C <= delta(e) <= (z+h)/C,
    |delta(e)| <= eta(e) := (|z|+h)/C.                       (13)

These are deterministic statements about every vector, with no random-log
or independent-error assumption. They imply the exact interval

    Nv [exp((z-h)/C)-1] <= w <= Nv [exp((z+h)/C)-1]           (14)

and, more simply,

    exp(-eta) Nv <= u <= exp(eta) Nv,
    |w| <= Nv (exp(eta)-1),
    |w|/max(u,Nv) <= 1-exp(-eta).                            (15)

For a desired absolute residual bound W>0, a sufficient sign-independent
certificate from (15) is

    (|z|+h)/C <= log(1+W/(Nv)).                              (16)

If V is a proved bound v<=V and |z|+h<=J, the uniform sufficient condition
is C >= J/log(1+W/(NV)). A rational, more conservative version avoids
evaluating that logarithm: require J/C<=1 and 2NVJ<=CW, since
exp(t)-1<=2t for 0<=t<=1. If W/(NV)<=1, the threshold in the logarithmic
certificate lies between J NV/W and 2J NV/W because
x/2<=log(1+x)<=x for 0<=x<=1. This describes the cost of this certificate,
not a necessary lower bound on the precision of a successful vector.

Energy supplies the following certified bounds:

    |z| <= sqrt(E-q(e)) <= sqrt(E),
    sum |e_j| <= min(sum R_j, sqrt(E sum_j f_j^(-2))),
    log v <= min(sum R_j log p_j,
                 sqrt(E sum_j (log p_j/f_j)^2)).             (17)

Both second bounds follow by Cauchy–Schwarz; discarding the nonnegative
coordinates for log v can only improve them. For the weights 1,1,2,2,...,
sum f_j^(-2)<=4, by comparison with the integral for sum_{m>=1}1/m^2.
Hence sum |e_j|<=2sqrt(E) for those weights, independent of k.
Integer-only looser choices J=ceil(sqrt(E))+epsilon(1+sum R_j) and
V=2^(sum R_j bl(p_j)) suffice when a rational certificate is wanted.

Two limitations are decisive:

1. A polynomial absolute rounding scale usually certifies only a modest
   relative error, while Nv is at least N. For W=exp(o(ell)), the above
   sign-independent certificate with fixed positive epsilon and its J>=epsilon
   requires an exponential-size sufficient threshold, since NV/W is
   exponential. This is a limitation of the guarantee in (16), **not** a
   theorem that actual cancellation needs exponentially large C. Actual
   rounding errors can cancel, and unusually good vectors may occur.
2. Raising C and retaining E=T^2 does not even force a shrinking *uniform*
   logarithmic error. The zero vector is always admitted, and its actual
   delta is -log N. Moreover the coarse bound sqrt(E)/C is of order log N.
   A useful guarantee needs a much smaller attained residual/norm window
   and a supply theorem for that window, not just exact global minimization.

The inequalities are analytic implications, not floating-point tests.
For an already constructed vector, computing the integer w directly tests
|w|<=W exactly and is already paid for in section 5. If |w|<1, integrality
forces w=0. In that case gcd(u,v)=1 forces v=1 and N=u, so N is entirely
supported on the chosen primes; zero is not an ordinary smooth relation
to feed into a parity matrix.

## 7. What precision refinement really preserves

There is a simple costed preservation statement, but it does not create
useful relations. Suppose two generated objectives use C_0 and C_1=rC_0,
integer r>=1, the same f_j and primes, and coefficient errors <=epsilon.
Let their residuals be z_0,z_1. Then

    |z_1(e)-r z_0(e)|
        <= epsilon(1+r)(1+sum |e_j|).                        (18)

For every e with F_0(e)<=E_0, put D_0=sum_j R_{0,j}. It follows that

    F_1(e) <= E_0 + [r sqrt(E_0)
                         + epsilon(1+r)(1+D_0)]^2.          (19)

An integer cutoff E_1 may be the ceiling of this bound, or the explicitly
rational bound obtained by replacing sqrt(E_0) with ceil(sqrt(E_0)).
Using the original box [-R_{0,j},R_{0,j}] and cutoff E_1 preserves *all*
the coarse accepted vectors, hence any useful ones among them. In this box

    S_1 <= r S_0 + epsilon(1+r) D_0,   L_1=L_0.              (20)

Run the same DP with this fixed box, replacing E,S,L,b in the costs by
E_1,S_1,L_0,b_1. The box proof is not needed when an explicit box is part
of the requested domain. The counting cost pays the new E_1 coordinate.
For fixed coarse parameters, S_1 can scale linearly with r and E_1
quadratically with r. Rebuilding tables is thus polynomial in the
*magnitude* of r, not established polynomial in log r.

Alternatively, if M coarse vectors have been explicitly retained, rescore
them at fine precision with O(M k b_1^2) integer work plus the new log
construction. Their integer u,v,w never change. This preserves the
population with its full M output cost, which can be exponential.
Unranking a polynomial number of coarse vectors and rescoring is cheap,
but provides no guarantee that the chosen sample contains useful vectors.

Equations (18)–(20) are the entire claimed refinement mechanism. Keeping
E_1 small enough to impose a stronger cancellation requirement can discard
any or all useful coarse vectors; no population-preserving theorem for
that stronger operation is supplied. There is no hidden precision-tuning
promise or claim that refinement solves the supply problem.

## 8. Relation processing is affordable per vector; relation supply is open

Fix a smoothness base of m>=k primes, generated and charged as in section
5 with m in place of k. For nonzero w, test whether |w| is smooth by exact
trial division, retaining every prime valuation and the sign. There are
at most m failed divisions and H successful divisions, since each success
reduces the integer by a factor at least 2. Thus O((m+H)H^2) bit work per
vector is sufficient. Check gcds and accept a factor only if 1<d<N and
d divides N; a conservative O(H^3) gcd cost is covered by this bound.
If the smoothness primes have larger widths, use H+bl(p_m) in place of H
for division widths. Zero residuals require the separate treatment above.

For unit smooth relations, write w/u as a signed product of base primes
and record the exponents modulo 2, including a sign row. With r collected
relations, elementary elimination costs at most O((m+r)^3) bit operations.
A nonzero kernel vector produces a congruence of squares after exponent
sums and modular powering. For a chosen dependency, exponent summation
costs O(rm log(rH+2)); modular powering can be charged
O(m log(rH+2) ell^2), plus O(m(ell+bl(p_m))^2) to reduce the prime bases
modulo N, followed by O(ell^3) for a conservative gcd bound.
Nonunits are handled by gcds first. These are costs of processing supplied
rows, not a bound on the number of candidate vectors needed to obtain them.

None of the exact DPs proves any of the following for each composite N:

* An inverse-polynomial fraction of its accepted vectors has smooth w.
* A polynomial prefix of its lexicographic enumeration has useful rows.
* The smooth outputs avoid duplication and contribute the needed parity
  structure or sufficiently varied dependencies.
* A dependency yields a proper split instead of only X=+Y or X=-Y mod N.

The dimension inequality r>m+1 ensures a nonzero kernel vector; it does
not ensure a proper factor. Full column independence is not even possible
at that count. Distinguish nonduplicate relations, matrix rank, kernel
dimension, and the arithmetic usefulness of the resulting square roots.
No generic random-integer smoothness law or generic random-square-root
success probability has been transferred to this structured distribution.

For example, if a *separate theorem* gave per-input useful probability
rho_N>=1/poly(ell) under the exact uniform sampler, independent sampling
would give an expected 1/rho_N draws for one such event. Successively
obtaining the needed new rows and a split would require corresponding
conditional probability guarantees, and a bounded-time algorithm would
also charge capped sampling failures. This note supplies none of those
probability assumptions. The missing ingredient is useful population and
its accessibility, not the cost of finding one exact minimum.

## 9. Analytic check against scalar-Lagrange enumeration

For f=(1,1), a=(69,110), T=434, the supplied vector e=(0,4) has

    F(e) = 16 + (440-434)^2 = 52.

For it to minimize sum e_j^2-lambda sum a_j e_j coordinatewise, including
all ties, nearest-integer optimality would require simultaneously

    -1 <= 69 lambda <= 1,
     7 <= 110 lambda <= 9.

The intervals are disjoint because 1/69 < 7/110. Thus a scalar-Lagrange
supported-vector enumeration misses this accepted vector at E=52. This
is an exact algebraic check on the supplied integer coefficients, not a
finite experiment or a claim that this vector is the global F minimum.
It suffices to refute completeness of that enumeration shortcut. No
assertion about literal nearest-log rounding at N=77 is needed for this
integer-objective observation.

## 10. Disposition and review handoff

The parent proposal survives as a constructive lemma: exact optimization
and complete low-energy generation are pseudo-polynomial in the stated
single-sum range, with explicit count, precision, and output costs. A
uniform polynomial-scale instance family exists for every binary N.
This is a standard finite-state dynamic-programming construction; no
novelty claim is made, and this was not an exhaustive prior-art survey.
The rational log implementation is deliberately a changed generator.

The precision guarantee does not prove useful cancellation at polynomial
scale, and its failure does not prove that accidental useful cancellation
is impossible. No smoothness, rank, proper-splitting, or factoring speed
claim follows. Best supported full-work claim: equations (3), (6), and
(8), plus the prime/log/output costs, for the explicitly stated domains.

The next action is **independent review by the coordinator's next reviewer**,
especially the capped suffix invariant, worst-case enumeration delay,
count-bit/random-bit accounting, rational-series width bound, and the
quantifiers in the precision discussion. Review must precede acceptance
of these positive claims. No recursive delegation was used here. A later
implementation correctness screen could test these lemmas, but no new
finite test is run or registered by this note. The substantive next
research question is a costed per-input useful-population mechanism for a
specified cutoff/distribution; merely changing precision or minimizing F
again would not resolve it.

Only this assigned finding was created. Shared code, Lean, hypotheses,
registries, STATE, and prior reports/evidence were not edited.
