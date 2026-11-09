# H027 — Adaptive generation, forced divisors, and the price of useful supply

2026-10-08. **Exploratory construction report; no new theorem accepted.**
Verified full classical factoring complexity improvement: **NONE**.
Proposed disposition: **no survivor for implementation in this round**.

Three concrete constructions were considered independently: a flat-weight
smooth-product walk with modular reduction; an exactly solvable power-of-two
congruence that forces a smooth divisor; and CRT-conditioned quadratic values.
The second gives a particularly explicit conditioning primitive, and the third
recovers a real, familiar reduction in cofactor size. Neither supplies a new
complete factoring bound. The conclusions below distinguish exact algebra,
proposed derivations requiring independent review, and unsupported yield laws.

Only this report and adjacent `H027-adaptive-*` source artifacts were written.
No research program, sample, benchmark, parameter sweep, package, Lean change,
shared-file edit, delegation, commit, publication, or scheduler was used. Reading,
primary-source retrieval, text extraction, hashing, and symbolic derivation were
the work of this round. The numerical parameter rules below specify algorithms
on paper; they were not executed on a finite corpus.

## 1. Accepted interfaces and baseline

I read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, the full H027 brief, the H021/H024/H025/H026
dispositions, the current H021 generator and H024 cost/population reports,
H026's proof and its independent review's scope discussion, and W001's baseline
ledger. H026 acceptance in the assignment and disposition supersedes the stale
live-review instruction initially present in STATE. No H026 task was polled.

The accepted H021 objective remains

    F(e) = sum_j f_j^2 e_j^2 + (sum_j a_j e_j - T)^2.

Its `round_star` rational coefficients have a certified bounded error; they are
not an implementation of exact nearest rounding of true logarithms. H024's
nonempty cutoff is E_star < 40 ell^2. Its tilde-O(ell^3) optimizer is in the
specified charged indexed-memory model; its conservative tape realization and
counting/enumeration costs are separate. H026 uses the first ell primes aligned
with f_j=ceil(j/2), exp(O(ell^(2/3))) exponent vectors, and exp(o(ell)) possible
smooth residuals to bound qualifying inputs. The balanced-semiprime denominator
rejects that precise universal supply lemma. It does not establish a conditional
rarity law for every fixed input/history. The review's weight swap is a scope
counterexample, not a generator with useful yield. None of these results covers
the constructions below merely by name or analogy.

Write ell=bit_length(N), and use natural logarithms in

    L_N[alpha,c] = exp((c+o(1)) (log N)^alpha (log log N)^(1-alpha)).

The comparison is complete factoring, including collection, exact valuations,
linear algebra, square reconstruction, productive gcds, and restarts. The
reference heuristic NFS constant is Coppersmith's

    c_C = ((92+26 sqrt(13))/27)^(1/3), approximately 1.902,

as well as the conventional GNFS constant (64/9)^(1/3). Coppersmith's separate
1.639 amortized precomputation estimate is not a cold single-input baseline.
His paper explicitly treats structured-value smoothness as heuristic.
[Coppersmith, sections 2–4](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf).

The W001 rigorous complete-factoring comparison is Lenstra–Pomerance's expected
L_N[1/2,1]; the deterministic comparison is the recorded Harvey–Hittmeir
N^(1/5)-scale bit bound. This report proposes no improvement to either.
For the concrete constructions, Dixon's random squares and the quadratic sieve
are the relevant mechanisms. Dixon proves a subexponential randomized factoring
bound and separately controls productive dependencies through randomness among
square-root fibers; his theorem is not the heuristic sqrt(2) constant derived
below. [Dixon, sections 2–3, especially Lemma 3](https://pages.cs.wisc.edu/~cs812-1/dixon.pdf).

## 2. Common executable and accounting conventions

Handle even inputs and exact perfect powers first, at polynomial bit cost, and
use a primality test when recursive full factorization needs it. All constructions
receive N alone and public size rules. Hidden factors and the family labels used
in analysis are unavailable to them. A gcd is accepted only when 1<d<N; gcd=N
does not certify a split or a unit. Hard-input discussions concern the branch
remaining after the stated small-prime tests.

Let P_B be the primes <=B, k=pi(B), and B>=5. Generate and certify this list,
test its primes against N, and retain their modular inverses when needed.
This costs B*poly(ell+log B) bit work and storage at most that scale. No prime
or inverse table is advice. A sequential alternative to random-access sieving
lists all products ab<=B with a,b>=2, sorts/deduplicates this O(B log B) list,
and merges it against 2,...,B; thus a B*poly(log B) prime-construction bound
does not require free indexed memory.

Unless a literal integer product is explicitly requested, modular products and
powers use O(ell+log B+h) bit operands, where h is the conditioning precision
in section 4. Schoolbook multiplication/reduction at width w costs O(w^2),
extended Euclid can conservatively be charged O(w^3), and binary powering by
an exponent of d bits costs O((d+1)w^2). Exponent *magnitude* still matters if
the integer power is materialized. No numerical logarithms are needed in any
of the three proposed implementations.

For a batch of S integers of H bits, exact division by every prime costs
O(S(k+H)(H+log B)^2). This is an available conservative implementation, not
the favorable complexity model used in section 7. To avoid falsely rejecting
a mechanism solely through that implementation, also allow the accepted H016
integer batch construction: full sparse valuations in (B+S)*poly(ell) bit
work when H, log B, log S and payload widths are polynomial in ell. Retain
the actual aggregate-bit cost otherwise. This is about full exponents, not
just a smoothness yes/no test. Its source distinguishes smooth-part extraction
from complete small-factor recovery.
[Bernstein, introduction and algorithm](https://cr.yp.to/factorization/smoothparts-20040510.pdf);
[accepted H016 interface](H016-disposition.md).

Sort candidate records to detect duplicates, with record bits and comparison
costs charged. Different roots of the same square residue must be compared
by gcd before discarding them: they can be immediately productive. Distinct
integer residuals, distinct exponent vectors, distinct parity columns and
productive dependencies are four different counts.

## 3. Construction A: flatten the weights and generate modular smooth products

### 3.1 An exact N-only selector and its actual distribution

A fully specified polynomial-scale version uses B=ell^2 and t=ell^3. With all
base primes coprime to N, start g=1. Repeat t times independently: stay put
with probability 1/2; otherwise choose j uniformly from 1,...,k and choose
epsilon=+1 or -1 equiprobably, then set

    g <- g p_j^epsilon mod N.

Keep the signed exponent vector e if desired. It satisfies sum |e_j|<=t and
sum e_j^2<=t^2. This is a genuine flat-weight, enlarged-domain selector, not
an optimizer chosen without a distribution. Each attempt starts afresh; a
single continuing walk would require a separate history-dependent analysis.
Exact uniform index sampling uses rejection, with expected constant trials;
a fixed cap must report failures and include them in any success denominator.

One can place its vectors inside an explicit H021-style *changed* objective
with f_j=1 and the same rational coefficient rule, but that does not describe
its law as uniform on an F-sublevel set. For example, if A_max=max |a_j|,

    F(e) <= t^2 + (t A_max + |T|)^2.

Computing such a containing cutoff or an exact minimum adds no supply result.
The proposed arithmetic output instead is

    r = g^2 mod N,  0<=r<N,       g^2 = r mod N.       (A1)

This deliberately abandons the requirement that the integer quotient in a
literal u-Nv identity be smooth. The known square on the left replaces that
requirement. H026 neither supplies nor prohibits its yield.

Let H=<p_j mod N> inside G=(Z/NZ)^*. The law of g is exactly the t-fold
convolution of the displayed lazy-step law on H. For a character chi of H,

    lambda_chi = 1/2 + (1/(2k)) sum_j Re chi(p_j),
    TV(law(g),Uniform(H)) <= (1/2) sqrt(sum_{chi!=1} lambda_chi^(2t)). (A2)

This follows by diagonalizing convolution on a finite abelian group and
Cauchy–Schwarz; it is a proposed elementary derivation for independent checking.
It is an analysis formula, not a computational oracle for H or its characters.
The output law is exactly the pushforward under squaring. There is no supplied
bound on the spectral sum, on H=G, or on useful smoothness under this law.

### 3.2 Cost, and what even perfect mixing would buy

The t choices use O(t log(k+2)) expected random bits. Per attempt modular
arithmetic costs O(t(ell+log B)^2), with an exponent record of at most t
nonzero occurrences before merging. A stored sparse e uses at most
O(min(t,k)(log k+log(t+2))) bits. The literal numerator and denominator would
have O(t log B) bits, but are unnecessary for (A1).

To realize the bound without free random table accesses, generate requests for
an entire batch, sort them by prime index, merge against the prime/inverse list,
then sort by attempt identifier and multiply. Commutativity preserves each
sample exactly. This gives (B+St)*poly(ell+log B+log S+log t) bit work and
storage at most the same scale, plus exact smoothness processing. It does not
hide a k-sized scan on every walk step. Retained relation storage is additional.
With Y distinct accepted records in S attempts, amortized generation cost is
the displayed total divided by Y; there is no finite guarantee if Y=0.

For an explicit supply test, suppose *even more favorably* that g is exactly
uniform on G. For N=pq with distinct odd balanced primes, r is uniform on
QR_N, of size phi(N)/4. Consequently

    Pr(r is B-smooth) <= 4 Psi(N,B)/phi(N).           (A3)

For B=ell^2, an elementary bound already makes this exponentially small.
Use the finite Euler product at sigma=3/4:

    Psi(N,ell^2) <= N^(3/4) product_{p<=ell^2}(1-p^(-3/4))^(-1).

Since -log(1-z)<=z/(1-2^(-3/4)) in this range and
sum_{m<=ell^2} m^(-3/4)=O(sqrt(ell)), the product has logarithm O(sqrt(ell)).
Thus the right side of (A3) is N^(-1/4+o(1)). This is a bound on the *ideal
uniform law for each such N*, not H024's rejected conditional law and not a
bound on the actual walk. If the walk is delta-close to uniform G, only the
bound N^(-1/4+o(1))+delta follows. A polynomially small delta cannot be silently
dropped. Nor does a small subgroup automatically have the same density.

The construction needs an arithmetic bias toward smooth residues, rather than
merely a proof of mixing. Enlarging B to the usual subexponential scale and
granting inexpensive mixing returns the random-square envelope in section 7.
Sampling an unrestricted uniform unit directly is already cheap from N; it
also preserves the square-root fiber randomness used in Dixon's proof. The
smooth-product restriction has supplied neither a better norm nor a better
yield law, and may lose that root randomness.

**Missing lemma A.** For the displayed walk (or an explicitly replaced
N-only walk), bound the number of *new* smooth records and the eventual proper
split probability per paid batch, uniformly on the claimed inputs. A mixing
bound alone is not this lemma. No favorable law for the actual output has been
established. **Disposition: do not implement as a speedup candidate.**

## 4. Construction B: force 2^h into a smooth-product residual

This directly attacks the residual, rather than relying on log proximity.
Use odd base primes, including 3 and 5, and h>=3. A concrete size rule is
h=ell and a t=ell^3-step lazy choice of exponents on the other odd primes.
Remove any base divisor of N first. The following congruence construction
itself needs neither the factorization nor the group order of N.

### 4.1 The congruence is efficiently solvable, with an exact index

Every odd a modulo 2^h has a unique representation

    a = (-1)^s(a) 5^d(a) mod 2^h,
    s(a) in {0,1}, d(a) in Z/DZ, D=2^(h-2).          (B1)

Here s(a) is read modulo 4. The identity

    5^(2^j) = 1+2^(j+2) mod 2^(j+3)

follows inductively by squaring. It proves both the order of 5 and a bit-lifting
discrete-log algorithm: after solving modulo 2^(j+2), choose the next bit of d
to fix the bit at 2^(j+2). Precompute successive squares modulo 2^h and lift
for h-2 steps. O(h^3) schoolbook bit work per logarithm suffices, with O(h^2)
bits if all powers are stored. Preprocessing all base logarithms and d(N)
costs O((k+1)h^3), besides reading/reducing N and the base. This is an explicit
special-group calculation, not a generic discrete-log assumption.

For a signed exponent vector e, forcing

    product p_j^e_j = N mod 2^h

is exactly the pair of linear congruences

    sum s(p_j)e_j = s(N) mod 2,
    sum d(p_j)e_j = d(N) mod D.                       (B2)

After choosing all coordinates except those of 3 and 5, set e_3 in {0,1}
from the first congruence (s(3)=1, s(5)=0), then set e_5 to the centered
representative modulo D given by the second (d(5)=1). This produces an
exponent vector for every free choice. The homomorphism in (B2) is onto, so
its kernel in Z^(k-1) has index, equivalently full-rank lattice determinant,

    2D = 2^(h-1).                                    (B3)

Exactly one pair survives among the 2D residue choices for (e_3 mod 2,e_5 mod D)
for each fixed free choice. That is an exact population loss on complete
periods. It is **not** a uniform density theorem for short boxes or for the
N-dependent log-target window.

### 4.2 Literal output pays for the forced coordinate

Write the signed smooth product as u/v with coprime positive odd u,v. Since v
is invertible modulo 2^h, (B2) gives

    2^h | u-Nv.                                      (B4)

This is a real known smooth divisor. But the solved coordinate can have
|e_5| up to D/2. Materializing its numerator or denominator then takes
Theta(2^h) bits in the allowed worst range. More generally literal output
width is O(ell+t log B+2^h), and must be charged at its actual value. The
O(h)-bit description of e_5 does not reduce the number of digits of 5^|e_5|.
For flat weights its permitted diagonal energy is already O(t^2+4^h).

Adding the group residue as a coordinate to the H021 DP pays the 2D states;
this explicit implementation loses polynomial numerical ranges when h is
Theta(ell). Selecting only small solved coordinates avoids large outputs but
has no established supply. The index (B3) cannot be replaced by a favorable
short-box volume heuristic. These observations reject the stated literal
construction's cheap-large-forced-part argument; they do not lower-bound every
algorithm finding a short representative of (B2).

There is also a precise proposed cost falsifier for the specified h=ell
literal sampler, rather than just a large worst-case coordinate bound. Fix
ell and any realization of its free exponents. Among all ell-bit N, at most

    2(2 floor(L)+1)

can give |e_5|<=L: the two choices of e_3 and these choices of e_5 determine
N modulo 2^ell, hence at most one N apiece in the bit interval. Use H026's
accepted ensemble of Omega(2^ell/ell^2) balanced squarefree semiprimes; its
factors eventually exceed ell^2, so every input reaches the same base and
free-choice rule. With L=2^(ell/2), the fraction of that ensemble having a
small solved coordinate is O(ell^2 2^(-ell/2)), uniformly for each free choice.
The free-choice distribution depends only on ell, not on N within this
ensemble. Averaging over it preserves the bound. Thus the ensemble average
expected literal-output work is Omega(2^(ell/2)). This rules out an all-input
expected-polynomial bound for this particular literal implementation, which
materializes the products on each attempt. It proves neither a per-input
smoothness law nor a bound on a new N-adaptive short-representative selector.
This short counting derivation needs independent review, as do the other
new derivations in this report.

### 4.3 Modular compression works, but retains an N-sized cofactor

There is a precise cheap alternative to materializing u and v. Let

    M = N 2^h,
    g = product p_j^e_j mod M,
    d_0 = (g-N) mod M in [0,M),
    w_0 = d_0/2^h in [0,N).                           (B5)

All inverses exist because the chosen primes are odd and coprime to N.
Equation (B2) ensures exact divisibility of d_0. Reducing (B5) modulo N gives

    product p_j^e_j = 2^h w_0 mod N.                  (B6)

Thus a B-smooth w_0 gives a valid fully factored unit congruence, with the
known valuation h at 2 included. In fact w_0 is a unit modulo N, so zero
does not occur in this branch. All arithmetic has O(ell+h+log B) bit width;
the large solved exponent has only h bits for modular powering. A sparse free
choice of t steps plus the two corrections costs

    poly(ell+h+log B) * (t+h+1)

per attempt, with the preprocessing of section 4.1 charged once. Batch-sorted
prime access as in section 3 and H016 valuation recovery avoid an extra k
factor per attempt. A retained signed exponent record uses
O(min(t,k)(log k+log(t+2))+h) bits. Division by 2^h is exact integer shifting,
not a precision approximation.

Crucially, the cofactor in (B5) has range N, not N/2^h. This is not merely a
loose width analysis: CRT gives an exact bijection between

    {g mod M : gcd(g,M)=1, g=N mod 2^h}
       and (Z/NZ)^*,

and g -> w_0 is that bijection followed by multiplication by (2^h)^(-1)
modulo N. Uniformity on this fiber therefore makes w_0 exactly uniform among
units modulo N. Its smooth fraction is exactly

    #{1<=w<N : gcd(w,N)=1, w B-smooth}/phi(N).         (B7)

The fraction of unit residues modulo M meeting the prescribed congruence is
exactly 1/2^(h-1). Rejection sampling would pay this; coordinate solving avoids
the rejected attempts but gives neither uniformity on that fiber nor an
arithmetic bias toward small/smooth w_0. Under uniformity, (B7) is independent
of h. A forced factor was obtained, but the larger lifting modulus exactly
restores the original cofactor range.

**Missing lemma B.** The explicitly solved, sparsely randomized exponents must
yield enough distinct smooth w_0 under their actual pushforward law, or supply
enough short literal representatives of (B2) with useful u-Nv. Either lemma
must also pay for selecting those representatives and prove productive square
dependencies. Neither follows from known congruences, determinant, or log
optimization. For S attempts and Y distinct accepted records the cost per such
record is (setup + S*poly(ell,h,t,log B) + batch processing)/Y; Y may be zero.
**Disposition: the construction works as a conditioning primitive; its alleged
size/supply gain does not survive the two displayed implementations.**

## 5. Construction C: known smooth divisors of quadratic values via CRT

This is a genuinely different way to keep the unknown quotient small. It
recovers quadratic-sieve-style polynomial generation, rather than conditioning
a multiplicative exponent vector modulo a separate group.

### 5.1 Exact selection, root construction, and evaluation

Use B=ell^2, K=ell^2 as one fixed polynomial-scale rule. The symbolic cost
analysis also permits public larger B,K with log B,log K=poly(ell).
For the asymptotic branch assume A_max=floor(isqrt(N)/(2K+1))>=1; finite
smaller inputs can be processed by the elementary baseline. Compute N modulo
each odd p<=B and its Legendre symbol by modular powering. A zero gives a
factor. Take eligible primes p congruent to 3 modulo 4 with symbol +1, in
increasing order, multiplying them into A until the next one would exceed
A_max, then stop. If none is used,
A=1. This rule claims no lower bound on the number of eligible primes or on
the resulting A. Let nu=omega(A) and R=2^nu.

Obtain a root of N modulo each p dividing A by the explicit formula
r_p=N^((p+1)/4) mod p, and verify it by squaring. The exponent is integral,
and r_p^2=N*N^((p-1)/2)=N mod p by the eligibility test. This costs
O(ell^2+log^3 p) per prime using reduction and schoolbook binary powering.
Restricting the eligible primes makes this root step deterministic; it does
not license any lower bound on their number or on useful polynomial outputs.

For A squarefree and odd, there are exactly R CRT roots of N modulo A. With
roots r_i modulo p_i, precompute

    c_i = r_i (A/p_i) ((A/p_i)^(-1) mod p_i) mod A.

Every root is sum epsilon_i c_i mod A, epsilon_i in {-1,+1}. Initial CRT work
is O(nu*ell^3); Gray-code sign changes enumerate roots with polynomial delay
and O(nu*ell) stored bits. Enumeration has R outputs and costs R*poly(ell);
it is not a polynomial-time operation when nu grows. There is no assumption
that the roots are uniformly spaced on the real line.

For each root r choose its lift x_0 nearest sqrt(N). This choice is exact:
let x_-=r+A floor((isqrt(N)-r)/A), and compare 4N with (2x_-+A)^2 to choose
between x_- and x_-+A. The interval contains sqrt(N); since A<=sqrt(N), its
endpoints are nonnegative. No real-log or floating-point tie is involved.
For -K<=j<=K put

    x_j = x_0+Aj,
    Q_r(j) = (x_j^2-N)/A = A j^2 + 2x_0 j + c,
    c = (x_0^2-N)/A in Z.                            (C1)

Each pair supplies x_j^2 = A Q_r(j) mod N. The known factors of A are included
in the relation; they are not discarded when A is nonsquare. For A=1 this
is ordinary quadratic-sieve arithmetic.

### 5.2 The forced factor and the lattice spacing must be charged together

Since |x_0-sqrt(N)|<=A/2,

    |Q_r(j)| <= 2sqrt(N)(K+1/2) + A(K+1/2)^2
              <= (5/2)sqrt(N)(K+1/2).                (C2)

The last bound uses A(2K+1)<=sqrt(N). All x_j are positive and between
(1/2)sqrt(N) and (3/2)sqrt(N). Operands and coefficients have O(ell) bits
for this rule. Integer evaluation, gcd, and storage per candidate cost
poly(ell), before valuation recovery.

The determinant of each progression is A. Among a full period of A integers,
exactly R have x^2=N mod A; the density is R/A. In any real interval of length
J the number is at most R(J/A+1). Selecting a root constructs a member without
scanning A/R integers, but changes the natural step from 1 to A. Formula (C2)
exhibits the cancellation: the factor A removed from x^2-N is accompanied by
an A-sized change in x. A nearest lift certifies a sqrt(N)-scale quotient,
not a quotient smaller by a factor A than ordinary quadratic-sieve norms.

This is an upper-envelope calculation, not a lower bound |Q|>=sqrt(N) for
each output. Exceptionally close roots can give much smaller values. A new
algorithm exploiting them needs their population and costed selector.

There are U=R(2K+1) candidate integers if all roots are used. Within this one
A, they are distinct: different roots occupy disjoint residue classes and
different j give different integers. Positivity then makes Q distinct as well.
Across different A, a repeated x represents the same original relation
x^2-N; redistributing its known factors is not a new congruence. Even within
one A, distinct Q need not give new parity information.

The deterministic setup and all-output cost is

    (B + U)*poly(ell+log B+log K),                    (C3)

using sequential CRT enumeration and H016 batch valuation recovery on Q,
with the factors of A appended. Processing polynomial roots modulo every
factor-base prime anew for every branch instead would cost R*k*poly(ell);
that alternative is not silently suppressed. Batching scalar Q values avoids
that repeated setup and does not assume any smoothness. Storing all U values
costs U*poly(ell) bits; bounded batches reduce scratch at the price of repeated
batch-base setup, which must be included. Enumeration itself uses only
polynomial scratch beyond the prime list. For Y distinct accepted records,
the amortized generation/processing cost is (C3)/Y, with no promised Y>0.

The construction genuinely forces a known smooth part and bounds the remaining
norm. Its polynomial congruence and cost mechanism belongs to the existing
quadratic-sieve/multiple-polynomial framework. Pomerance describes sieving
quadratic values, identifies the structured smoothness assumption, gives the
L_N[1/2,1] heuristic including sparse linear algebra, and notes the
multiple-polynomial variants.
[Pomerance, pp. 73–80](https://math.dartmouth.edu/~carlp/PDF/qs08.pdf).
The original Silverman MPQS PDF was requested but blocked by HTTP 403; no
unchecked formula or implementation constant from it is used here.

### 5.3 Can an inexpensive root join improve that scale?

An explicit additional selector is possible: split the CRT sign sums into two
halves, enumerate their residues, sort one half, and for each entry of the
other query nearest circular neighbors to sqrt(N) mod A. This finds the closest
CRT root in

    O(2^ceil(nu/2)*poly(ell)) time and space,           (C4)

including list construction, sorting, and exact comparisons with sqrt(N).
Sorted predecessor/successor candidates suffice for the nearest circular sum;
the target's fractional part can be compared by squaring as above. The list
cost is additional to materializing any output. This is an on-paper
meet-in-the-middle primitive, not an executed experiment or a free CVP oracle.

It finds one best root; it does not manufacture a large population of close
roots or smooth quotients. To demand |Q|<=W for the positive x range above,

    |x-sqrt(N)| = A|Q|/(x+sqrt(N))
                 <= 2AW/(3sqrt(N)).                 (C5)

For any *fixed* root set modulo A and an independent uniform target phase,
the probability of a root within distance D_0 is at most min(1,2R D_0/A), by
the union of R arcs. For W=N^o(1), (C5) asks for a phase window with relative
length N^(-1/2+o(1)). Also R=N^o(1) when log A=O(log N): distinct primes give
A>=nu!, hence nu=O(log N/log log N) and log R=o(log N). The uniform-phase
model consequently gives no supply even after examining every root of one A.

**The actual target is not independent of the roots:** both are determined by
N, and A was selected from N. The previous sentence is a model calculation,
not an all-input or random-N theorem. No fictitious randomness is assigned to
uncomputed root locations. It states exactly what a favorable targeted-root
lemma would have to overcome, and why (C4) alone is not that lemma.

**Missing lemma C.** For the exact eligible-prime rule and a paid root selector,
prove sufficient distinct smooth Q with useful dependencies, or replace that
rule by a fully charged mechanism with a provable bias to substantially
smaller Q. Existence of many CRT roots and fast nearest-root search do not
establish this. Ordinary sqrt(N)-scale smoothness recovers the familiar
quadratic-sieve envelope. **Disposition: a valid known-style generation
primitive, but no new complete-cost survivor.**

## 6. Parity, square reconstruction, root entropy, and full factoring

For A and C let the relation be g_i^2 = z_i mod N, where z_i is respectively
r_i or A_i Q_i, completely factored over P_B with its sign. For B record

    product_{p odd} p^e(i,p) = 2^h w_i mod N.

Its signed valuation vector is e(i,p)-v_p(2^h w_i), with e(i,2)=0. All base
elements are units. Include a sign row when needed. With m=k+1 features and r retained
relations, the binary matrix has m rows and r columns; each dense relation
column has m bits. In A and C the integer valuations need O(log ell) bits
each; in B the corrected exponent needs O(h+log(t+2)) bits. Sparse records
in A,C have O(ell) nonzero valuations; B has at most O(t+ell) nonzeros before
merging. The explicit roots in A,C each occupy O(ell) bits. Full exponent
records, relation identifiers and roots are additional to parity storage.

When r>m there is a nonzero binary kernel vector, regardless of rank. This
does not mean that every new column increases rank or that a dependency
factors N. Dense elimination gives the always-available conservative
O((m+r)^3) bit bound and O((m+r)^2) parity/dependency bits. The favorable
asymptotic comparisons below grant the standard sparse solver at m^2*poly(ell)
for r=O(m*poly(ell)) with polynomial column sparsity; using dense elimination
instead worsens the comparison. All attempted dependencies and failures count.

For A,C, sum the selected integer valuations, require all to be even including
sign, multiply the retained g_i modulo N, and construct the other square root
from half the prime exponents. For B, sum the signed valuation vectors to Z_p,
then form

    X = product_p p^(max(Z_p,0)/2) mod N,
    Y = product_p p^(max(-Z_p,0)/2) mod N.

The exponents are integers because the kernel condition makes Z_p even.
In every case X^2=Y^2 mod N. Exponent summation costs its sparse input size
times the exponent width; a conservative modular-power bound is
O(k(h+log(r(t+ell)+2)+1)*ell^2), plus root products and O(ell^3) gcd work.
For A,C take h=0 in this bound. A failed gcd, including N, requires another
paid dependency or batch, not a declaration of success.

Here is a sufficient proper-split condition that isolates the missing
probability. If, conditional on the retained right sides and the selected
dependency, at least one included root is still uniform on its full square-root
fiber in G and independent of the other roots, their product is uniform on
the resulting fiber. For odd N with d>=2 distinct prime factors, that fiber
has 2^d roots. Exactly two choices are the trivial global signs of the other
constructed root; a proper split therefore occurs with probability
1-2^(1-d)>=1/2. This is the kind of conditional randomness Dixon exploits.

Neither uniformity of exponent vectors nor uniformity of square residues
implies this condition. A sampler can choose just one root in each fiber.
The smooth-prime walk is confined to H and can lack the needed root choices;
CRT roots in section 5 are roots modulo known A, not roots of a square modulo
N with the required hidden sign randomness. Section 4 has its own signed
relation distribution. No positive universal split probability is supplied
for these proposed samplers. Duplicated parity columns are not automatically
worthless: their two corresponding roots can be the productive pair. Identical
full records, however, can generate the trivial square of a known equality.

For genuinely independent epochs with total expected work C_N and proper-split
probability s_N>0, restarting costs C_N/s_N; neither symbol is supplied by a
dimension count. Adaptation requires a strategy-valid conditional or aggregate
law for the actual sampler. A theorem on each nonprime input, plus primality
testing and recursive splitting, can give full prime factorization with at
most polynomial extra bookkeeping. A balanced-semiprime argument alone does
not satisfy that all-composite contract.

## 7. Symbolic full-work comparison: what the ordinary smoothness model permits

This section is deliberately a **conditional model calculation**, not a claim
about the actual output laws above. Grant the favorable costs: B*poly(ell)
setup, S*poly(ell) generation/valuation work, k*poly(ell) retained relations,
k^2*poly(ell) sparse algebra, polynomial reconstruction overhead, a constant
productive-dependency probability, and adequate distinct population. Suppose
the tested cofactor behaves, for smoothness, like an integer of size
N^(beta+o(1)), with fixed beta>0. With B=L_N[1/2,b], the ordinary model is

    smooth probability = L_N[1/2,-beta/(2b)].

Then the complete exponent in that model is

    c(b,beta) = max(b+beta/(2b), 2b),
    inf_{b>0} c(b,beta) = sqrt(2beta),
    achieved at b=sqrt(beta/2).                       (M1)

The minimum follows directly from AM–GM on the first term, with equality
also in the second at the displayed b. This is a symbolic optimization of
the charged *model*, not an experimental fit or an algorithmic lower bound.

Thus the best optimistic envelope furnished by A or the uniformly distributed
compressed B is the random-residue scale beta=1, c=sqrt(2). C with K=N^o(1)
supplies the ordinary quadratic scale beta=1/2, c=1 under the model. Costs
for a large t, too few eligible primes or CRT outputs, duplicates,
unproductive dependencies or the extra selector (C4) can worsen these values.
These are not new factoring theorems; in particular sqrt(2) is not attributed
to Dixon's original rigorous theorem.

A merely favorable fixed power saving does not reach the heuristic NFS
frontier. At B=L_N[1/3,b] and cofactor size N^beta, the same model has

    log(1/probability)
      = (2beta/(3b)+o(1)) (log N)^(2/3)(log log N)^(1/3),

already an L_N[2/3,*] search term, before the other stages. To compete at
L_N[1/3,*], this model needs cofactor logarithms on the order of
(log N)^(2/3)(log log N)^(1/3), or a quantitatively stronger, justified
nonuniform smoothness bias. Larger bases and energy windows by themselves
provide neither. Any NFS-constant claim would additionally have to beat c_C
with its full enlarged-base and square-root costs; there is no such claim here.

## 8. Disposition and one materially changed next question

No option passes the useful-supply acceptance gate. This does not close
logarithm-lattice factoring, CRT conditioning, smooth-product methods, or
factoring generally. The precise findings are narrower:

* A has an executable flat-weight selector and an exact convolution law.
  Favorable mixing alone supplies ordinary large-residue smoothness, not a
  useful bias; the actual smoothness and root-fiber laws remain unknown.
* B cheaply solves a known group congruence of exact index 2^(h-1).
  Literal representatives can require exponentially many output bits; cheap
  modular representatives instead retain an N-sized cofactor. Neither escape
  supplies the missing distributional lemma.
* C genuinely constructs a known smooth part and a smaller quotient, but its
  charged generic envelope is the quadratic-sieve scale. The nearest-root
  join is explicit and paid; its output count and useful yield remain unknown.

No finite experiment is needed to establish these algebraic/cost distinctions,
and none is proposed as a route to promote their missing all-input laws.
Accordingly there is no new finite protocol to preregister this round. In
particular, no larger energy sweep, favorable CRT-root sample or walk-mixing
plot is recommended as a substitute for a supply mechanism. The symbolic
derivations above remain subject to independent review before acceptance.

**Changed next question: preserve useful root entropy in an existing
relation-producing algorithm.** Investigate an explicitly specified modification
of the Lee–Venkatesan randomized NFS sampler/dependency selection, with at most
poly(ell) multiplicative overhead, for the restricted family N=pq,
p and q distinct and both congruent to 3 modulo 4. Require a quantitative bound
after *all* selection and square-root steps, for example

    Pr[ Jacobi(X Y^(-1) mod N, N) = -1 ] >= ell^(-c)  (E1)

for every sufficiently large input in that family and some fixed c, with
X^2=Y^2 mod N and both units. This is a concrete testable mathematical target:
for such N the four square roots of one have Jacobi symbol -1 exactly for the
two mixed signs, so (E1) implies a proper split. The Jacobi test is executable
from N, but generating the required distribution is the missing primitive.

This revisits a named existing gap rather than claiming a new insight or
starting another child task. Lee–Venkatesan's square-congruence theorem and
conditional fruitful-congruence result are distinct; Remark 4.31 also confirms
the Coppersmith constant quoted above.
[Lee–Venkatesan, Theorems 2.1/2.3, section 7 and Remark 4.31](https://arxiv.org/html/1805.08873v1).
A simple common random mask fails immediately: replacing (X,Y) by (aX,aY)
leaves XY^(-1) unchanged. Any proposed modification must change the hidden
root-sign distribution, not merely randomize visible representatives or
collect more equal columns. Even success on this next question would initially
be a special-family rigorous improvement, not an all-input result or a better
heuristic NFS constant. No solution to (E1) is supplied here.

## 9. Source archive and handoff

[H027-adaptive-sources.json](H027-adaptive-sources.json) records URLs, retrieval
date, byte counts, hashes, text extractions, and the blocked Silverman request.
The successfully archived primary documents are Dixon 1981, Pomerance 2008,
Coppersmith 1993, Bernstein 2004, and Lee–Venkatesan v1. Their relevant portions
were inspected as described above. No claim relies on a secondary search
summary, the inaccessible Silverman text, or a numerical paper fit.

The accepted H021/H024/H025/H026 dispositions and H016 integer-processing
interface remain unchanged. No shared checks were rerun for document/source
archiving work. There is no implementation to validate and no theorem accepted
by this author. The coordinator owns disposition, independent review decisions,
STATE and subsequent task selection. Verified full factoring improvement
remains **NONE**.
