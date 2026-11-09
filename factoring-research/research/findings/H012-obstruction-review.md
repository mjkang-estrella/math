# H012 obstruction: second independent mathematical review

2026-10-08. **Disposition: ACCEPT the scoped representation obstruction.**
Verified new factoring complexity improvement: **NONE**.

The new argument in [the first independent review](H012-independent-review.md)
does prove an infinite family of actual distinct-prime semiprimes for which
the frozen H012 modulus and fixed slack require
`Omega(phi(m)*bit_length(N))` certificate components, counted separately for
each unit residue. At least one third of the unit residues individually need
`Omega(bit_length(N))` components. The same conclusion holds for distinct
certificates counted separately per residue, with a further factor two.
This defeats the proposed uniform `C(n)=O(n/log n)` full-cover premise.

No fatal mathematical error or constant repair was found. In particular, the
suggested Brun–Titchmarsh citation objection is resolved **in favor of the
original constant 4**: both Ford's displayed formula and the original
Montgomery–Vaughan Theorem 2 are short-interval bounds. I located and visually
checked the original author-hosted paper. A cumulative-only argument would
instead permit 8; that fallback also proves existence, but is unnecessary here.

The proof below makes the uniform errors, order of quantifiers, component
counting, and logarithmic-target regularity explicit. These are clarifications
of the accepted claim, not new assumptions about prime equidistribution or
certificate generation. The logarithmic extension applies to a **fixed regular
target** of the stated kind, not every function written `N^(1/5+o(1))`.

The [original finite screen](H012-certificate-reuse.md) remains a **finite
continuation pass**. Neither its observations nor the twelve finite identity
checks prove the asymptotic result. No factoring, distinct-giant-value, or
general algorithmic lower bound is accepted.

## Review boundary and evidence

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, and research/STATE.md; the full W001-deterministic report
(especially Card A and shared accounting); H012's hypothesis and finite
finding; the full first independent review, its preregistration, audit source
and saved evidence; and the relevant frozen source definitions. Also read
H015-geometric-family-bound.md for a direct scope conflict.

All writes in this round are this report and the two adjacent
`H012-obstruction-*.png` primary-source page captures linked below. No prior
report, frozen artifact, shared source, Lean file, STATE, or registry was
edited. No packages, commits, delegation, publishing, or scheduler. This round
ran no new numerical experiment, parameter sweep, certificate replay, or
finite mathematical audit; it performed read-only hash/provenance checks and
a mathematical review. Accordingly there is no new empirical evidence being
used without preregistration.

All six published SHA-256 values match the actual bytes:

```text
research/experiments/H012/certificate_reuse.py
181e97caeef68b373b639fdb3f510b0811a7c902eb83e2f6ca1ea13cb04f0f13
research/hypotheses/H012.md
17f456aa1727cff5657d7de00e66251bce3d4b27e2de2d09b5574956c00bc456
research/experiments/H012/result.json
77b7d6573586a7eda648473c1cb850ee35bbb3f9fff6a269ecc70e59378f9a07
research/findings/H012-review-preregister.md
3b6dd46a7c10e911aef0736fe689909f99ee83a3b3cbba7017ca43bca1ebf16f
research/findings/H012-review-audit.py
98e08a61ab8f0e29762cf4f0ff6cced709421fa8c215827dcdba99dd58723d06
research/findings/H012-review-audit.json
84c5a6c51db81afbe0e3239bd3cfa2fc69712f8247d2ab731d442e0ead67778b
```

The original result's embedded source/protocol hashes and the audit's embedded
source/preregistration hashes agree with these values. The reviewed first
independent report itself has SHA-256
`b37bfcccbd24b9d6b07d58d64f665e7abea2e252fcb3e475aa8ef3febedf8276`.

The unchanged audit records 96 passing rows, 9,727 certificates, 9,728 generated
directions, 9,809 Gauss iterations, and 314,101 envelope decisions. Its other
stages record 34,496 edge envelopes, 809 cover pools, and twelve exact
rectangle identities, all passing; failures is empty and elapsed time is
4.438999942969531 seconds. These are **verified records of the earlier
audit**, not claims that I reran it. Its code uses an independent rational
quadratic-extremum oracle and dynamic programming, not just the frozen
predicate/greedy implementation as their own oracle. No concern found here
requires replay. The six public odd inputs are not promised semiprimes.

## Precise theorem and quantifiers

There is an absolute threshold such that, for every initial primorial m above
it, there exist distinct primes p,q in `[m^(5/2),2*m^(5/2)]` with N=pq having
the following property. The frozen primorial-then-doubling rule selects
exactly m. Put

```text
n = bit_length(N),    K = 16*ceil(sqrt(N/m^3)),    H = K*m^2,
I_N = [ceil(N^(1/3)), floor(sqrt(N))].
```

For each unit j modulo m, allow **all** integer triples (u,v,t) satisfying

```text
v+2*u*j = 0 mod m,       N*t+u*j^2+v*j = 0 mod m^2,
(u,t) != (0,0).
```

Each selected certificate can cover only points in its exact positive-real
set `|u*z+v+N*t/z|<=H`. Require the union to cover all of I_N for every j.
Let C_j count used connected certificate components after intersecting with
I_N, and let D_j count distinct selected triples for that j. With

```text
h = #{k in Z : m^(17/8) <= 2^k <= m^(19/8)},
```

every such cover satisfies

```text
sum_j C_j >= phi(m)*h/130,
sum_j D_j >= phi(m)*h/260.
```

For at least `phi(m)/3` unit residues, simultaneously
`C_j>=h/260` and `D_j>=h/520`. Here
`h=(log2(m))/4+O(1)=n/20+O(1)`. An infinite cover trivially satisfies the
cardinality obstruction; the relevant claim concerns finite representations.
The residue set with these individual lower bounds is determined by N and
the hard-point definition, independently of how a cover is selected.

The construction also yields an unbalanced family with p in `[m^2,2*m^2]`
and q in `[m^3,2*m^3]`. In both families all factors exceed N^(1/3).
The existence proof is not an efficient procedure for locating these inputs,
and supplies no factor advice to a solver. An existential counterexample
family suffices to refute the uniform cover claim.

## Proof audit, including uniform error bounds

**1. Congruence lattice and necessary coefficient rectangles.** Subtract j
times the first congruence from the second modulo m. This gives
`u*j^2=N*t mod m`, or `u=c*t mod m` for the unit
`c=(N mod m)*j^(-2)`. Conversely that relation together with
`v=-u*j-N*t*j^(-1) mod m^2` implies the two certificate congruences.
The inverse exists modulo m^2. The obstruction only needs necessity and
therefore remains valid when v is chosen without restriction beyond validity.

Write `f(z)=u*z+v+w/z`, w=Nt. If `|f|<=H` on `[P,s^2*P]`, s>1, the
following exact identities are sign-independent:

```text
f(P)-(s+1)*f(s*P)+s*f(s^2*P) = u*P*(s-1)^2*(s+1),
s*f(P)-(s+1)*f(s*P)+f(s^2*P) = (w/P)*(s-1)^2*(s+1)/s^2.
```

Both sums of absolute weights equal `2(s+1)`. Hence, with r=s^2,

```text
|u| <= 2H/[P*(s-1)^2],
|t| <= 2r*H*P/[N*(s-1)^2].                       (A)
```

For every N in `[m^5,4*m^5]`, `sqrt(N/m^3)>=m>=1`, so the ceiling gives
`H<=32*sqrt(N*m)<=64*m^3`. Also `H/N<=32/m^2<=64/m^2`.
Thus the claimed uniform enlarged rectangle is valid:

```text
U(P) = 128*m^3/[P*(sqrt(r)-1)^2],
T(P) = 128*r*P/[m^2*(sqrt(r)-1)^2],
B_r := U(P)*T(P)/m = 16384*r/(sqrt(r)-1)^4.       (B)
```

The upper bound on H/N is deliberately loose; this is harmless. These
rectangles depend on m and P, not the later choice of N in the window.

**2. Exact average, including all nonprimitive pairs.** For unit c modulo m,
let Z_c count pairs with `0<|u|<=U`, `0<|t|<=T`, `u=c*t mod m`. Define
`A_q(Y)=#{a in Z: 0<|a|<=Y, gcd(a,q)=1}` and take `phi(1)=1`.
Necessarily `gcd(u,m)=gcd(t,m)=d`. Writing `(u,t)=d*(a,b)` and q=m/d,
both a,b are units modulo q. Exactly one unit class c modulo q solves the
relation. Reduction of units modulo m onto units modulo q is surjective,
with every fiber of size `phi(m)/phi(q)`; this follows prime by prime from
the Chinese remainder theorem. Therefore, for every m, including nonsquarefree
m and q=1,

```text
E_c Z_c(U,T) = sum_{d|m} A_(m/d)(U/d)*A_(m/d)(T/d)/phi(m/d).   (C)
```

No condition `gcd(u,t)=1` was imposed or used. Probabilities equal 1/phi(q),
not 1/m. Axis pairs are temporarily omitted and dealt with in step 3.

Here is an explicit uniform error bound for (C). Fix `0<epsilon<=1/2` and
B>0, and assume `m^epsilon<=U,T<=m^(1-epsilon)` and `UT<=Bm`. Put
`tau=tau(m)` and `D=m^(epsilon/2)`. Mobius inversion, including the two
signs, gives

```text
A_q(Y)=2*sum_{e|q} mu(e)*floor(Y/e)
      =2Y*phi(q)/q + E_q(Y),      |E_q(Y)|<=2*tau(q).
```

For d<=D, the main term in its summand is `4UT*phi(m/d)/m^2`. Its mixed
errors are at most `4*(U+T)*tau/m` and its squared error is at most
`4*tau^2/phi(m/d)`. The elementary inequalities
`(m/d)/phi(m/d)<=m/phi(m)<=2^omega(m)<=tau` and
`sum_{d|m}phi(m/d)=m` now give the following bound after summing and using
nonnegative upper bounds for errors:

```text
sum_{d|m,d<=D} (...) <= 4UT/m
    + 4*tau^2*(U+T)/m + 4*tau^4*D/m.
```

For d>D, use `A_q(U/d)<=2U/d` and the analogous bound for T. This tail is
at most `4*(UT/m)*tau*sum_{d|m,d>D}(1/d)<=4B*tau^2/D`. Consequently

```text
E_c Z_c <= 4UT/m
    + 8*tau(m)^2*m^(-epsilon)
    + 4*tau(m)^4*m^(-1+epsilon/2)
    + 4B*tau(m)^2*m^(-epsilon/2)
  = 4UT/m + o(1),                                      (D)
```

uniformly throughout the stated range. The error contains no hidden dependence
on U,T or the dyadic point. Empty ranges when epsilon>1/2 need no theorem.

For completeness, `tau(m)=m^o(1)` here is elementary: for any fixed delta>0,
for primes p>=2^(1/delta) one has `a+1<=2^a<=p^(delta*a)`; for each of the
finitely many smaller primes, `(a+1)/p^(delta*a)` has a finite maximum over
a>=0. Multiplying gives `tau(m)<=C_delta*m^delta`. Choosing delta sufficiently
small for each fixed epsilon makes every error in (D) tend to zero. Thus
neither prime distribution nor a smooth-modulus heuristic is hidden in (D).

**3. Hard points with the correct average.** Fix r=2^32 and
`Z={2^k:m^(17/8)<=2^k<=m^(19/8)}`. For all sufficiently large m, even the
enlarged interval `[z/r,r*z]` is inside I_N for every z in Z and every N
in the window: its lower exponent 17/8 exceeds 5/3, and its upper exponent
19/8 is less than 5/2, with fixed multiplicative constants absorbed. The
integer endpoint rounding therefore causes no loss.

Use the two rectangles (B) with P=z/r and P=z. Their u half-widths are
fixed positive multiples of powers between m^(5/8) and m^(7/8), and their
t half-widths are fixed positive multiples of powers between m^(1/8) and
m^(3/8). Uniformly in z, all four half-widths eventually lie between
m^(1/16) and m^(15/16), and each product is B_r*m. Apply (D) with these
fixed epsilon and B_r.

Call c soft at z if either rectangle contains an informative congruent pair.
Because U,T<m and c is a unit, t=0 forces m|u and u=0 forces m|t;
neither axis can give a nonzero pair inside these rectangles. Thus (C)
counts every possible relevant pair. Markov on Z_c and a union bound over
the **two rectangles** give

```text
Pr_c[soft at z] <= 8B_r+o(1)
 = 2^(-15)/(1-2^(-16))^4 + o(1) < 1/1000                (E)
```

eventually, uniformly in z. For example the constant term is below 1/32000,
using `(1-x)^4>=1-4x` at x=2^(-16), so there is ample fixed error margin.
There is no union bound requiring every one of the growing number h of
test points to be hard simultaneously for a slope.

For a unit input residue a, set `c_j(a)=a*j^(-2)` and let S(a) count soft
pairs (j,z). For each fixed j, a -> c_j(a) is a bijection of the unit group.
We therefore obtain `E_a S(a)<=phi(m)*h/1000`, without any distribution
assumption on j^2. Let

```text
Bad = {a : S(a)>phi(m)*h/2}.
```

Then `|Bad|<=phi(m)/500`. Every other input residue has at least
`phi(m)*h/2` hard pairs. This good/bad set is defined **before** choosing
the semiprime and is valid for the entire N-window because (B) was uniform.

**4. Transfer to actual semiprimes, with sources checked.** The short-interval
form needed is

```text
pi(x+y;k,b)-pi(x;k,b) < 2y/[phi(k)*log(y/k)]
```

for real x,y>0, coprime positive integers b,k, and y>k. This is exactly
[Montgomery–Vaughan, The large sieve (1973), Theorem 2, equation (1.10),
printed p. 121](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3).
The [saved page capture](H012-obstruction-mv-page121.png) was visually inspected
because the PDF's text layer misreads the equation. Ford's
[opening display](https://www.ford126.web.illinois.edu/wwwpapers/sigphi.pdf#page=1)
also explicitly has `pi(x+y)-pi(x)`, not just a cumulative pi bound.

For the total number of primes, the original
[Rosser–Schoenfeld paper (1962), Theorem 1 and Corollary 1, printed p. 69,
equations (3.2) and (3.5)](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)
gives `x/log x<pi(x)` for x>=17 and
`pi(x)<(x/log x)*(1+3/(2log x))` for x>1. I also visually checked its
[saved page](H012-obstruction-rs-page69.png). These bounds imply

```text
Q(X) := pi(2X)-pi(X) = (1+O(1/log X))*X/log X.
```

No arithmetic-progression prime number theorem is used. Choose
X=m^(5/2), and fix any prime q in `(X,2X]`; Q(X) tends to infinity.
For every unit b, the displayed short-interval theorem gives

```text
#{p in (X,2X] : p=b mod m}/Q(X)
 <= [2*log X/log(X/m)]*(1+O(1/log X))/phi(m)
 = (10/3+o(1))/phi(m) < 4/phi(m)                       (F)
```

eventually, uniformly in b. Multiplication by this q permutes unit residues,
since q>m. At most `4/500` of the available p have `pq mod m` in Bad.
The remaining number tends to infinity, so exclude the one possibility p=q
and choose another p. Both factors are units modulo m and exceed N^(1/3)
for large m. Using half-open intervals avoids a possible prime endpoint;
they are contained in the claimed closed intervals.

For the unbalanced version, use X=m^2 for p and fix q in `(m^3,2*m^3]`.
The coefficient in (F) tends to 4 and is eventually below 5. At most 5/500
of p are lost. The prime windows are disjoint for large m, and again
`m^5<N<=4*m^5`, with `p=Theta(N^(2/5))>N^(1/3)`.

If only cumulative Brun–Titchmarsh were available, bounding this interval
by `pi(2X;m,b)` would give limiting density constants 20/3 and 8 in the
balanced and unbalanced cases. Safe eventual constants would then be 8
and 9 respectively, not 4 and 5; both are still below 500. This explicitly
checks the proposed fallback without incorrectly attributing that limitation
to the sources actually read.

The exact frozen modulus selection follows without asymptotics beyond m
being a sufficiently large initial primorial:

```text
m <= floor(N^(1/5)) <= floor(4^(1/5)*m) < 2m.
```

The next initial primorial is m times a prime greater than 2. Thus the
primorial-building loop stops at m and its doubling loop does not execute.
This checks the actual rule, not merely `m=N^(1/5+o(1))`. As primorials
grow, these N-windows are disjoint, so the construction supplies infinitely
many distinct admissible inputs.

**5. Components, boundaries, and counting.** Fix a good input just chosen.
Intersect each maximal positive-real certificate component with compact I_N.
The result, if nonempty, is a closed interval [L,Q], possibly a singleton.
If it contains a hard point z and Q/L>=r^2, then either z/L>=r or Q/z>=r.
In the first case it contains `[z/r,z]`; in the second it contains `[z,r*z]`.
Either contradicts hardness via (A)-(B). Thus every component containing
a hard point has Q/L<r^2.

Such a component contains at most 65 dyadic test points. In fact 64 would
suffice with the strict inequality, but 65 is a valid conservative bound.
Closed endpoints and equality Q/L=r^2 cause no exception. Unbounded
positive-real components cause no exception after the intersection with I_N.
Any explicitly selected subinterval satisfies the same charging bound.

Since `f'(z)=u-N*t/z^2` has at most one zero, f is monotone on at most two
positive-real intervals. Its inverse image of [-H,H] consequently has at
most two connected components; zero-coordinate cases are monotone. A distinct
triple can therefore cover at most 130 hard test points for a fixed j.
Arbitrarily subdividing an interval cannot reduce these required counts.

Let h_j be the number of hard points for residue j. We have

```text
sum_j h_j >= phi(m)*h/2,    C_j>=h_j/65,    D_j>=h_j/130.
```

These prove both total bounds. If J is the number of residues with h_j>=h/4,
then `sum_j h_j <= J*h+(phi(m)-J)*h/4`. Hence J>=phi(m)/3, which proves
the individual bounds. This charges **hard** points only; it asserts no
constant capacity for every certificate everywhere. The direction `(m,0)`
can still cover Theta(n) low-scale cells, exactly as the earlier review noted.

All sufficiently-large thresholds above can be taken simultaneously: r,
epsilon, B_r and the prime-density margins are fixed; (D) is uniform over
the whole band; the prime estimates are uniform in the residue. No threshold
depends on the later chosen j, z, p, q, or certificate pool.

## Logarithmic rebalancing: accepted with explicit regularity

First prescribe an initial primorial m, a scale `X=m^(5/2+o(1))`, a window
`N in [X^2,4*X^2]`, and a fixed constant A with `H<=A*sqrt(N*m)`.
Replace the band by `[X*m^(-3/8), X*m^(-1/8)]`. Applying (A), valid
uniform enlarged rectangles are

```text
U(P)=4A*X*sqrt(m)/[P*(sqrt(r)-1)^2],
T(P)=4A*r*P*sqrt(m)/[X*(sqrt(r)-1)^2],
UT/m=16A^2*r/(sqrt(r)-1)^4.
```

They have the same exponent ranges as before. Choose a fixed power of two
r large enough for `8*16A^2*r/(sqrt(r)-1)^4<1/1000`; choose it with a strict
margin for the uniform errors. The band and both side intervals are inside
I_N eventually: their lower end divided by `(4X^2)^(1/3)` is
`m^(11/24+o(1))` up to a fixed factor, and their upper end divided by X
is m^(-1/8) up to a fixed factor. The same proof gives h=Theta(n), and
`2*log X/log(X/m)->10/3` still supplies the prime transfer. For the frozen
ceiling, A=32 works since `sqrt(N/m^3)=m^(1+o(1))` tends to infinity.

To make the selected modulus equal this m under a modified target, it is
enough to use the following explicit class. Let

```text
F(y)=y^(1/5)*L(y),
L(y)=c*(log y)^alpha*(log log y)^beta,
```

with c>0 and alpha,beta fixed, and apply primorial-then-doubling to
floor(F(N)). The function is eventually continuous, increasing and unbounded,
`log L(y)=o(log y)`, and
`F(lambda*y)/F(y)=lambda^(1/5)*(1+o(1))` uniformly for 1<=lambda<=4.
Choose y=X^2 solving F(y)=1.1m. Then `X=m^(5/2+o(1))`, and uniformly
through the entire prime-product window

```text
F(N)/m in [1.1, 1.1*4^(1/5)+o(1)] subset (1,2)
```

eventually. Thus its floor is at least m and below 2m, and the exact same
modulus is selected. More general fixed targets require these regularity
properties to be checked, not assumed from an exponent notation.

W001's target after substituting C=n/log n is, up to a fixed multiplier,
`N^(1/5)*(log n/n)^(4/5)`. Replacing bit length by its continuous logarithm
changes this factor by 1+o(1), uniformly on `[y,4y]`; it fits the preceding
argument with alpha=-4/5 and beta=4/5. The margin from 1.1m to either m
or 2m absorbs both the bit-length jumps and the final floor. This validates
the intended logarithmic extension without asserting that every slow-looking,
discontinuous, or adaptive target has such a window.

## Consequences, retained costs, and reopening condition

Accept closure of the **uniform fixed-slack, per-residue, full-real-interval
cover-compression premise** for the frozen modulus rule and the explicit
regular logarithmic retargeting just described. The argument grants an
unrestricted pool and free generation; improving Gauss reduction, centering,
endpoint calculations, or greedy implementation does not repair that premise.
It does not imply the same lower bound on distinct modular giant values,
optimal shared encodings, or runtime.

The appropriate comparison in W001 is the general deterministic
`O(N^(1/5)*n^(16/5)/(log n)^(3/5))` theorem of
[Harvey–Hittmeir, Theorem 1.1](https://arxiv.org/pdf/2105.11105).
The [Gao–Feng–Hu–Pan v1 Theorem 1.1](https://arxiv.org/html/2512.19076v1)
states its improvement for balanced semiprimes; its scope is not a uniform
H012 full-cover theorem. These primary statements were checked directly;
this review makes no comprehensive priority or latest-best-bound claim.

Full algorithm accounting still requires all residues, generation and
selection, modular giant computation, a signed baby span through 2K,
factor-or-high-stride-order preparation, product/evaluation and sorting,
collision localization, metadata, and verified extraction. The shared
`O(G*n^3+K*n^2)` expression is an upper bound for a specified search method;
one cannot substitute a lower bound for records into it to obtain a runtime
lower bound. No additional logarithmic speedup, GNFS gain, or polynomial-time
factoring conclusion follows. The existing Lean extraction lemmas remain
algebraic invariants and do not formalize this analytic theorem.

The balanced witnesses can be handled by a method that knows or first tests
their balanced size range. Unbalanced witnesses also have a narrow promised
range if that promise is supplied. An algorithm that adaptively succeeds early,
certifies impossible residue/size pairs, uses integer-only coverage, changes
the envelope/slack tradeoff, or searches different moduli need not construct
the representation counted here. No average over all semiprimes, no hard
family for factoring, and no all-input computational lower bound was proved.

There is no direct conflict with
[H015's fixed-family count](H015-geometric-family-bound.md): it concerns
keys `(u,t,v mod m^2)` and whole balanced cells. Its exclusion of u=0 at
that scale does not forbid H012's broad low-scale axis direction. Neither
report bounds distinct giant values or closes general cross-residue sharing;
I have not treated H015 as an independently accepted solution to that issue.

**Reopen only for a concrete, costed mechanism that escapes a stated
hypothesis**, particularly constructive cross-residue sharing with recovery
metadata, or a uniformly correct adaptive size search that avoids full covers.
It must pay for detecting useful sharing or excluding/choosing intervals,
including unsuccessful work, without factor or order advice. Alternatively,
a mathematical counterexample to a lemma or quantifier above would reopen
this disposition. Larger finite reuse ratios cannot do so. No mathematical
objection remains unresolved within the theorem's stated scope; shared/adaptive
factoring improvements remain open research questions, not consequences of it.

Primary-source capture provenance (source reading, not a numerical audit):

```text
H012-obstruction-mv-page121.png
source: Montgomery–Vaughan author PDF above, PDF page 3 / printed page 121
sha256: 11f21e945b18bdf538820097ac2ef3a79ff5d2ec397fd3082cf831887097add5
H012-obstruction-rs-page69.png
source: Rosser–Schoenfeld scan above, PDF page 6 / printed page 69
sha256: c1faceab6e49fb9e526a07b876214fe8b0f326f822f3cbcb72745ba1ed9c9ad7
```
