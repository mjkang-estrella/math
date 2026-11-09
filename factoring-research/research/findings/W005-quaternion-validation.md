# W005 — Independent validation of quaternion mechanism B

2026-10-08. **Disposition: the single-reflection realization with norm-unit direction is closed as an advantage over its scalar dot-product gcd. General pairs are not closed by the norm-of-difference test. Verified end-to-end factoring improvement: NONE.**

This is an independent symbolic review of the brief supplied in the task, not a review of another child's findings. No mathematical program, numerical search, experiment, sampler, or benchmark was run. The small example below is a hand-derived counterexample. Only this report and its assigned-prefix supplement are written; original reports, shared state, registries, harness, Lean, and the parent's lead direction are untouched.

The main conclusions are:

- Correct the handedness: a greatest common **right divisor** generates a **left ideal** and detects common right kernels. A greatest common left divisor generates a right ideal and detects common images.
- With the precise hypotheses below, both reflection gcd norms equal `gcd(N, 2<w,A>)`, including prime powers. This completely includes the scalar-gcd-equals-N case.
- For general pairs, `gcd(N, norm(A-B))` can equal N while a quaternion gcd splits N. Nevertheless, an exact coefficient gcd of `A*conj(B)` recovers the right-gcd norm without quaternion Euclidean division; `conj(A)*B` does the same for the left gcd.
- A primary unconditional expected-polynomial four-squares generator is available. A [supplement](W005-quaternion-validation-sampler-law.md) proves a right-orientation law for its precisely fixed core; collisions remain rare for large prime factors. The parent supplied no fast-sampler claim.
- An uncancelled denominator divisible by N must not be inverted. Exact cancellation can still make the reflection valid. The explicit generator `B=A*i` illustrates this exception, but has a severe local success obstruction.

## 1. Conventions, integral gcds, and their cost

Throughout, n is the ordinary binary bit length of N.

Write O for the Hurwitz order

    Z^4 union (Z+1/2)^4,
    norm(a+bi+cj+dk) = a^2+b^2+c^2+d^2,
    conjugation(a+bi+cj+dk) = a-bi-cj-dk.

Half coordinates must all occur together. An integral Z-basis is
`1,i,j,h`, where `h=(1+i+j+k)/2`. For Cartesian coordinates `(a,b,c,d)`,
the coordinates in this basis are `(a-d,b-d,c-d,2d)`.
Primitive means not in `m O` for an integer `m>1`, rather than an unspecified
coordinate convention. This is the convention of Coan–Perng, Definition 4.1;
their Proposition 2.3 and Corollary 2.4 establish the two Euclidean divisions
and principality of the corresponding ideals. [CP]

For integral A,B, define D_R and D_L by

    O A + O B = O D_R,          A O + B O = D_L O.

Thus `A=a D_R, B=b D_R`, while `A=D_L a', B=D_L b'`.
Generators are unique up to a unit on the left and right, respectively.
Their positive norms are unambiguous. Multiplicativity proves

    norm(D_R), norm(D_L) divide gcd(norm(A),norm(B)).

In particular, for two integral norm-N elements, a norm strictly between
1 and N is a valid factor. The norm of the scalar quaternion N is N^2;
this must not be confused with a quaternion of norm N.

Here is a concrete gcd algorithm and a conservative bit bound. For right
divisors divide `A = q B + R`: form `A*conj(B)/norm(B)` and select its
nearest point from the integer and half-integer cosets. For left divisors use
`conj(B)*A/norm(B)` and `A = B q + R`. To see the norm reduction, let
`0<=t_j<=1/2` be the four distances from the nearest integers. The two
squared distances are `S=sum(t_j^2)` and `T=sum((1/2-t_j)^2)`.
Since `S<=sum(t_j)/2`, either `S<=1/2` or `T<=1/2`.
Consequently each nonzero remainder has at most half the divisor's norm.
For L-bit input norms there are O(L) divisions on O(L)-bit integers.
Exact rounding, multiplication, and schoolbook division give O(L^3) bit
time. Let M(L) denote L-bit integer multiplication cost. With division
cost O(M(L)), the same algorithm costs O(L M(L)).
This counts the divisions, not just the number of gcd calls.

For factoring, handle even composite N immediately by returning 2. All local
claims below concern **odd N**. Neither the rank-one-line model nor
division by 2 is imported at the prime 2.
For a norm-N input A, a nontrivial scalar content in the stated integral
basis already gives a proper divisor: if `g O` contains A, then `g^2|N`.

## 2. Local kernels, primitive rank, and prime powers

For each odd p, `O tensor Z_p` is `M_2(Z_p)`, with norm equal to determinant
and conjugation equal to adjugation. This is a proof device; the algorithms
below do not need p or a computed splitting. For completeness, choose
`u^2+v^2=-1` in Z_p. A solution exists modulo p by intersecting two sets
of `(p+1)/2` square residues, and lifts because one of `2u,2v` is a unit.
The matrices

    I = [ 0  1 ],    J = [ u   v ]
        [-1  0 ]        [ v  -u ]

have squares -1 and anticommute; `1,I,J,IJ` form a basis since 2 and
`u^2+v^2` are units. This gives the asserted integral splitting.

Suppose `p^e || N` and A is primitive of norm N. Its local Smith form is
`diag(1,p^e)`, up to unit factors. Thus A modulo p has **rank one**.
For another primitive norm-N B, the following are equivalent:

    p | norm(D_R);
    A and B have the same right kernel modulo p;
    their row spaces modulo p coincide.

Indeed, matrices in `M_2(Z_p) A` have rows in the row lattice of A.
The sum of the two row lattices has index divisible by p precisely when
their reductions span one line rather than the whole two-dimensional space.
Its index valuation is `v_p(norm(D_R))`. For D_L replace rows/kernels by
columns/images, or equivalently by left kernels.

More precisely, put A into `diag(1,p^e)` by invertible row operations and
a common invertible column change, and let the correspondingly transformed
B be `(b_ij)`. Its row lattice sum with A has index

    p^k,  k = min(e, v_p(b_12), v_p(b_22)).                 (1)

The convention is `v_p(0)=infinity`. Formula (1) handles all prime powers,
not merely divisibility by p. When B also has primitive norm N, its kernel
modulo `p^e` is a free rank-one summand. Then k is the largest `0<=r<=e`
for which the two kernel lines agree modulo `p^r`.
One way to check this last description is to normalize a primitive kernel
vector to `(z,1)` whenever its reduction agrees with `(0,1)`; its annihilating
row lattice has generators `(1,-z),(0,p^e)`.

Primitivity is essential to this rank-one formulation. If A is zero modulo
p, it has a two-dimensional kernel. A squarefree norm makes primitivity
at its prime divisors automatic; repeated prime factors do not.

## 3. Exact closure of the norm-unit Householder proposal

Let A be primitive in O with odd norm N, let `w in Z^4` be nonzero, and set

    t = norm(w),   r = 2<w,A> = tr(A*conj(w)) in Z,
    B = A - (r/t) w,                 C = tB = tA-rw in O.

Assume `gcd(t,N)=1`. The norm expansion gives `norm(B)=N` and
`norm(C)=t^2 N`. B need not belong to O. Its denominator is a unit at
every p dividing N, however, so it belongs to the localization of O
obtained by inverting integers coprime to N. The integral computation to
use is `gcrd(A,C)` or `gcld(A,C)`, retaining the original A.
Their norms still divide N. Clearing both inputs unnecessarily can add
irrelevant factors outside N; then intersect the resulting norm with N.
For a rational scalar `u/v` with `gcd(v,N)=1`, its gcd with N means
`gcd(u,N)`; this is independent of the chosen unit denominator.

**The exact identity is**

    norm(gcrd(A,C)) = norm(gcld(A,C)) = gcd(N,r).           (2)

Proof: locally at `p^e || N`, w is an invertible quaternion because its
norm t is a unit. If `h=v_p(r)`, then

    O_p A + O_p C = O_p A + O_p rw = O_p A + p^h O_p.

The Smith form of A makes its row lattice sum
`Z_p(1,0) + Z_p(0,p^min(e,h))`. The right gcd norm therefore has
valuation `min(e,h)`. Column lattices give exactly the same left-gcd
valuation. No prime outside N divides either gcd norm, proving (2).

This also proves the parent's local invertible-difference argument:
`B-A=-(r/t)w` is invertible modulo p if `p does not divide r`; if p divides
r, then `B=A mod p`. In the latter case B retains A's rank one.
Thus either both orientations match or neither does. For odd N,
`gcd(N,2<w,A>)` is the precise integral meaning of the proposed scalar
`gcd(N,<w,A>)` when A has half coordinates.

If A has local Smith exponents `a,b` with `a+b=e`, the actual reflection
formula is instead

    v_p(norm(gcd)) = min(a,h)+min(b,h).

For example, symbolically take `A=p`, `w=1`, with p odd. Then
`N=p^2`, `r=2p`, and `B=-p`: the quaternion gcd has norm `p^2`, while
`gcd(N,r)=p`. The preliminary content test already finds p.

Finally,

    norm(A-B)=r^2/t.

Its scalar gcd with N has exponent `min(e,2h)`, whereas (2) has exponent
`min(e,h)`. Supports agree, but multiplicities need not. If `gcd(N,r)=N`,
the reflection gcd norm really is N: no hidden split survives this case.
If a nonzero r is shortened below an unknown p in absolute value, that
excludes p divisibility. It does not amplify the desired event.

## 4. General pairs: difference norms lose information; product coefficients do not

For any integral equal-norm pair,

    norm(D_R), norm(D_L) divide gcd(N,norm(A-B)).           (3)

For example, `A-B=(a-b)D_R` proves the right statement. Thus a proper
scalar gcd in (3) already factors N and a scalar gcd of 1 excludes both
quaternion successes. A scalar gcd of N is inconclusive.

At an odd p where both matrices have rank one, write
`A=u v^T`, `B=x y^T`. Then

    det(A-B) = -det[u,x] det[v,y].

Singularity of the difference is the **union** of equal-image and
equal-kernel events. It need not identify which handedness matches.

There is a stronger inexpensive exact test. For X in O, let `c(X)` be
the gcd of its four coordinates in the integral basis of section 1.
If A is primitive with odd norm N and B is any integral quaternion, then

    norm(gcrd(A,B)) = gcd(N,c(A*conj(B))),
    norm(gcld(A,B)) = gcd(N,c(conj(A)*B)).                 (4)

Equivalently take the gcd of N and the four **doubled Cartesian
coordinates** of the displayed product; doubling is harmless for odd N.
This returns a gcd's norm, not a quaternion generating its ideal. It does
not eliminate the work of constructing a norm-N quaternion in the sampler.

Proof of the right formula: use the local transformations of (1).
Under these transformations, `A*adj(B)` changes only by an invertible
matrix on the left and a unit scalar, so its scalar content is preserved.
For `A=diag(1,p^e)` it is

    [ b_22       -b_12    ]
    [-p^e b_21    p^e b_11].

Its content valuation, capped at e, is exactly (1). Take this equality at
every p dividing N. Conjugating the right-gcd statement proves the left
formula. This proof does not assume squarefree N, and needs no local
splitting computation in the implementation.

**Hand-derived counterexample, also an explicit changed generator.** Put

    a=1+i+j, b=1+2i,
    A=ab=-1+3i+j-2k,     B=A i=-3-i-2j-k,     N=15.

Both inputs are primitive and have norm 15. Direct identities give

    norm(A-B)=30,
    A*conj(B)=-5i-10j+10k,     conj(A)*B=15i.

For instance `a i conj(a)=i+2j-2k` and b commutes with i, proving the
first product identity without a search. Formula (4) gives right-gcd
norm 5 and left-gcd norm 15, although the difference-norm scalar gcd is
15. This refutes general domination by that one scalar norm test.
The displayed a,b are a proof of the example, not advice given to a solver.

## 5. An exact-cancellation escape, with its actual limit and cost

For **any** norm-N A, the generator `B=A i` is a fixed signed permutation
of coordinates and needs no factors. It is also the reflection with

    w=A-A i=A(1-i),   t=2N,   r=2N,   r/t=1.

When A has Hurwitz half coordinates, w still has integer coordinates.
Thus `gcd(t,N)=N` but exact cancellation makes B integral. The blanket
statement “a nonunit denominator cannot be used” needs this qualification:
one cannot invert it modulo N; one may cancel it exactly over Q and check
the **remaining** denominator. Here w itself is not norm-unit, so (2)
does not apply. This is a concrete escape from that representation's
hypothesis, not from all scalar computations: use (4).

Given A, generating B costs O(n) bit operations and obtaining the right
gcd norm uses one quaternion product and at most four scalar integer gcds
with N, conservatively O(n^3) schoolbook bit time. No quaternion quotient
sequence is needed for the extraction. Acquiring A still costs the chosen
generator's full S(n), below. One attempt therefore costs
`S(n)+O(n^3)` in expectation when that generator is used.

This escape does **not** establish a fast splitter. Locally
`ker(A i)=i^{-1}ker(A)`, so right-gcd success at p requires an eigenline
of i. Its characteristic polynomial is `X^2+1`. For `p=3 mod 4` there
is no such line; for `p=1 mod 4` there are two. Under a *separately
assumed uniform line distribution*, the respective probabilities are
0 and `2/(p+1)`. In particular, on odd N supported entirely on primes
`3 mod 4`, primitive A gives right-gcd norm 1 every time. The left gcd
always has norm N because B is a right unit multiple of A.
For the specific Pollack–Treviño core fixed in the supplement, the
obstruction is stronger: its support avoids those eigenlines also at
primes `1 mod 4`. Thus `B=A i` always has right-gcd norm 1 after that
sampler's preliminary factor checks. The example in section 4 proves an
algebraic escape, but its useful A is outside this sampler's support.

## 6. Independent orientations: only the specified idealized law

The following model is an assumption, not a conclusion about the generator:
for each `p^e || N`, each sample's right-kernel line is uniform in
`P^1(Z/p^e Z)`; choices at different primes and in different samples are
mutually independent. Primitive columns modulo units give

    |P^1(Z/p^e Z)| = (p^(2e)-p^(2e-2))/(p^e-p^(e-1))
                    = p^(e-1)(p+1).

Every reduction to `P^1(Z/p^r Z)` has equal-size fibers. Thus if k is
the right-gcd norm valuation from (1),

    Pr(k >= r) = 1/(p^(r-1)(p+1))           (1<=r<=e),
    Pr(k = 0)  = p/(p+1),
    Pr(k = r)  = (p-1)/(p^r(p+1))           (1<=r<e),
    Pr(k = e)  = 1/(p^(e-1)(p+1)).

These k's are independent across primes in this model. For distinct primes
`N=pq`, one pair splits by its right gcd with probability

    1/(p+1) + 1/(q+1) - 2/((p+1)(q+1))
    = (p+q)/((p+1)(q+1)).

For m samples the probability of no p-orientation collision is
`product_{j=0}^{m-1}(1-j/(p+1))` until the pigeonhole cutoff. Hence a
constant collision probability needs order `sqrt(p)` samples. Balanced
semiprimes give order `N^(1/4)` samples. This is a **sample count**:
naively checking all pairs still takes order p gcd tests. Hashing unknown
local orientations, or an efficient batch detector, has not been supplied.
Independent random seeds alone do not imply uniform orientations or CRT
independence. The supplement supplies a separate proof for one actual
sampler, with a different law at primes `1 mod 4`; this model is not
silently transferred to it.

## 7. Primary algorithm found; acquisition and remaining cost

[Pollack–Treviño, *Finding the Four Squares in Lagrange's Theorem*,
Integers 18A (2018), A15](https://math.colgate.edu/~integers/sjs15/sjs15.pdf)
gives an unconditional generator in §4, pp. 8–13; §3 is ERH-conditional.
Its amended trial (T), p. 11, and final Gaussian/Hurwitz gcds have expected
cost `O(n^2/log n)` arithmetic operations; p. 2, footnote 3, gives bit cost
`S(n)=O(n^2 M(n)/log n)`, or `O(n^4/log n)` schoolbook.
This is expected time. The paper supplies no orientation guarantee. [PT]

The core's intermediate integer coordinate gcd is 1. Its odd-norm right
divisor is therefore Hurwitz-primitive. Preprocessing that finds a small
proper divisor already splits N. Thus primitivity requires no unpriced
rejection loop.

For general independently generated pairs, one fully priced *attempt* is:
run this generator twice, test content, and apply (4). Its expected cost is
`2 S(n)+O(n^3)`. For T disjoint attempts it is
`O(T(S(n)+n^3))`. The supplement proves the right-gcd success probability
rho for its fixed core: expected time until a split is bounded by
`O((S(n)+n^3)/rho)`. On balanced semiprimes `rho=Theta(N^(-1/2))`.
For m retained samples with all pair tests, the bound is
`O(m S(n)+m^2 n^3)`, with O(mn) bits to retain the samples, in addition
to the sampler's workspace. These are conservative symbolic accounting
bounds, not a reviewed implementation or a factoring complexity theorem.

For the original reflection, with b bits per coordinate of w, computing
t,r and their scalar gcds costs conservatively `O((n+b)^3)` bit time,
plus the full cost of acquiring A and choosing w. The cleared C has
O(n+b)-bit coordinates, so charging its Euclidean algorithm gives the
same conservative polynomial scale but redundant work. Equation (2)
lets the parent omit C and the extraction's quaternion divisions. Finding
a w with a useful scalar gcd is exactly the remaining task; the reflection
adds no success event. No smoothness or order-finding stage is replaced
until a complete generator-and-success argument is provided.

## 8. Scoped disposition and next decisive proof

Accept the local invertible-difference falsifier, corrected for handedness,
primitive rank, prime powers, and rational denominators as in (2). Reject
the norm-unit single reflection as a way to outperform its already
available dot-product gcd. Do not extend that rejection to every rational
reflection: the exact-cancellation example in section 5 lies outside it.
Nor does the proof close comparisons of nonadjacent outputs from multiple
reflections, where the difference need not be a scalar times one unit.

The useful replacement computation for arbitrary pairs is (4), retaining
all four product coordinates rather than one difference norm. It saves
quaternion Euclidean quotient construction, not the missing favorable-pair
generation. The explicit unit-multiple generator avoids the reflection's
norm-unit assumption but fails on the stated prime family. A materially
stronger next proposal must specify a generator and prove how often these
coefficient gcds are proper, at what total acquisition and bit cost.
The supplement discharges the joint right-orientation distribution
obligation for one precisely fixed sampler, including trial (T)'s
conditioning. It does not improve the birthday exponent or pay for a
faster pair detector. A useful replacement must change that rare-match
law or supply a fully priced detection computation. No new experiment
is authorized or proposed for execution here.

## Read scope and reproducibility

The supplemental sampler deduction was reached afterward using the same
primary text, without reading another child's results. Only this report
and its exclusively owned `-sampler-law.md` supplement were written.

Local full reads: `AGENTS.md`, `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md`,
`README.md`, `docs/SPECIFICATION.md`, and
`research/findings/Norm2-shallit-source-note.md`. The supplied user message
is the mechanism-B input, including the parent's additional objection;
no parent hypothesis file or sibling-child report was read. After the
independent reflection and general-pair conclusions were reached and
reported in commentary,
`research/STATE.md` lines 1–35 and 760–792 were read for context only.
Its intervening sections were not read. File-name listings were used to
locate instructions and check ownership; no listed archived report was opened.

SHA-256 identities of the six fully read inputs:

    dc826260f9df986dd899270772d05443d6e3a3b6db521921969ccf1c370cc094  AGENTS.md
    a1491eabfb67a9df1eb76ed5eb689c5165173ae995c859baa3d8b5f3436a46e1  RESEARCH_LOOP.md
    f876857552ad487b9a2d8036292443760240a7f52f65ec7c28b32a855760730f  RESEARCH_TEAM.md
    b91bb2101c18e59706959612683e9b8c18b7bbdafe02bddfce7abbf705c3344f  README.md
    257511f8150bdeea977c38e3a83c6751d000fb7070eb13d12d50e0c94d008fb7  docs/SPECIFICATION.md
    6d4082370c1796afb35563134ef64de6417f5ba205eeee8a55e077e5f033ab56  Norm2-shallit-source-note.md

Primary-source scope (retrieved 2026-10-08):

- **[PT]** Publisher PDF linked in section 7: §§1–4, pp. 1–13, including
  the amended trial and Lemmas 1–5; pp. 14–16 were returned and skimmed
  for scope and bibliography. Earlier sources cited inside it were not
  independently audited. This is a sourced published algorithm bound,
  not a new verification of every analytic input.
- **[CP]** Boyd Coan and Cherng-tiao Perng,
  [*Factorization of Hurwitz Quaternions*, International Mathematical
  Forum 7 (2012), 2143–2156](https://www.m-hikari.com/imf/imf-2012/41-44-2012/perngIMF41-44-2012.pdf):
  focused reading of §2, Proposition 2.3/Corollary 2.4, §3 Lemma 3.1,
  and §4 Definition 4.1 (pp. 2144–2147, 2149). Extraction additionally
  returned material through p. 2152; no result from that later material
  is needed for this review.
- Discovery-only: Pollack's current author/research pages, Voight's book
  landing page, and Wang–Deng's [arXiv:2205.00642 abstract](https://arxiv.org/abs/2205.00642).
  The Wang–Deng full text was not read or used as a complexity guarantee.
  Web search snippets, including the older Voight book excerpt, were
  leads only. Voight's two current PDF links returned internal errors;
  no unavailable book text is credited as checked.

The old Pollack PDF URL redirected to his new homepage; the publisher PDF
above succeeded. The failed Shallit TR85-001 and Wiley endpoints noted in
the supplied source limitation were not retried. Source retrieval, file
reading/hashing, and report writing are the only execution in this task.
