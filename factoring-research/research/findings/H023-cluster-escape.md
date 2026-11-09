# H023 — A clustered ordinary-base family and its special-form NFS scope

2026-10-08. **Finite geometry and population mathematics accepted after
independent review; optimized constants accepted only as conditional real
relaxations.** Original reviewed bytes are preserved in
[H023-submitted-draft.md](H023-submitted-draft.md), SHA256
`c025d0e2c52ad9deb9540a8514cd170c2779e18e02cd60838b65a65b1974eeb3`.
See [review](H023-independent-review.md) and [disposition](H023-disposition.md).

**Reviewed disposition:** retain the geometry counterexample and exact primitive
population construction; reject promotion to a new factoring algorithm or a
verified complexity improvement. The stated rectangular relaxation has infimum
`C^3=16/3`, but its mechanism is ordinary translated, skewed NFS on a sparse
special family. There are additional special-form representations even with
independent M. **Verified full factoring complexity improvement: NONE.**

The derivation below proves more than square-freeness within its stated finite
range: the proposed f is irreducible. It also gives an actual population violating
the H022 count if its separation hypothesis is deleted. Neither assertion
contradicts the accepted conditional H020/H022 results.

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, the full H023 preregistration, H020's
disposition and normalization, H022 Sections 1–4 and its review scope, and H016's
processing disposition. Historical pending-review text does not supersede the
completed dispositions. No prior proof is reproduced as new work here.

## 1. Primary literature and baseline classification

The following primary sources were consulted online on 2026-10-08. The
representations specific to this family in Section 8 are my symbolic deductions,
not results attributed to these authors. Search scope included special/general
NFS, skewed polynomial shape, semi-special/semispecial terminology, and
multivariate/nonlinear representations; this was a bounded comparison, not an
exhaustive literature or priority search.

- Lenstra–Lenstra–Manasse–Pollard, *The number field sieve*, Sections 1–3:
  special-form polynomial selection, the rational/algebraic relation pair, and
  the heuristic special-NFS constant `(32/9)^(1/3)` are established prior art.
  Their treatment explicitly distinguishes this heuristic analysis from a
  proved running time. [Primary paper](https://wstein.org/129/references/Lenstra-Lenstra-Manasse-Pollard-The%20number%20field%20sieve.pdf).
- Murphy, *Polynomial Selection for the Number Field Sieve Integer
  Factorisation Algorithm* (1999), especially Sections 5.1–5.2: selecting
  polynomials by coefficient shape and using rectangular regions of unequal
  side lengths is established NFS methodology. A large unweighted coefficient
  maximum does not by itself determine the norm sizes in an appropriate
  rectangle. [Primary thesis](https://maths-people.anu.edu.au/~brent/pd/Murphy-thesis.pdf).
- Kleinjung, *Polynomial selection for the number field sieve*, Sections
  6.3, 6.5–6.7: skewness, translations, and adding a polynomial multiple of
  the other polynomial belong to the standard selection framework. Its
  discussion also separates special polynomial pairs from pairs available for
  general integers. This is the relevant baseline for shifting X to Y−1 and
  for the rotation in Section 8. [Primary chapter](https://www.joppebos.com/montgomery/book_ch6.pdf).
- Coxon, *On nonlinear polynomial selection for the number field sieve*:
  nonlinear polynomial pairs and modular geometric-progression/lattice
  constructions are also existing alternatives. A bivariate expression with
  small coefficients does not automatically supply a small univariate
  number-field pair. This report supplies no exclusion theorem for those
  alternatives. [Primary research paper](https://arxiv.org/abs/1109.6398).
- Coppersmith's multiple-polynomial modification is a different relation
  architecture. The conventional GNFS cube `64/9` is not the best cited
  multiple-polynomial constant cubed; Lee–Venkatesan give the smaller cube
  `(92+26 sqrt(13))/27` and distinguish square congruences from proper
  factoring. Neither work supplies a smoothness theorem for this fixed family.
  [Coppersmith's primary research record](https://research.ibm.com/publications/modifications-to-the-number-field-sieve),
  [Lee–Venkatesan, optimization and Remark 4.31](https://arxiv.org/html/1805.08873v1).

Thus “semispecial” or “shape advantage” would only be descriptive labels here.
The construction is already within the known special-form/skewed NFS framework.
No novelty claim follows from beating an isotropic gamma=1 calculation. The
search and explicit comparisons below do not prove that the best existing
special-family construction has been exhausted.

## 2. An exact finite family, ordinary digits, and recognition

Use the following convenient sufficient finite conditions throughout:

    d >= 4 even,  k=d−2,
    m >= 2^(d+7) even,
    M odd,  m/2^(d+3) <= M <= m/2^(d+2).

M is chosen independently anywhere in this interval; no quotient/remainder
relation between m and M is imposed. In particular M>16. Put

    f(X)=(X+1)^k (X²+M+1)+1,
    N=f(m),  q=m+1,
    G(Y)=f(Y−1)=Y^d−2Y^(d−1)+(M+2)Y^k+1.

With binomial coefficients outside `[0,k]` defined to be zero, the coefficient
of X^j in f is exactly

    a_j = binom(k,j−2)+(M+1)binom(k,j)+[j=0].       (2.1)

All are nonnegative and a_d=1. For every j,

    a_j <= (M+2)2^k+1
        <= m/16+2^(d−1)+1 < m.                   (2.2)

The last strict inequality follows already from the displayed finite m bound.
Thus these coefficients are legal ordinary base-m digits, including the leading
one, with no carries. Also

    N > m^d,
    (m+1)^d−N = (m+1)^k(2m−M)−1 > 0.             (2.3)

Consequently `m=floor(N^(1/d))`, the actual degree is d, and f is precisely
the ordinary nonnegative base-m polynomial of N. Since m is even and M odd,
N is odd.

For a supplied trial degree d, recover

    m=floor(N^(1/d)),
    Q=(N−1)/(m+1)^(d−2),
    M=Q−m²−1,                                    (2.4)

rejecting a nonintegral division or any failed finite/parity/interval condition.
Verify f(m)=N and, if desired, the digits directly. This is exact recognition
using N and d alone; it needs neither a factor of N nor a factorization of N−1.

The degree is not advice: an N-only recognizer can try all even d from 4 to
`n=bit_length(N)`. There are O(n) trials. Integer root by binary search and
integer powers/divisions have polynomially bounded iteration counts and bit
widths; even an unreduced trial power with d<=n has O(n²) bits. Computing
2^(d+7), binomial coefficients, and the final identities is polynomial bit work.
Abort powers above a comparison bound if useful, but no fast-power oracle is
needed. This proves polynomial recognition of this family, not representation
of arbitrary N. Asymptotic optimization over d does not assert that one fixed
input has all the required degree representations.

Let A be the actual coefficient maximum of f. From (2.1)–(2.2),

    M+2 <= A < m,
    log m−(d+3)log 2 <= log A <= log m.            (2.5)

Write, as in H022,

    t=log N, D=t^(1/3)(log t)^(2/3),
    V=t^(2/3)(log t)^(1/3),
    d=(delta+o(1))(t/log t)^(1/3),  delta>0 fixed.

Equation (2.3) gives `t=d log m+O(d/m)`. Therefore

    log m=(1/delta+o(1))V,
    log M=log m+O(d)=(1/delta+o(1))V,
    log A=(1/delta+o(1))V.                         (2.6)

Here d=o(log m) and d=o(V). The actual ordinary-base height parameter is
**gamma=1**, despite the clustered roots. These are not arbitrary coefficients
whose height has merely been replaced by the upper bound m.

Such scale sequences exist: let even d grow and choose even m with
`log m ~ 3 d² log d / delta³`, then any allowed odd M. The resulting t has the
required degree scale. All finite bounds eventually hold. This existence
statement is distinct from selecting a representation on every input.

## 3. Strict root counts, irreducibility, and actual separation

Set `r=(2/M)^(1/k)`. Then 0<r<1. On the circle |Y|=r,

    |M Y^k|=2,
    |G(Y)−M Y^k|
       <= 1+r^k(r²+2r+2)
       < 1+10/M < 2.                             (3.1)

Rouche's theorem therefore puts exactly k roots, counted with multiplicity,
strictly inside |Y|<r. There are no roots on that circle. On |Y|=1, separately,

    |(M+2)Y^k|=M+2>4
       >= |Y^(k+2)−2Y^(k+1)+1|.                 (3.2)

Thus exactly k roots are strictly inside the unit disk and exactly two strictly
outside it, with none on its boundary. Combining the counts, all k inside
roots lie in the smaller disk; there are no intervening roots.

For real Y,

    G(Y)=Y^k((Y−1)²+M+1)+1 > 0,                  (3.3)

because k is even. The two roots outside the unit disk consequently form one
nonreal conjugate pair.

**Irreducibility argument.** If monic G factored nontrivially over Q, Gauss's
lemma would give monic nonconstant integer factors. A factor containing one
outside root must contain its conjugate. At least one other factor would then
have all roots strictly inside the unit disk. Its nonzero integer constant
term would have absolute value equal to a product of numbers strictly less
than one, an impossibility. Since G(0)=1, a zero constant term is excluded.
Hence G, and its integral translate f, are irreducible over Q. Characteristic
zero then gives square-freeness. This is a proof within the stated range, not
an assumption that a sparse polynomial is generically irreducible. There is
no exceptional-M search or discarded-M cost in this construction.

For the k cluster roots alpha_i of f, `|alpha_i+1|<r`. In the exact H020
normalization put

    R_i=max(1,|alpha_i|),
    Delta_ij=|alpha_i−alpha_j|/(R_i R_j),
    kappa_J=(1/2)min_(i!=j in J) Delta_ij.

Every cluster root has |alpha_i|<2. For any H>=1 it cannot be in a selected
large-root set requiring `|alpha_i|>=2H+2`. Hence every permitted complement
J contains all k cluster roots. There are at least two, and for any pair of
them `Delta_ij<2r`, since R_i R_j>=1. In particular

    0<kappa_J<r,
    log(1/kappa_J) > log(M/2)/(d−2)
                   =(delta^(−2)+o(1))D.           (3.4)

This bounds the **true separation from above**, rather than showing that a
particular disk certificate is poor. No positive certified lower bound on
kappa_J can satisfy H020/H022's `log(1/kappa)=o(D)` on these sequences. Choosing
a different eligible large-root subset does not remove the cluster. It is
therefore a concrete failure of an all-input separation premise, already for
irreducible ordinary-base polynomials with actual gamma=1.

## 4. Exact resultants and a population that can actually be generated

For positive integers x,z let `y=x+z`. Then

    g(X)=xX+y=xY+z,  gcd(x,y)=gcd(x,z).

Use the convention `Res(P,Q)=lc(P)^deg(Q) product_(P(alpha)=0)Q(alpha)`.
Monicity gives

    Res(G,xY+z)=(-1)^d x^d G(−z/x).

For even d this is exactly

    Q(x,z)=z^d+2xz^(d−1)+(M+2)x²z^(d−2)+x^d.     (4.1)

An integral translation preserves this resultant, so it is also Res(f,g).
Swapping the two resultant arguments multiplies by `(-1)^d=1` in this case.
All four terms are positive; in particular there are no zero norms here.
The rational value is

    R(x,z)=g(m)=qx+z > 0.                          (4.2)

Let fixed constants satisfy a>=c>0 and set

    U=floor(exp(aD)), Z=floor(exp(cD)),
    1<=x<=U, 1<=z<=Z, gcd(x,z)=1.                 (4.3)

These are distinct sign-normalized primitive linears. For U>=Z the elementary
Mobius inversion count is

    sum_(j<=Z) mu(j) floor(U/j) floor(Z/j)
      = UZ/zeta(2)+O((U+Z)log(2Z)+U).             (4.4)

Indeed expansion of the floors costs O((U+Z)sum_(j<=Z)1/j+Z), and the tail
of sum mu(j)/j² costs O(UZ/Z)=O(U). This error is o(UZ) as Z grows
exponentially in D. Thus the actual primitive population is

    exp((a+c+o(1))D).                              (4.5)

The upper-edge rectangle `U/2<x<=U, Z/2<z<=Z` has, by subtraction of four
prefix counts,

    UZ/(4 zeta(2))+O((U+Z)log(2Z)+U)               (4.6)

primitive members. It has the same positive exponent. Floors and strict/closed
interval endpoints alter only the stated errors.

Scanning the raw rectangle and applying Euclid's algorithm generates every
member in `UZ poly(n)` bit work. Rejected nonprimitive pairs are paid for;
their positive-density rejection changes no leading exponent. Computing (4.1)
and (4.2) takes polynomial bit work per raw pair: log x, log z, d, log M,
and the norm widths are all polynomial in n. Enumeration is neither an
upper-count oracle nor a smoothness filter.

## 5. Uniform norm bounds, actual norm strata, and a sharper obstruction

Uniformly on the full rectangle,

    q+1 <= R(x,z) <= qU+Z,
    log R(x,z)=(1/delta+o(1))V.                    (5.1)

Here log U, log Z=O(D)=o(V); no assumption about typical x is needed.
Taking the maximum of the four terms of (4.1) gives

    log Q(x,z) <= (beta+o(1))V,
    beta=max(a delta, 1/delta+c delta).            (5.2)

The omitted terms have coefficients c delta; the factor x² in the M term
has logarithm O(D), not a further leading V contribution. The x^d term has
coefficient a delta and **cannot** be omitted.

These are uniform upper bounds, not a full-box common smoothness law. For
example x=z=1 gives Q=M+6 with coefficient 1/delta, generally smaller than
beta. On the upper-edge rectangle of (4.6), however,

    log x=aD+O(1), log z=cD+O(1),
    log Q(x,z)=(beta+o(1))V                         (5.3)

uniformly: use both positive lower terms x^d and `(M+2)x²z^(d−2)` and
the upper bound (5.2). Errors such as d log 2 and O(D) are o(V). This supplies
a population of the asserted exponent in one actual leading norm stratum.
It still says nothing about its smoothness or useful relation density.

There is even a direct population counterexample to **deleting** H022's
geometry condition. Fix a>delta^(−2), take U as before, and now choose Z as
the largest integer with

    (M+2) Z^(d−2) <= U^(d−2).

Then `log Z=(a−delta^(−2)+o(1))D`; put H=U+Z. Every pair in the rectangle
has x<=H, y=x+z<=H and

    Q(x,z)<=5U^d.                                 (5.4)

The binomial maximum also gives the stronger finite coefficient estimate

    A >= (M+1)2^(d−2)/(d−1) >= m/[32(d−1)].

Using `N^(1/d)<m+1` and m>=1,

    (2H)^d(d+1)A N^(−1/d) >= (2^d/64)U^d.

For even d>=10 this is larger than 5U^d. Hence all primitive pairs satisfy
H022's **exact** threshold with its parameter Q_threshold=1, not just a
leading-exponent approximation.

Choose `a delta²=2`. Then c=a−delta^(−2)=a/2, so the actual admitted
population exponent is 3a/2. The H022 expression at gamma=1,
`z_H022=a delta²=2`, `Q_threshold=1`, would give `a F_1(2,1)=a`.
This strict discrepancy refutes the geometry-free version of that upper count.
The separation condition is precisely what fails, by (3.4); the accepted
conditional theorem is unaffected. This example uses no smoothness hypothesis.

## 6. Complete optimization of the stated rectangular relaxation

Write `u=a+c` and let `B=exp((b+o(1))D)`, b>0. The rational plus algebraic
norm-size coefficient on the edge rectangle is

    W=1/delta+max((u−c)delta, 1/delta+c delta).     (6.1)

The following is an additional **heuristic relaxation**, not a consequence of
Sections 2–5. Suppose these actual primitive edge candidates, under the sampling
or scan law used, produce usable doubly smooth data with exponential rate
`exp((-W/(3b)+o(1))D)`. For a positive factoring claim one needs a sufficient
lower-yield/concentration statement after all exclusions, not merely an upper
expected yield. Suppose also the conventional collection obligation is
`exp((b+o(1))D)` and the later matrix charge is `exp((2b+o(1))D)`.

The displayed full-scan real inequalities are then

    u >= b+W/(3b),   C>=u,   C>=2b.                (6.2)

This only models collection and those work charges. At equality it does not
give concentration, enough independent square information, or a proper factor.

To optimize, hold u>0 and delta>0 fixed, with `0<c<=u/2`.
The two arguments of the maximum cross at

    c0=(u−delta^(−2))/2.

If `u delta²>1`, this is an admissible interior minimum, and

    min_c W = u delta/2+3/(2delta).               (6.3)

Moving c to either side only increases the active linear branch. If
`u delta²<=1`, c0<=0 and the minimum over the closure is instead at c=0,

    inf_c W=2/delta >=2 sqrt(u).                  (6.4)

In the first regime, arithmetic–geometric mean gives

    u delta/2+3/(2delta) >= sqrt(3u),

with equality at `delta²=3/u`, which is inside that regime. The second
regime is strictly worse. Thus the global minimum is exactly sqrt(3u), with

    a=2u/3, c=u/3, delta²=3/u.                    (6.5)

The collection inequality requires b<u and

    sqrt(3u) <= W <= 3b(u−b) <= 3u²/4.

Squaring positive quantities and dividing by u gives

    u³>=16/3,  C>=u>0.                            (6.6)

This bound is attained in the real relaxation by

    u0=(16/3)^(1/3), b=u0/2,
    a=2u0/3, c=u0/3, delta²=3/u0, C=u0.           (6.7)

The corresponding exact-balance rectangles of Section 5 have the same
leading parameters and population, if exact rather than asymptotic term
balancing is desired. For u>u0 the analogous assignments give collection
slack in the relaxation.

This checks the unbalanced and boundary regimes, rather than presuming balance:
`a=c=u/2` has min W=2 sqrt(u), hence cube at least 64/9; the closure c=0
has `W=1/delta+max(u delta,1/delta)` with the same minimum 2 sqrt(u).
At fixed positive u, delta tending to zero or infinity cannot improve the
minimum, and b tending to zero or b>=u cannot satisfy collection. c=0 itself
would be a single z strip, not the two-growing-side count (4.4); its limiting
norm calculation still cannot improve (6.6). No negative-coordinate cancellation,
different smoothness bounds, multiple fields, or growing/unbounded parameters
are silently included in this optimization.

If only exp(vD) distinct members of one such edge rectangle are processed,
v<=u, the same fixed-stratum yield law would require
`v>=b+W/(3b)`. Since `W>=sqrt(3u)>=sqrt(3v)`, it still implies v³>=16/3.
This observation assumes that law remains valid for the chosen subset; it
does not cover an adaptive selector with a better conditional yield.

The optimized constant is below the conventional gamma=1 isotropic model,
and above the usual negligible-coefficient SNFS constant. These comparisons
of real relaxations do not establish a new algorithmic gain.

## 7. What is paid and what remains unproved

Recognition, the exact identities, primitive enumeration, and norm evaluation
are costed above. For `S=exp((u+o(1))D)` raw candidates, the accepted
[H016 processing disposition](H016-disposition.md) supplies an integer
prime-exponent recovery construction costing `(B+S) poly(n)` when its
polynomial bit-width and payload conditions hold. They hold for the integer
values here. Invoking this construction does not invoke a distribution theorem.
Naive independent trial division by every prime instead incurs S*B and would
spoil the stated envelope. No implementation of either is supplied or run here.

There is an actual field `K=Q(beta)`, G(beta)=0, of degree d, and beta is
integral. The order map `Z[beta] -> Z/NZ`, beta -> q, exists because G(q)=N.
For a primitive pair and a prime p dividing Q(x,z), p cannot divide x: otherwise
Q is congruent to z^d modulo p. At a good prime `p not dividing disc(G)`, the
root `−z/x mod p` uniquely labels the degree-one ideal containing x beta+z;
its valuation agrees with the p-valuation of the norm. This gives the linear
version of the good-prime labeling step. Prime/root-table construction, table
access, and valuation recovery still have to be paid; expected polynomial
finite-field preprocessing per prime is compatible with exponent max(b,u).
The deterministic B²-style preprocessing allowance is compatible with the
modeled max(u,2b), too.

The discriminant is a computable nonzero integer of polynomial bit length.
Testing `gcd(Q,disc(G))=1` is polynomial work per candidate and needs no
factorization of the discriminant. But excluding the other pairs has an
unproved supply cost. The desired yield hypothesis must concern the population
after that exclusion, or a correctly costed treatment of bad primes. Smoothness
of the integer norm alone is not an ideal-parity certificate at bad primes.
For example 2 divides disc(G), since its reduction modulo 2 is a square;
nevertheless (4.1) is odd for every primitive x,z. This one local fact does not
control all the bad primes or the joint smoothness distribution.

The remaining logical and cost obligations are substantial:

1. **Actual useful yield.** A Dickman-type size substitution is only a model
   for these correlated polynomial values. It supplies neither a uniform lower
   count nor a success probability. All coprimality, bad-prime, duplicate,
   character, and selection conditions must be included in the asserted law.
   No full-box law is inherited from (5.2), and no adaptive law is inherited
   from an average on (5.3).
2. **Units and ideal squares.** Norm-square parity does not imply that the
   algebraic element is a square. The field is totally imaginary, with unit
   rank d/2−1: there are no real-embedding sign columns, but units, torsion and
   ideal-class square obstructions do not disappear. Correct ideal columns
   and sufficient character information must be constructed, not simply
   postulated as supplied labels. R is positive, so its rational sign causes
   no additional column for these candidates.
3. **Dependencies and rank.** More correct rows than columns supplies a linear
   dependency. Distinct primitive pairs do not prove useful independence of
   the resulting square information or productive dependencies. A sparse
   matrix of factor-base size B times polynomial factors motivates the 2b
   charge; that model is not a theorem that these rows deliver what is needed.
4. **Square roots and reduction.** Reconstruct an algebraic square root with
   charged coefficient growth, precision, storage and denominator handling.
   The order map alone does not make every element of K reducible modulo N.
   Denominators require invertibility or a checked gcd branch. Ordinary NFS
   square-root methods are relevant prior art, but no family-uniform bound
   fitting C=u0 is proved here.
5. **Proper gcd and restarts.** Even a valid A²=B² modulo N can have
   gcd(A−B,N) in {1,N}. A lower bound on proper-splitting probability and the
   costs of failed dependencies/restarts remain necessary. Prime inputs lie
   outside the composite promise; no balanced-semiprime or hard-instance
   promise is supplied. Finding an incidental small factor is not evidence
   for the proposed L-constant.

Accordingly Sections 4–6 give an attained **candidate population** and an
optimized **conditional collection relaxation**, not attained smooth supply or
a complete conditional factoring theorem with all sufficient hypotheses proved.

## 8. Stronger baseline tests and representation traps

### 8.1 Tying M to m would change the problem

Suppose, outside the independent-parameter construction, one imposed
`M=floor(m/s)` with `s=2^(d+O(1))` and `m=sM+r0`, 0<=r0<s. Then

    P(X)=(X+1)^k(sX²+X+s−r0)+s,
    P(m)=sN.                                      (8.1)

The coefficients have logarithmic height O(d), negligible on the V scale;
the leading coefficient need not be one for NFS. This is the familiar
small-coefficient special-form route, subject to the usual field selection and
factoring obligations. Choosing s=2^d illustrates the trap in the brief;
shifting its exponent by a fixed amount gives variants matching the proposed
M interval. Such a construction cannot support a new gamma=1 algorithm claim.

For independent M one can still write `s=floor(m/M)`, `r0=m−sM`, but now
only 0<=r0<M is guaranteed. There are permitted pairs with r0 comparable
to M. Then the height of (8.1) has logarithm of order log m, so the negligible
coefficient conclusion does not follow. Independently chosen does not mean
that every individual pair lacks an accidental better representation; the
recognizer should retain such possibilities. Nor is failure of this one
substitution a lower bound on all polynomial selection.

### 8.2 The same independent family has a degree-halved representation

Let h=d/2 and K0=2m−M>2. Directly,

    H(T)=T^h−K0 T^(h−1)+1,
    H(q²)=N.                                      (8.2)

Indeed `K0=2q−(M+2)`. At the polynomial level,

    H(Y²)=G(Y)+2Y^(d−2)(Y−q).                     (8.3)

Thus this is precisely a rotation by the rational polynomial Y−q followed by
grouping even powers. It works for **every** permitted independent M.
It is an explicit reason to compare against shape-aware special-form selection,
not merely generic ordinary-base f.

H is also irreducible: on |T|=1 its middle term has modulus K0>2, strictly
larger than |T^h+1|. Exactly h−1 roots lie inside the unit disk and one outside;
a nontrivial monic integer factorization would again have a factor entirely
inside, contradicting its nonzero constant term. There are no boundary roots.

The new base q² has leading log size 2V/delta, and H's coefficient maximum
has logarithm V/delta. Thus its coefficient height relative to its own degree
scale `delta_H=delta/2` has gamma_H=1/2. H is a valid NFS polynomial, although
it is not the nonnegative ordinary expansion at floor(N^(1/h)).

Even an isotropic rectangle for this pair gives, with total population exponent
u, combined norm coefficient `W_H=3/delta+u delta/4`. Optimizing this expression
over the family degree scale gives min W_H=sqrt(3u) at delta²=12/u, reproducing
the cube 16/3 of Section 6 by a different conventional special representation.
For this assertion the middle term dominates uniformly on a positive upper-edge
rectangle: K0 exceeds all fixed-ratio edge losses exp(O(h)), since log K0~V/delta.

There is a stronger **model-only** comparison on the subfamily d divisible
by 4, so h is even. Its exact positive resultant is

    Res(H,xT+z)=z^h+K0 x z^(h−1)+x^h.

For a>=c>0 its leading coefficient is
`max(a delta/2,1/delta+c delta/2)`. The same balanced-shape minimization gives

    W_H=u delta/4+5/(2delta),
    delta²=10/u, a=3u/5, c=2u/5,
    min W_H=sqrt(5u/2).

With the same collection and matrix relaxation, this yields cube 40/9, smaller
than 16/3. The positive terms and upper-edge primitive count justify the norm
and candidate-population statements; the smoothness and factoring objections
are unchanged. No new complexity theorem is asserted for H either.

These optimizations use **different optimal delta values**. A fixed input's
original degree is fixed; one cannot compare the two globally optimized
constants as if the degree-halved construction uniformly beat G at G's own
optimizer. More precisely, when u delta²>2 both balanced shapes are admissible,
and at the same u and delta their difference is
`W_H−W_G=(4−u delta²)/(4delta)`. Thus H is better in this comparison when
u delta²>4, whereas G's optimizer has u delta²=3. Conversely, an alleged
new special-family record based only on
the globally optimized 16/3 would omit this readily available comparator.
For d=2 modulo 4 the exact signs for H differ and cancellation needs separate
care; the stronger positive-term claim here is expressly restricted to d=0
modulo 4. No such restriction was needed for the original G result.

### 8.3 The known factorization of N−1 and multivariate descriptions

There is the exact publicly recoverable identity

    N−1=q^k A0,  A0=m²+M+1.                       (8.4)

This is not a supplied **prime** factorization: q and A0 themselves need not
be factored. It identifies extra special structure that a matched baseline
must use. For any s dividing k, set ell=k/s. Besides the nonmonic binomial
`A0 T^ell+1` evaluated at q^s, the monic pair

    F_s(T)=T^ell+A0,   L_s(T)=q^s T−1

has `Res(F_s,L_s)=(-1)^ell N`. Here q is invertible
modulo N, since N is congruent to 1 modulo q. These are ordinary binomial
NFS candidates with log coefficient height `~2V/delta` and rational coefficient
height `~sV/delta` for fixed s; neither height is free. Their field factors and relation
architecture must be treated if used. Grouping powers, and any further useful
factorizations of q or A0, belong in a special-family baseline. This report
does not assert they uniformly dominate (4.1), or optimize all divisors s.

The small-coefficient bivariate description

    P(U,V)=(U+1)^k(U²+V+1)+1,  N=P(m,M)

is likewise real structure, but two evaluation parameters each have logarithm
of order V. Eliminating V by V−M reintroduces the large coefficient. A different
elimination, nonlinear pair, or tower construction must specify its fields,
norms, relation space, and costs; merely calling this multivariate SNFS does
not assign the negligible-coefficient constant. The primary nonlinear-selection
literature above was checked for this baseline distinction; no cited theorem
was found that automatically grants a stronger full factoring bound for all
these independent parameters. This is a limited literature/comparison result,
not a proof that no such construction exists.

Finally, a factorization of N−1 is not a factorization of N. Smoothness of
N−1 does not assert smoothness of p−1 for an unknown prime divisor p of N.
Any primality or splitting method using extra factorization information must
charge obtaining it and state its own hypotheses. No such method is proved
fast merely by (8.4).

## 9. Sparsity, exact scope, and the next decisive action

For fixed d and large B, taking even m in [B,2B] gives Theta(B) possible m,
and each has Theta(m/2^d) permitted odd M. The total is Theta(B²/2^d).
There are no collisions at that fixed d: recover m by (2.3), then M by (2.4).
All these inputs lie between B^d and (2B+1)^d. Equivalently, in the range
where T^(1/d) is much larger than 2^(d+7), the number of members <=T at that
fixed trial degree is Theta(2^(−d)T^(2/d)), with absolute constant-factor
bounds uniform in that regime. For the upper bound use m<=T^(1/d); for the
lower bound use all even m<=floor(T^(1/d))−1, for which (2.3) suffices.
For each m the number of allowed odd M is m/2^(d+4)+O(1). Summing over even
m proves the claim; the rounding error O(T^(1/d)) and the excluded prefix
m<2^(d+7) are negligible under the displayed condition.

At the usual degree scale, the logarithm of this count is
`2t/d−d log 2+O(1)`, subject to that prefix condition; the fraction among
integers up to exp(t) is `exp(−t+2t/d−d log 2+O(1))`. In particular it is
`N^(−1+o(1))`, not a positive fraction of all inputs. A polynomial number of
degrees in a fixed positive compact degree-scale range still gives only
exp(O(V)) recognized inputs up to exp(t). Counting all such generated inputs
does not count balanced semiprimes.

There are explicit composite subsequences if the geometric counterexample is
required inside the composite-input promise: choose m=0 modulo 6 and M=1
modulo 6 within the same interval. Then N=0 modulo 3. These congruences permit
arbitrarily large independent choices and the prescribed degree scale. Such
examples are easy composites, which is entirely adequate to disprove uniform
geometry and entirely inadequate to establish hard-family factoring progress.
There is no assertion of infinitely many balanced semiprimes in the family.

The narrow claims accepted by independent review are:

1. The exact ordinary-base, recognition, actual-height and irreducibility
   construction in Sections 2–3, with genuine normalized separation failure.
2. The exact resultant, primitive lower population, uniform edge norm stratum,
   and geometry-free H022 counterexample in Sections 4–5.
3. The infimum 16/3 of the stated conditional rectangular relaxation, including
   its boundary scope, and the exact alternative representation identities in
   Section 8. None is a smoothness or factoring theorem.

Independent symbolic review accepted these finite inequalities and scope
statements, including irreducibility, the exact Q_threshold=1 population and
the degree-halved comparator. The geometric counterexample is retained;
this relation architecture is classified against established special-form
NFS. The [parent binomial comparison](H023-intake.md) also passed review as a
conditional model calculation. No useful-yield experiment is justified as a
novelty test without a further specific claim that survives comparison on
the same inputs and available representations. Reopen only for a concrete
new primitive or a stated useful-yield/extraction mechanism with paid costs.

No experiment, root sample, parameter sweep, executable code, benchmark,
package, Lean change, recursive delegation, commit, publication, or scheduler
was used. This report is the sole owned output. Shared code, STATE, registries,
hypotheses, and prior evidence were not edited. No shared-code test or build
was run for this analytic document.

**Verified full factoring complexity improvement remains NONE.**
