# H020 — Primitive linear tails with a discrete weighted count

2026-10-08. **New informal derivation; independent review required.**
Disposition: a computably conditional supply obstruction for the accepted
H018 witness; the ordinary-base all-input geometry question remains open.
**Verified factoring complexity improvement: NONE.** No novelty claim.

Keeping the leading coefficient in the large-root estimate repairs the main
loss in a direct linear analogue of H017. Outside at most one primitive
linear per remaining root, the accepted pairs satisfy a weighted inequality
in their leading coefficient x and actual height h. An exact dyadic count
of that region, rather than its continuous volume, gives

    limsup log(max(1,S_prim))/D <= 9/5

at the H018 parameters, provided the certified normalized pair separation
on the remaining roots has log(1/kappa)=o(D). This permits the full large-root
fraction allowed by the ordinary-base coefficient bound, 25/49; an extra
o(d)-large-roots assumption is unnecessary. The exponent 9/5 is strictly
below the unchanged modeled attempt requirement 15101/7980, by 737/7980.

This is slightly weaker than H018's conjectured 88/49 count, which remains
unproved in its original scope. The theorem here counts normalized primitive
linears under explicit root conditions. It neither assumes that conjecture
nor supplies smoothness or a factoring lower bound. A weaker quantitative
separation condition also suffices; see Section 5.

## 1. Inputs, accepted background, and scope

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, the H020 question, the complete corrected
H018 report and its independent review, the complete H017 report and its
independent review, and W001 Card C/shared accounting. Historical pending
review descriptions in STATE do not supersede the completed reviews.

H014's exact enumerator, H017's conditional quadratic count, and corrected
H018's model/enumeration analysis are accepted informal background. This
report does not rerun or review their implementations. H019's frozen quadratic
certificate experiment and H016's processing review are separate.

Fix N>1, an integer H>=1, and a monic square-free integral f of actual degree
d>1 and coefficient height A>=1. The intended f is the ordinary nonnegative
base-m expansion of N, with m=floor(N^(1/d)); check m>=2, actual degree d,
leading coefficient one, and f(m)=N. The counting proof applies more broadly
to monic square-free f; only its ordinary-base specialization uses A<=m.
Irreducibility is not needed for the count and is not certified by it.

The population of interest is

    g=xX+y,  1<=x<=H,  |y|<=H,  gcd(x,y)=1,
    g(m)!=0,  Res(f,g)!=0,
    |Res(f,g)|^(5d) N <= C0^(5d),
    C0=(2H)^d(d+1)A.                                      (1)

Positive x fixes sign associates. Write h=max(x,|y|). Let S_prim denote the
number of these distinct polynomials, not visits to them or ideal rows.
For proof only, set T=C0 N^(-1/(5d)), the unfloored real cutoff. Integer
acceptance is exactly |Res|<=floor(T); (1) is its exact implementation.

The proof below bounds a superset also allowing zero rational values and
zero resultants. Removing either cannot increase the bound. Neither zero
quantity is subsequently treated as a smooth nonzero norm.

## 2. Two evaluation rows and one primitive exception per root

Let alpha_1,...,alpha_d be all the roots, including both members of every
nonreal conjugate pair. Define

    R_i=max(1,|alpha_i|),  M=product_i R_i,
    E_i(g)=|x alpha_i+y|/R_i,
    Delta_ij=|alpha_i-alpha_j|/(R_i R_j).

Choose any set F of r roots certified to have |alpha_i|>=2H+2, and put
J={1,...,d}\F, k=d-r. Require k>=2. F need not be maximal or invariant
under conjugation. Choose a rational lower bound

    0<kappa<=kappa_J := (1/2) min_(i!=j in J) Delta_ij.      (2)

All root moduli and separations enter through (2) and the certified split;
no bounded-root or random-digit premise is implicit.

**Two-evaluation lemma.** All but at most one E_i, i in J, are >=kappa h.
For a pair i,j, the matrix with rows (alpha_i,1)/R_i has entries of modulus
at most one and determinant magnitude Delta_ij. Every inverse row has
absolute sum at most 2/Delta_ij. Consequently

    h <= 2 max(E_i,E_j)/Delta_ij.

Two values strictly below kappa h would contradict this inequality. Order
the k values and put e=min_(i in J) E_i. Then

    product_(i in J) E_i >= e (kappa h)^(k-1).             (3)

The matrix and its inverse are over C; the argument imposes both real
coordinates when necessary and does not replace a complex evaluation by
its real part. In particular it is valid for nonreal conjugate roots.

**Large-root lemma, retaining x.** For i in F,

    E_i >= x-H/|alpha_i| > x-1/2 >= x/2.                  (4)

This uses x>=1. Replacing the right side by 1/2 would discard the essential
coefficient dependence. Combining (3), (4), and monicity gives

    |Res(f,g)|/M >= 2^(-r) x^r e (kappa h)^(k-1).          (5)

**Primitive uniqueness lemma, with no root-modulus loss.** At any fixed
complex alpha, at most one normalized primitive linear of height <=H has

    |x alpha+y|/max(1,|alpha|) <= 1/(4H).                 (6)

To prove it, let g'=x'X+y' be another and D0=xy'-x'y in Z. If |alpha|<=1,

    D0=x g'(alpha)-x' g(alpha),   |D0|<=1/2.

If |alpha|>=1, use instead

    alpha D0=y' g(alpha)-y g'(alpha),   |D0|<=1/2.

In the second case division by |alpha| cancels exactly the normalization
factor; there is no multiplier |alpha| left over. Thus the integer D0 is
zero. The two coefficient vectors are rationally proportional; primitivity
and positive leading coefficients force equality. This also covers y=0.
It uses absolute complex values throughout.

Let E be the union of the sets in (6) over i in J. Then |E|<=k. Conjugation
may reduce this number, but k suffices. This bound applies to the whole
height-H primitive box, before tail filtering. It does not bound the number
of nonprimitive multiples along these rays.

For comparison with a suggested bounded-root approach, if R=max(1,|alpha|)
and E_alpha<=h/(2R), then |y|<=R(x+E_alpha) implies x>=h/(2R) when
h=|y|; when h=x the same conclusion is automatic. This is a valid
comparability statement, but substituting an unbounded R could lose its
benefit. The weighted count below requires no such modulus assumption.

## 3. Finite cutoffs and an exact integer upper count

Expanding the monic root product bounds each coefficient of f by at most
2^d M. In particular A<=2^d M, so

    T/M <= 4^d(d+1)H^d N^(-1/(5d)).                      (7)

Define the integer and positive real quantities

    C=4 * 2^r * 4^d * (d+1) * H^(d+1),
    W=C * kappa^(-(k-1)) * N^(-1/(5d)).                  (8)

**Weighted containment theorem.** Every admitted primitive g outside E
satisfies

    x^r h^(k-1) < W.                                    (9)

Indeed, outside E all E_i, i in J, exceed 1/(4H). Inserting this strict
inequality and (7) into (5) proves (9). Equivalently, if the reverse weak
inequality holds then some E_i<=1/(4H), and g belongs to E. Equality is
handled safely. No coefficient is assumed typical and no lattice volume
estimate is used.

There is a finite cutoff for each x:

    Y(x)=(W/x^r)^(1/(k-1)).                              (10)

If an admitted primitive g has h>=Y(x), it is in E. There is also the coarser
uniform height cutoff

    Y0=W^(1/(k-1))
      =kappa^(-1)[C N^(-1/(5d))]^(1/(k-1)).              (11)

For any integer h_*>=max(1,Y0), all admitted primitive linears of height
>=h_* are among at most k exceptions. Put Z=min(H,h_*-1). Then

    S_prim <= min(H(2H+1), Z(2Z+1)+k).                   (12)

This is a containing-box bound; it does not assert that every lattice point
in that box is primitive or admitted. The height-dependent (10) gives a
stronger count than (12) when there are many large roots.

### Exact arithmetic, including strict endpoints

Write kappa=p/q with positive integers p,q, and define

    a_exp=5d(k-1),    b_exp=5dr,
    V=q^a_exp C^(5d),    U=N p^a_exp.                    (13)

Here U,V are integers, unrelated to root moduli or smoothness bounds.
Containment (9) is exactly

    U x^b_exp h^a_exp < V.                              (14)

The uniform-cutoff certificate is the integer predicate

    U h_*^a_exp >= V.                                  (15)

One can find its least positive h_* by integer power comparisons or a
rational ceiling root. No floating logarithms or root approximations decide
(14) or (15).

A sharper finite count needs only O(log(2H)) height bands, not H calls.
For j=0,...,floor(log2 H), set

    L_j=2^j,    Z_j=min(H,2L_j-1).

If r>0, set

    Q_j=floor((V-1)/(U L_j^a_exp)),
    X_j=min(Z_j, iroot_(b_exp)(Q_j)),                    (16)

where iroot_s is the nonnegative integer floor s-th root. If r=0, set
X_j=Z_j when U L_j^a_exp<V, and X_j=0 otherwise. Define

    B_j=X_j(2Z_j+1)-min(X_j,L_j-1)(2L_j-1),
    B_cert=min(H(2H+1), k+sum_j B_j).                    (17)

**Exact finite certificate theorem.** Under the hypotheses above,

    S_prim <= B_cert.                                  (18)

Proof: a nonexception with L_j<=h<=Z_j must satisfy x<=X_j by (14), because
h>=L_j. The integer rectangle 1<=x<=X_j, |y|<=Z_j contains exactly
X_j(2Z_j+1) pairs. Subtract its pairs with h<L_j: there are exactly
min(X_j,L_j-1)(2L_j-1). The result is B_j. These height bands are disjoint.
Their primitive accepted subsets have no larger size. Add the at-most-k
exceptions and cap by the ambient box. In particular, B_cert is an exact
integer *upper bound*, not an algorithm for computing S_prim exactly.

The V-1 in (16) enforces the strict integer inequality without losing a
boundary candidate. Terms with Q_j=0 contribute no pair. Cases H=1,
k=2, r=0, and a resultant cutoff below one cause no definition failure.
When T<1 the specified nonzero-resultant population is empty independently.

Equations (13), (16), (17), together with certified root data, are a rational
N-only supply certificate. One can additionally check B_cert<=K for any
specified integer K by a final exact comparison. A failed desired comparison
or a vacuous bound gives no lower supply conclusion.

For a concrete sufficient endpoint, the additional integer comparison

    B_cert^20 <= H^37                                  (18a)

certifies S_prim<=H^(37/20) on that input. Along a sequence with the witness's
height scaling, passing (18a) gives exponent at most 37/20, strictly below
15101/7980 by 169/3990. Under the lambda=0 hypotheses proved below, (18a)
eventually passes because 9/5<37/20. This is an optional analytic certificate
endpoint, not a frozen test protocol or an executed experiment.

## 4. Growing degree: why the weighted region avoids the large-root loss

Use natural logarithms, t=log N, D=t^(1/3)(log t)^(2/3), and the fixed
H018 witness

    log H=(1+o(1))D,
    d=(7/5+o(1))(t/log t)^(1/3),
    eta=4/5,   b=19/20,   q0=(1/5)/(7/5)^2=5/49.

Assume the certified geometry satisfies, for some fixed lambda>=0,

    log(1/kappa) <= (lambda+o(1))D.                      (19)

Write theta_N=r/d. Every factor in C is explicit, and

    log W/(dD)
      <= 1-q0+(1-theta_N)lambda+o(1).                   (20)

The extra H in C contributes 1/d+o(1) here; the logarithms of 4, 2^r,
4^d and d+1 contribute o(1). Replacing (k-1)/d by 1-theta_N costs o(1).
These errors are uniform for 0<=r<=d-2. In particular no d^(c d) factor
has been suppressed: d log d is order D in this regime, so such a factor
in a final count would have required separate accounting.

For a nonempty band of (17), let

    v=log X_j/D,    z=log Z_j/D.

Then 0<=v<=z<=1+o(1), and the dyadic inequality gives

    theta_N v+(1-theta_N)z
      <= 1-q0+(1-theta_N)lambda+o(1).                   (21)

Replacing L_j by Z_j introduces at most 2^(k-1) before taking the logarithm
and dividing by dD; its contribution is o(1). Also B_j<=3X_j Z_j. There
are only O(log H) bands, whose logarithm is o(D). Thus maximizing v+z in
(21) bounds the count; this is an optimization of a proved discrete bound.

For any limiting theta<=1/2,

    theta v+(1-theta)z >= (v+z)/2,
    v+z <= 2[1-q0+(1-theta)lambda].                     (22)

For theta>=1/2, using z<=1 instead gives

    v+z <= 2-q0/theta+(1-theta)lambda/theta.             (23)

Both can be capped by 2. Subsequences handle a varying theta_N, so no
limiting large-root fraction need exist. At lambda=0 the bound is 88/49
for theta<=1/2, and 2-5/(49 theta) for theta>=1/2.

By comparison, discarding x^r and using only (11) would give the much
weaker height exponent (44/49)/(1-theta)+lambda. Its squared-box exponent
does not close the witness at the allowed ordinary-base large-root fraction.
Keeping x^r changes the count, not merely a constant in that failed bound.

## 5. Ordinary-base specialization and exact margins

For the actual checked ordinary-base construction, A<=m<=N^(1/d).
The reviewed Mahler/l2 bound M<=sqrt(d+1)A, also used in H017, yields

    r log(2H+2) <= log M <= log N/d+(1/2)log(d+1).

Consequently

    limsup r/d <= 25/49.                                (24)

This is an upper bound for any certified subset F, including nonmaximal F.
It does not assume one huge root, independent digits, a distribution of N,
or random f. Multiple huge roots are explicitly allowed. Eventually (24)
leaves k comparable to d, as required by the meaningful specialization.

At lambda=0, (22)--(24) give

    s_prim := limsup log(max(1,S_prim))/D
      <= max(88/49, 2-(5/49)/(25/49)) = 9/5.             (25)

The same leading bound holds for B_cert, so it is supported by a polynomial
size finite certificate rather than a nonconstructive continuum count.
The comparison is exact:

    u_required=15101/7980,
    u_required-9/5=737/7980>0,
    9/5-88/49=1/245>0.                                 (26)

If the stronger restriction limsup r/d<=1/2 is independently checked along
the sequence, lambda=0 gives 88/49 here for the *primitive conditional*
population. This does not prove H018's original all-output homogeneity claim.

For 0<=lambda<5/49, the maximum of (22) on theta<=1/2 is bounded by its
theta=0 value. Expression (23) is increasing in theta in this lambda range.
Thus a convenient uniform quantitative version is

    s_prim <= min(2, max(88/49+2lambda,
                        9/5+(24/25)lambda)).           (27)

Both terms are strictly below u_required if

    lambda < min(5387/111720, 3685/38304)
           = 5387/111720.                              (28)

For example, lambda=0 is not essential. These are strict asymptotic margins;
equality at (28) is not decided by this report. Finite equality in (15) is
safe for its different, explicitly proved purpose. A finite certificate alone
does not prove (19), an asymptotic exponent, or a finite smooth-relation deficit.

**Interpretation.** Under the unchanged H018 selected-tail joint-yield law,
the number of distinct attempts must have exponent at least 15101/7980.
Equations (25), or (27)--(28), contradict that population premise on
sequences satisfying the stated geometry. No smoothness assumption is used
to prove the upper counts. The contradiction uses the modeled yield law;
norm upper bounds alone do not make that law a necessary theorem about
actual smoothness. Conditional rejection of this witness is not an
unconditional factoring-complexity statement.

## 6. N-only construction, verification, and bit costs

The public degree and height algorithms must be fixed and charged. To make
uniform computability entirely explicit, one possible exact rounding with
the witness's asymptotic parameters is the following. Put n=bitlength(N),
ell=bitlength(n), and

    d=max(2, iroot_3(floor(343 n/(125 ell)))),
    e_H=the least nonnegative integer e with e^3>=n ell^2,
    H=2^e_H.                                           (29)

Since n log 2~log N and ell log 2~log log N, these have exactly the required
leading delta=7/5 and height coefficient 1. They use only integers and
polynomial bit work. Equation (29) is an existence/construction detail for
this analytic certificate, not a preregistered experiment or a change to
H019. Other fixed public rounding rules with the same limits also work.

Compute m=iroot_d(N) and its ordinary-base expansion by integer division.
Check the required m, degree, monicity, coefficient, and evaluation predicates,
then gcd(f,f')=1. Integer-root search, exact expansion, and polynomial gcd
have polynomial bit cost in n,d,log A. Failure is a visible failed prerequisite;
do not replace f by its square-free part while retaining d and (1).

For a rational complex disk D_i with center c_i and radius t_i>0, verify
that it contains exactly one root of this same f. The following sufficient
test is fully rational. With exact Gaussian-rational Taylor coefficients
a_ij=f^(j)(c_i)/j!, put

    u_ij=|Re a_ij|+|Im a_ij|,
    l_i1=max(|Re a_i1|,|Im a_i1|),
    l_i1 t_i > u_i0+sum_(j=2)^d u_ij t_i^j.             (30)

Rouche's theorem compares the Taylor linear term with its remainder on the
circle; (30) certifies one root counting multiplicity and none on its boundary.
Also verify pairwise disjointness by

    |c_i-c_j|^2>(t_i+t_j)^2.

d such disks cover every root. This is the same reviewed certificate
principle as H017, with different linear geometry afterward. One may instead
use a reviewed isolator's certified disks/root counts; bare approximate root
locations are insufficient. Failure of the sufficient Taylor test is unknown,
not a proof of no root.

Include i in F only if the exact sufficient inequality

    |c_i|^2>(2H+2+t_i)^2

holds. Unresolved boundary disks stay in J; recompute k and the separation
on that actual J. Define rational bounds

    U_i=max(1, |Re c_i|+|Im c_i|+t_i),
    L_ij=max(0, max(|Re(c_i-c_j)|,|Im(c_i-c_j)|)-t_i-t_j),
    kappa_cert=(1/2) min_(i!=j in J) L_ij/(U_i U_j).      (31)

Here U_i>=R_i and L_ij<=|alpha_i-alpha_j|, so (31) is a sound (2) lower
bound. Require k>=2 and kappa_cert>0. A vanishing sufficient lower distance
requires refinement or an unknown result. Compute (13)--(18) using this exact
rational kappa. All ingredients are derived from N and the fixed public rules;
the certificate can be independently checked without trusting its producer.
No factor, order, useful relation, or selected embedding is provided as advice.

**Construction cost.** Mehlhorn--Sagraloff--Wang, Theorem 5, supplies
isolating disks for integer polynomials of degree d and coefficient bits tau,
and refinement to precision P, in soft-O(d^3+d^2 tau+dP) bit operations.
The exact integer coefficients provide its input access. This theorem, checked
directly in the primary paper, provides a polynomial construction primitive;
it is not a runtime guarantee for an arbitrary floating root solver.
[Primary Theorem 5](https://arxiv.org/pdf/1301.4870v2).

A fixed public polynomial precision cap P_max(n,d,tau,log H) makes the
construction bounded, with failures/unknowns retained. No assertion here says
every polynomial passes the geometry condition at that cap. Distinct-root
isolation itself has polynomial precision bounds: the elementary integral
discriminant argument gives

    sep(f)>=[2(A+1)]^(-(d(d-1)/2-1)).

This permits suitably fine rational disks in polynomial bits and fixed-factor
approximations to the positive pair quantities. It does not imply the much
stronger asymptotic bound (19). A root on a chosen classification boundary
need not be forcibly assigned to F. No practical time budget is claimed.

**Verification and count cost.** Let B_disk bound the bit widths of disk
coordinates/radii, and B_kappa those of p,q. Pair comparisons/minimum take
O(d^2) rational operations; taking a minimum selects one rational, it does
not multiply all pair denominators. Taylor verification can be implemented
in O(d^3) rational operations with widths polynomial in
d,tau,B_disk,log d. Disjointness and the root split use squared rational
comparisons. All arithmetic, not only operation counts, is charged.

The integers in (13), and the intermediate band comparisons, have widths

    O(n+d^2(B_kappa+log(2H)+log(d+1)+1)).                 (32)

Exponentiation, division and integer-root binary search on these widths
are polynomial bit algorithms. There are O(log(2H)) bands. Thus producing
and verifying B_cert is polynomial in n,d,tau,log H and the actual certificate
widths. The output count has O(log H+log d) bits. For polynomial certificate
precision and the witness parameters this is poly(n), with no height-H
or coefficient-line enumeration. Storage, disk generation and rejected
prerequisites are included. This is a mathematical construction, not an
implemented or empirically timed H020 routine.

## 7. What this says about yield, duplicates, and completion

In the theta<=1/2, lambda=0 case, one maximizer of the dyadic containing
bound occurs at smaller actual height:

    log x/D = log h/D = 44/49.

At theta=1/2 other maximizers can occur. These are locations of the upper
envelope, not assertions that candidates actually occur there. At the worst
permitted theta=25/49, the corresponding
maximizer is log h/D=1 and log x/D=4/5: even a full-height stratum can have
a smaller leading coefficient. No mass distribution has been proved.

If smaller-height or smaller-x strata dominate actual candidates, their
rational-norm envelope is also smaller. For a bin with x<=X and h<=Z, the
exact bounds are

    |g(m)|<=Xm+Z,
    |Res(f,g)|<=min(T,(2Z)^d M).

The reduction in the logarithm of this rational-norm envelope may be below
the leading norm scale at these fixed parameters, but it is real and must
not be erased in a joint-yield claim.
Exceptional rational cancellation and much smaller resultants require their
own bins as well. No full-height smoothness law is an unconditional upper
bound on their success probabilities.

A genuinely different surviving model would specify populations M_j by
actual x/height and rational/algebraic norm size, and a conditional joint
useful-yield probability pi_j for each bin of the selected tail. It must
establish or explicitly assume those correlated probabilities, not infer
them from norm upper bounds. The modeled collection obligation would then
use sum_j M_j pi_j, with sufficient independent usable rows, rather than
assigning every attempted element the same full-height law. If it invokes
the usual two-sided smoothness ansatz for a bin, its actual two norm-size
coefficients must replace H018's W in that ansatz. Generation and rejected
outputs, bin selection, processing, rank, and completion still cost work.
No such revised yield theorem or optimization is proved in this report.

Zero-resultant primitive linears correspond to rational linear factors of f;
there are at most d normalized ones, already safe under the superset bound.
If f is irreducible of degree >1 there are none. Zero g(m), if it fits the
box, forces x=1,y=-m under primitivity, and is separately excluded. Repeated
roots of f invalidate the declared square-free prerequisite; reducible but
square-free f is acceptable for the count and insufficient for a single-field
interpretation. Integer-square conditions, signs at embeddings, and the
positive-leading associate convention are different issues.

Repeated polynomials do not create new attempts. Different polynomials can
still produce duplicate or dependent relation/ideal data. Nonprimitive
multiples are outside S_prim and can enlarge an enumerator's all-output
charge; (18) is not silently substituted for S_all in H014/H018's enumeration
cost. There is no claim that gcd filtering retroactively saves that work.

Rational norm processing, prime-ideal labels including exceptional primes,
characters/square classes, rank, algebraic square roots and proper splitting
remain separately paid. H016's independent processing review supplies no
assumption to this proof. A bound on primitive supply gives no ideal
completion algorithm or success probability.

## 8. Remaining gap, quantifiers, and decisive next action

The concrete missing condition is (19) for the actual N-derived f and an
actually certified split J,F. A successful finite root/count certificate is
a theorem about that input; it is not evidence of a lower population.
Equations (24) and (27) show that **no additional large-root fraction
assumption is needed for the stated ordinary-base witness**. If a different
polynomial generator is used, its replacement for (24), or the actual theta
in (22)--(23), must be supplied explicitly.

In particular, at these parameters a sufficiently large primitive population
would have to escape the strict uniform geometry condition (28), or leave
the declared polynomial/primitive domain. Failing the geometry condition is
not sufficient for supply: one close pair can spoil the minimum in (2) while
the actual tail remains sparse. Failure of an approximate disk bound may
also reflect only a weak certificate.

Keep the quantifiers separate:

- For every fixed N passing the finite prerequisites, (18) holds as an exact
  upper bound. The ordinary-base recipe is deterministic; restarting it at
  the same public degree and height produces the same f.
- An asymptotic statement about all ordinary-base inputs needs a uniform
  geometric bound, which is absent. Special families satisfying (19) give
  only that scoped obstruction; special families violating it give no supply.
- A declared random-N average needs a theorem for that N distribution, not
  independent random coefficients substituted for the actual digits.
- Field selection for a fixed N is a different generator with its own norms,
  construction cost and per-N probability of obtaining a useful field. It
  needs enough useful supply after selection. Escaping this certificate alone
  is not useful supply, and repeated selection/rejection costs must be paid.

**Decisive next action:** obtain independent mathematical review of (4)--(18)
and the growing-degree optimization (20)--(28), especially the normalized
integer-determinant argument, strict integer endpoints, and dyadic count.
The next analytic question after review is whether the actual ordinary-base
family admits certified splits satisfying (28), or an explicit costed
alternative has enough useful yield while escaping it. This is more specific
than the original unproved homogeneity count. A subsequent empirical study
would require its own linear-only preregistration and authorization; none is
defined or executed here, and H019's quadratic protocol is untouched.

Best supported new result: the proposed finite primitive upper certificate
(18), with conditional exponent at most 9/5 under sub-D separation loss and
the quantitative margin (28). Positive mathematics awaits independent review.
No root sample, parameter sweep, finite experiment, solver/Lean change,
package installation, delegation, commit, publication, or scheduler occurred.
Only this report and adjacent H020-linear provenance are owned outputs.
Shared code checks were not rerun for this document-only analytic work.
**Verified factoring complexity improvement: NONE.**
