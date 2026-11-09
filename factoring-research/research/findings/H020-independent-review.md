# H020 — Independent mathematical review of the primitive linear tail

2026-10-08. Reviewed the complete 575-line
[submitted report](H020-linear-tail-supply.md), its
[provenance](H020-linear-provenance.json), the H020 hypothesis, and the full
H017/H018 reports, independent reviews and dispositions. Required project
instructions and STATE were read, together with W001 Card C and shared
accounting. The corrected H018 report is the version used here.

**Disposition: ACCEPT the finite primitive counting theorem, exact rational
certificate, growing-degree bounds and polynomial-bit construction in their
stated conditional scope. No mathematical correction is required.** The
ordinary-base uniform geometry question remains **INCONCLUSIVE**. This is
independent review of informal mathematics, not a Lean theorem, implementation
validation, novelty claim, or useful-supply result.

**Verified full factoring complexity improvement: NONE.**

The claim decisions are:

1. **ACCEPT — normalized evaluation geometry and primitive uniqueness.**
   The two complex evaluation rows control actual height; the large-root
   estimate retains x; the integer determinant gives at most one normalized
   primitive linear at each exceptionally small remaining-root evaluation.
2. **ACCEPT — weighted containment and uniform/per-x cutoffs.** Equations
   (7)–(15), including C, its degree dependence and the strict endpoint, are
   correct. These count a superset also containing zero norms.
3. **ACCEPT — exact finite upper certificate.** Equations (16)–(18) count
   containing rectangles in disjoint height bands. B_cert is an exactly
   computed upper bound, not the exact primitive population.
4. **ACCEPT — growing-degree optimization and ordinary-base specialization.**
   The 25/49 large-root fraction bound suffices; no additional small-fraction
   assumption is used. At sub-D separation loss the upper exponent is 9/5.
   The quantitative bound (27), strict margin (28), and optional finite
   endpoint (18a) are correct.
5. **ACCEPT — N-only parameter construction, root verification and bit costs.**
   The base-two rounding in (29) gives the claimed natural-log constants.
   Exact Taylor–Rouché predicates, complete root accounting, (31), the
   discriminant separation estimate, and the cited isolator support the
   polynomial-bit claim. They do not guarantee favorable geometry or a
   60-second implementation.
6. **ACCEPT — model interpretation and qualifications.** The resulting
   population deficit contradicts the unchanged H018 full-height joint-yield
   model on sequences passing the geometry condition. A count upper bound
   supplies no upper bound on smoothness probability. Smaller-height/norm
   strata require their own joint model.
7. **REJECT any stronger promotion.** The result does not prove H018's
   original all-output homogeneity count, uniform ordinary-base geometry,
   random-N behavior, field-selection success, a lower useful population,
   completion, or a factoring lower or upper complexity improvement.

No new substantive extension is proposed in this review. The derivations
below check the submitted claims and spell out their existing hypotheses.
There are no mandatory proposer edits. The next-action requirements at the
end are obligations for subsequent work, not repairs to the accepted theorem.

## 1. Domain, normalization and the two local lemmas

The finite theorem fixes integers N>1 and H>=1, a monic square-free integral
polynomial f of actual degree d>1 and actual coefficient height A, and

    g=xX+y,  1<=x<=H,  |y|<=H,  gcd(x,y)=1.

Actual A matters in A<=2^d M: it cannot be replaced by an arbitrarily inflated
coefficient upper bound while retaining that inequality. The report uses
the actual height. Positive x fixes the sign associate and excludes constant
polynomials. The population removes g(m)=0 and Res(f,g)=0. For the intended
ordinary-base application, m>=2, degree, monicity and f(m)=N must all pass
the stated checks. Irreducibility of f is not used by the count.

Monicity gives, with every root included once,

    |Res(f,g)| = M product_i E_i,
    R_i=max(1,|alpha_i|),  M=product_i R_i,
    E_i=|x alpha_i+y|/R_i.

Square-freeness ensures distinct roots. All d complex roots, including both
members of nonreal conjugate pairs, are required. Select any F of size r
whose roots have modulus at least 2H+2, let J be its complement of size
k=d-r>=2, and certify

    0<kappa<=(1/2) min_(i!=j in J)
                         |alpha_i-alpha_j|/(R_i R_j).

Neither maximality of F nor conjugation invariance is necessary.

For i,j in J the normalized evaluation matrix is

    [[alpha_i/R_i, 1/R_i], [alpha_j/R_j, 1/R_j]].

Its determinant has modulus Delta_ij. All four entries have modulus <=1;
thus every row of its inverse has sum of absolute values <=2/Delta_ij.
Applying it to the two complex evaluations proves

    h=max(x,|y|) <= 2 max(E_i,E_j)/Delta_ij.

Consequently two evaluations cannot both be strictly below kappa h. Ordering
the k evaluations, with e their minimum, gives

    product_(i in J) E_i >= e (kappa h)^(k-1).

This is an inverse-matrix estimate over C; it does not discard imaginary
parts or posit independent embedding values. Equality at kappa h is harmless.

For i in F, |alpha_i|>1 and the triangle inequality gives

    E_i >= x-H/|alpha_i| >= x-H/(2H+2) > x-1/2 >= x/2.

This holds even on the exact modulus boundary and for x=1. The weaker
constant 1/2 would lose the x^r weight. Multiplication yields the report's
inequality (5), with a weak >= sufficient even though the F factors are
strict. The case r=0 uses the empty product 1.

For primitive uniqueness, suppose g and g' both satisfy E_alpha<=1/(4H),
where R=max(1,|alpha|). Set D0=xy'-x'y, an integer. If |alpha|<=1, then

    D0=x g'(alpha)-x' g(alpha),  |D0|<=2H/(4H)=1/2.

If |alpha|>=1, then

    alpha D0=y' g(alpha)-y g'(alpha),
    |alpha| |D0|<=2H R/(4H)=|alpha|/2.

Both give D0=0. The nonzero integer coefficient vectors are proportional;
their primitivity and positive first coordinates make them identical. This
also handles y=0, |alpha|=1 and nonreal alpha. The second identity is crucial:
it cancels R exactly rather than introducing an unbounded modulus loss.
Taking the union over J gives at most k exceptions in the entire primitive
height-H box. Counting conjugate witnesses separately only overcounts.

The report's auxiliary comparison is also valid: if E_alpha<=h/(2R) and
h=|y|, then h<=R(x+E_alpha) implies x>=h/(2R). For h=x this follows from
R>=1. That comparison is not needed by the weighted proof.

## 2. Containment, strict endpoints and the finite count

Expanding the monic root product gives |f_j|<=binom(d,j) M and hence
A<=2^d M. With the unfloored real threshold

    T=(2H)^d(d+1)A N^(-1/(5d)),

one obtains

    T/M <= 4^d(d+1)H^d N^(-1/(5d)).

Outside the exceptional union every J evaluation is strictly greater than
1/(4H). Substituting in the resultant lower bound gives

    x^r h^(k-1)
      < 4*2^r*4^d*(d+1)*H^(d+1)*kappa^(-(k-1))*N^(-1/(5d))
      = W.

Thus the constants C and W in (8) and the direction and strictness of (9)
are correct. The extra H comes from the uniqueness threshold, not an
unjustified replacement of global H by actual h. No lattice volume is used.

The per-x cutoff Y(x)=(W/x^r)^(1/(k-1)) is valid because k-1>0.
As x>=1, W^(1/(k-1)) also supplies a uniform cutoff. For an integer h_*
at least this cutoff, all admitted nonexceptions have h<=h_*-1. With
Z=min(H,h_*-1), the positive-leading containing square has Z(2Z+1)
integer pairs. Adding k and capping by H(2H+1) proves (12). This formula
allows h_*=1 or h_*>H without a boundary failure.

For kappa=p/q>0, use a=5d(k-1), b=5dr only in this paragraph's arithmetic
notation. Raising positive quantities to the integer power 5d gives exactly

    U x^b h^a < V,
    U=N p^a,  V=q^a C^(5d).

No reduction of p/q to lowest terms is needed for correctness, although
reduction can save work. The uniform cutoff is U h_*^a>=V. Equality there
is safe: any nonexception at height h_* would contradict its strict
containment. The accepted resultant inequality itself is closed and
equivalent to |Res|<=floor(T); these are different endpoints.

For L=2^j and Z=min(H,2L-1), a nonexception with L<=h<=Z has

    U L^a x^b < V.

When r>0, U L^a and x^b are nonnegative integers, so this is equivalent to

    x^b <= floor((V-1)/(U L^a)).

This justifies exactly the V-1 and the integer root in (16). When r=0,
b=0 and x contributes no restriction; testing U L^a<V directly is the
correct separate branch and avoids an undefined zeroth root.

In either case 0<=X<=Z. The containing rectangle has X(2Z+1) points.
Its subset with h<L is exactly

    1<=x<=min(X,L-1),  |y|<=L-1,

and therefore contains min(X,L-1)(2L-1) points. Their difference is B_j.
The subtraction removes only the earlier height bands, not points in the
band under review. Every original positive-leading height belongs to exactly
one such band, including a final clipped band. Adding k proves (17)–(18).

The count does not impose gcd or the resultant condition on its rectangles;
it deliberately counts a superset. B_cert is an exact integer upper bound,
not an assertion of exact S_prim or of population existence. In particular:

- H=1 has the single band L=Z=1 and no subtracted lower-height points.
- k=2 leaves a=5d>0 and all proofs well defined.
- Q_j=0 gives X=0 when r>0, hence B_j=0.
- Equality U L^a x^b=V is excluded, as required for nonexceptions.
- T<1 makes the specified nonzero-resultant population empty by integrality,
  regardless of whether this containing bound notices that stronger fact.

These are symbolic boundary checks, not executed finite tests.

## 3. Growing degree and exact margins

Let t=log N, D=t^(1/3)(log t)^(2/3), log H=(1+o(1))D and
d=(7/5+o(1))(t/log t)^(1/3). Then

    t/(5d^2 D) -> 5/49 = q0.

The exact logarithm of W is

    log W = (d+1)log H - t/(5d) + (k-1)log(1/kappa)
            + log 4 + r log 2 + d log 4 + log(d+1).

If log(1/kappa)<=(lambda+o(1))D, divide by dD and set theta_N=r/d.
The first three terms give 1-q0+(1-theta_N)lambda+o(1).
The extra log H contributes O(1/d); the explicit exponential-in-d
constants contribute O(1/D). These errors are uniform over 0<=r<=d-2.
No factor d^(c d) in the final population is concealed. Indeed
d log d=(7/15+o(1))D, so such a final multiplicative loss would matter.

To audit the discrete-to-asymptotic step, consider any band with X_j>=1.
Use v=log X_j/D and z=log Z_j/D. The bound defining X_j gives

    r log X_j+(k-1)log L_j < log W

also in the r=0 branch. Since L_j<=Z_j<2L_j, replacing L_j by Z_j
costs at most (k-1)log 2. Thus

    0<=v<=z<=1+o(1),
    theta_N v+(1-theta_N)z
      <=1-q0+(1-theta_N)lambda+o(1).

Moreover B_j<=X_j(2Z_j+1)<=3X_j Z_j. The logarithm of the number of
bands is O(log log(2H))=o(D), and log k=o(D). If every band is empty,
only the at-most-k exceptions remain. This proves that optimizing v+z
really bounds both S_prim and B_cert. It is not a replacement of lattice
points by continuous area.

For a limiting theta<=1/2,

    theta v+(1-theta)z - (v+z)/2
       =(1/2-theta)(z-v)>=0,

which yields (22). For theta>=1/2, solving the constraint for v gives

    v+z <= [1-q0+(1-theta)lambda]/theta
              + [(2theta-1)/theta]z
          <= 2-q0/theta+(1-theta)lambda/theta.

The limiting height restriction supplies z<=1. The ambient square supplies
the cap 2. Passing to subsequences is valid because theta_N and the relevant
band coordinates are bounded; a limit of theta_N is not assumed globally.

For the actual checked ordinary-base f, every digit has size <m and the
leading digit is one, so A<=m<=N^(1/d). The accepted Mahler/l2 estimate is

    M<=||f||_2<=sqrt(d+1)A.

Every member of F contributes at least log(2H+2) to log M, hence

    r/d <= [t/d+(1/2)log(d+1)]/[d log(2H+2)].

Since d^2 D/t -> 49/25 and log(2H+2)/D -> 1, this gives
limsup theta_N<=25/49. It allows multiple enormous roots and does not
use randomness or presume that the remaining roots are bounded. Eventually
k is a positive fraction of d. It applies to any certified subset F.

At lambda=0 the theta<=1/2 branch is 88/49. On the other branch the
upper bound increases with theta, attaining its largest permitted value
2-(5/49)/(25/49)=9/5. For 0<=lambda<q0, the derivative of the second
branch with respect to theta is (q0-lambda)/theta^2>0. The first branch
is at most its value at theta=0. This proves exactly

    limsup log(max(1,S_prim))/D
       <= min(2, max(88/49+2lambda, 9/5+24lambda/25)).

The same bound holds for B_cert. This is a valid convenient upper bound;
it is not claimed to be an attained population or a sharp estimate for f.

The required attempt exponent can be reconstructed without decimal fits:

    K/delta+delta = (9/5)/(7/5)+7/5 = 94/35,
    (94/35)/(3*19/20)=376/399,
    u_required=19/20+376/399=15101/7980.

The stated differences and thresholds are correct:

    u_required-9/5 = (15101-14364)/7980 = 737/7980,
    u_required-88/49 = (105707-100320)/55860 = 5387/55860,
    9/5-88/49 = (441-440)/245 = 1/245,
    (u_required-88/49)/2 = 5387/111720,
    (u_required-9/5)*(25/24) = 3685/38304.

The first lambda threshold is smaller: on common denominator 1340640,
their numerators are respectively 64644 and 128975. It is also <5/49,
so its strict satisfaction is within the range used to prove (27).
Equality at the critical asymptotic threshold is undecided, as reported.

For (18a), B_cert^20<=H^37 is exactly the sufficient comparison
B_cert<=H^(37/20). Its stated margin is

    u_required-37/20 = (15101-14763)/7980 = 169/3990.

At lambda=0 the same exponent bound for B_cert, together with
log H/D->1 and 9/5<37/20, ensures this comparison eventually holds.
It remains a proposed optional analytic endpoint, not an executed or frozen
experiment. A single passing certificate gives a finite upper count, not
an asymptotic frequency or a finite smooth-relation shortage.

## 4. Public parameter rules and exact root certificates

Write c=log 2 only for this rounding check. For n=bitlength(N) and
ell=bitlength(n),

    n=t/c+O(1),
    ell=(log t)/c+O(1),
    n/ell=(1+o(1))t/log t.

Thus the integer cube-root rule for d gives the coefficient 7/5; the
inner floor, cube-root floor and max with 2 have no leading effect. Also

    e_H=(n ell^2)^(1/3)+O(1),
    log H=c e_H=(1+o(1))t^(1/3)(log t)^(2/3).

The base-two factors cancel. There is no missing factor log 2 in either
parameter. H has e_H+1 bits, polynomial in n. The construction is an
integer algorithm with a fixed public rule, not a real logarithm oracle.

Integer-root search for m and division for the ordinary-base digits are
polynomial-bit tasks. Check m>=2, actual degree d, leading coefficient one,
actual height A, f(m)=N, and gcd(f,f')=1. Small inputs may fail these
prerequisites. Square-free reduction cannot be substituted while retaining
the original degree, resultant cutoff or root product. Reducibility is
permitted by the count, but it does not certify a number field.

For each rational complex center c_i and positive rational radius t_i,
the Taylor coefficients are exact Gaussian rationals. The report uses
valid upper and lower magnitude bounds:

    |a_ij|<=|Re a_ij|+|Im a_ij|=u_ij,
    |a_i1|>=max(|Re a_i1|,|Im a_i1|)=l_i1.

On the circle |z-c_i|=t_i, predicate (30) makes a_i1(z-c_i) strictly
dominate the remainder. It has exactly one zero inside, so Rouché gives
one zero of f counting multiplicity, and none on the boundary. Requiring
d such disks and the strict squared disjointness predicates accounts for
all degree-d roots. A single representative of a conjugate pair would not
suffice. Failure of this sufficient Taylor test is unknown, not root absence.

The strict disk test |c_i|^2>(2H+2+t_i)^2 implies
|alpha_i|>=|c_i|-t_i>2H+2, as required for F. It need not recognize an
exact-boundary root. Such a root can remain in J, and k and all separation
minima must then be computed for that actual J.

The rational U_i in (31) bounds max(1,|alpha_i|) from above. Conversely,
the triangle inequality in the maximum coordinate norm gives

    |alpha_i-alpha_j|
       >= max(|Re(c_i-c_j)|,|Im(c_i-c_j)|)-t_i-t_j.

Truncating this at zero gives a valid L_ij. Therefore
L_ij/(U_i U_j)<=Delta_ij, so kappa_cert is sound. A zero L_ij requires
refinement or an unknown status; it is not a usable zero separation constant.
No approximate root position alone can authorize the subsequent count.

The theorem accepts any verified split and valid rational lower bound. To
make a concrete producer reproducible, its isolator, precision cap and disk
classification rule must also be fixed. This is already the report's public
construction requirement, not an all-input success assumption.

## 5. Construction, verification and width accounting

I checked the cited primary source directly. Mehlhorn–Sagraloff–Wang,
Theorem 5 (printed page 19), gives isolating disks and multiplicities for
integer degree-d polynomials of coefficient bits tau in soft-O(d^3+d^2 tau)
bit work, and refinement to precision P within soft-O(d^3+d^2 tau+dP).
It supports precisely the polynomial construction primitive cited here.
Exact integer coefficients meet its access requirements; the square-free
check supplies d distinct roots. This is not a bound for an arbitrary
floating root finder. [Primary Theorem 5](https://arxiv.org/pdf/1301.4870v2).

The elementary precision estimate is independently valid. Put
B=2(A+1) and s=d(d-1)/2. Cauchy's monic root bound gives every root
modulus <=A+1, hence every pair distance <=B. Since f is monic, integral
and square-free, its discriminant is a nonzero integer. Selecting a closest
pair gives

    1<=|disc(f)|=product_(i<j)|alpha_i-alpha_j|^2
                 <=sep(f)^2 B^(2(s-1)).

Thus sep(f)>=B^(-(s-1)), as stated, including d=2. Its negative logarithm
is O(d^2 log(2A)). Root coordinates and sufficiently small rational radii
can consequently be represented with polynomially many bits. Fine disks
give fixed-factor estimates of positive normalized pair distances: the
coordinate norms differ from Euclidean norms by absolute factors, and
their radius errors can be made a fixed small fraction of separation.
Taking a pairwise minimum does not exponentiate that loss by d.

This explains polynomial isolation precision, not the desired small
log(1/kappa)/D. The crude separation estimate can be far weaker than
condition (19). A polynomial precision cap also does not guarantee that
every proposed disk passes the particular sufficient Taylor predicate,
every boundary is classified, or the useful count comparison succeeds.
Those unknown outcomes must remain explicit.

For verification, Taylor coefficients can be formed by the finite formula

    a_ij=sum_(l=j)^d f_l binom(l,j)c_i^(l-j).

This takes O(d^2) rational operations per disk, hence O(d^3) for all d.
Common denominators for each center and radius, binomial coefficients,
powers of degree at most d and finite sums give widths polynomial in
d,tau,B_disk,log d. Exact cancellation need not be numerically resolved;
it is rational arithmetic. The pair tests, squared disjointness tests and
F classification take O(d^2) further rational operations. Each candidate
for kappa uses only a fixed number of disk-derived quantities; a minimum
selects one rational, without multiplying all denominators.

Expanding the integer widths explicitly, log C is
O(d log(2H)+d+log(d+1)), while a_exp and b_exp are O(d^2).
Therefore U, V, U L_j^a_exp and the tested x powers have bit widths

    O(n+d^2(B_kappa+log(2H)+log(d+1)+1)),

as in (32). Exact division, integer powers and binary-search integer roots
on those widths are polynomial-bit operations. There are O(log(2H)) bands,
polynomially many for the witness; there is no loop over H points. The
ambient cap bounds the final output width, and storage for operands and
disk data is charged. For polynomial precision, d,tau,log H are polynomial
in n under the public construction, so the whole mathematical procedure
has polynomial bit cost. No explicit machine exponent or implementation
runtime has been proved by H020.

Construction, independent verification, failed prerequisite checks and
unknown certificate outcomes are all part of the cost. No factor/order
advice or selected useful relation is required. The finite certificate is
independently verifiable even when its producer is untrusted.

## 6. Yield interpretation, exceptional inputs and next action

The conditional comparison is correctly scoped. Under the unchanged H018
joint-yield law and B-scale collection obligation, distinct usable primitive
attempts require exponent at least 15101/7980. The upper count 9/5, or the
quantitative bound with lambda<5387/111720, is smaller. Thus this particular
population premise cannot hold on sequences satisfying the certified
geometry condition. No smoothness assumption entered the count proof.
The yield law enters only in turning scarcity into a contradiction of
that model. A count upper bound alone places no upper bound on the
smoothness probabilities of the candidates that do exist.

The submitted envelope locations are correct. At theta<=1/2, lambda=0,
v=z=44/49 is one maximizer of the containing constraint; when theta=1/2
there are others. At theta=25/49 the extremal choice is z=1,v=4/5.
These statements describe a relaxed upper envelope, not actual mass or
height distribution. For a bin x<=X, h<=Z, direct triangle/product bounds
give precisely

    |g(m)|<=Xm+Z,
    |Res(f,g)|<=min(T,(2Z)^d M)

on admitted elements. A smaller rational envelope does not assert that
actual norms attain it; its change can be lower order in the original
leading smoothness scale. Substantially smaller resultants or rational
cancellation can require materially different probabilities nevertheless.

A revised stratified model must therefore establish or explicitly assume
the selected population in each bin and its conditional joint useful-yield
probability, with the actual two norm-size scales. The obligation involves
the sum of these population-times-probability contributions, plus enough
independent rows. The original full-height law cannot silently serve as a
universal success-probability upper bound. Generation, selection, rejected
outputs, processing, dependence, rank and completion remain charged.
The report neither derives nor validates such a changed yield model.

The remaining domain qualifications are sound:

- A zero resultant means g's rational root is an f-root. Any such allowed
  root has modulus <=H, so it lies in J and its primitive g is already in
  the exceptional union. There are at most d normalized primitive linear
  factors of f in total; for irreducible f of degree >1 there are none.
- Primitivity and g(m)=0 imply x=1,y=-m, when that pair fits the box.
  Neither rational zero nor resultant zero is a smooth nonzero norm.
- Repeated roots violate the theorem's declared square-free prerequisite.
  Square-free reducible f is valid for counting but does not define the
  intended single number field.
- The normalized determinant bound controls primitive directions only.
  Nonprimitive multiples are outside S_prim; their emission/filtering costs
  do not disappear. B_cert cannot replace S_all in the accepted enumeration
  cost. Nor does the review conclude that every nonprimitive relation is
  useless under every different model.
- Repeated polynomials are not new attempts. Distinct polynomials may still
  yield duplicate or dependent ideal data. Positive-leading normalization
  does not resolve embedding signs, ideal square classes or characters.
- Prime-ideal labels, exceptional primes, rank, algebraic square roots,
  proper splitting and their probabilities and costs remain separate.
  H016's processing result is not a hidden supply or completion premise.

**Concrete remaining gap:** for the actual N-derived polynomials, prove
a bound log(1/kappa)<=(lambda+o(1))D with a fixed
lambda<5387/111720 on an actually certified split, in the input scope being
claimed. The ordinary-base Mahler bound already controls r/d, so an extra
o(d)-large-roots premise is unnecessary. A theorem for a special family,
a theorem for a declared random-N distribution, and a theorem for every
input are different outcomes. A fixed-N field selector is yet another
construction with different norms, cost and per-N success obligations.

Failure of this separation condition is only an escape from this upper
bound, not evidence of supply. A single close pair can make the minimum
small, and weak disks can fail even when the true geometry is favorable.
Repeating the deterministic ordinary-base construction at the same public
parameters does not change the field polynomial.

**Decisive next action:** the coordinator can accept this finite theorem
and conditional model obstruction as independently reviewed informal
mathematics. The next analytic task should address the displayed separation
gap for an explicitly declared ordinary-base input scope, or supply a costed
alternative with actual useful yield and a revised joint law. A future
finite linear-certificate study would need its own preregistration; it
cannot establish the asymptotic quantifier by a pass frequency alone.
This review runs no such study and changes no H019 protocol or H021 work.

## 7. Evidence and ownership record

The reviewed H020 report has SHA-256
`a69076b8379a12a3b413d4072ab6ea0cec491f190e35dd21f3df2ab00236a5b3`.
Of the 13 proposer-manifest input/output checks, 12 match. The sole mismatch
is the coordinated live STATE file already identified in the handoff.
Both its claimed and captured hashes are retained in
[review inputs](H020-review-inputs.json). Hashing establishes correspondence
to the captured bytes, not historical execution chronology or correctness
of the mathematics.

The proof audit, including rational constants and boundary cases, was
symbolic. No arithmetic runner, finite experiment, numerical root sample,
parameter sweep, candidate enumeration or yield test was needed or run.
Read-only hashing and document verification are provenance work, not a
registered research experiment. No shared code or Lean changed, so shared
code/build checks were not run. This review does not import H017's finite
arithmetic audit as validation of H020.

Owned outputs are this report and adjacent H020-review input/provenance
files only. The proposer report, prior evidence, hypotheses, STATE,
registries, shared solver and Lean are untouched. No packages, delegation,
commits, publication or scheduler were used. Completion hashes and input
changes, if any, are recorded in [review provenance](H020-review-provenance.json).

**Verified full factoring complexity improvement remains NONE.**
