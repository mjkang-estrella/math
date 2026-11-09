# H008 — New independent review of the quadratic embedding selector

Date: 2026-10-08. This is a new independent review round, not a continuation of
the proposer’s backing thread. Reviewed inputs: the full
[H008 report](H008-resultant-selector.md), its
[provenance](H008-resultant-provenance.json), and the original
[W001 Card C](../hypotheses/W001-relations.md), together with AGENTS.md, README.md,
docs/SPECIFICATION.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md and research/STATE.md.

**Disposition: accept the restricted separation/counting proof; revise the
scope of rejection.** The factor 72, strict threshold, scale correction,
root-union count and real-embedding norm-gain mapping withstand review. The
nonzero-constant hypothesis can be removed using a padded degree-two
resultant. The original Card C wording does not unambiguously exclude every
reducible polynomial, so an at-most-d bound on *all* its rows would be wrong.
Reducibles have a precise common-factor/triangle structure and reduce to
linear factors of height at most sqrt(3) H, with explicit parity bookkeeping.
They can still provide many new linear relation directions.

This rejects the proposed large population of **new irreducible quadratic**
relations at the three specified tolerances. It does not exclude a lucky small
dependency, efficient discovery of useful new linear factors, other
small-resultant mechanisms, or faster factoring. Verified new factoring
complexity improvement: **NONE**. The reviewed proof is informal mathematics,
not a Lean theorem. The extensions proved in this review are new review
findings, not independently reviewed formal results or a major promotion.

## 1. Claim decisions and correspondence to Card C

Accepted:

- For height at most H and a fixed complex point alpha, two quadratics obeying
  the same normalized epsilon slab have resultant magnitude at most
  72 epsilon H^4. Strict inequality 72 epsilon H^4 < 1 forces a common factor.
- With primitive irreducible quadratics normalized to positive leading
  coefficient, there is at most one per embedding and at most d per fixed f.
  The three nested tolerances do not multiply the union count.
- With t = log N, ell = log t, d ~ delta (t/ell)^(1/3) and
  log H ~ a t^(1/3) ell^(2/3), the proposed epsilon = N^(-lambda/d)
  satisfies epsilon H^C -> 0 for every fixed C. This is an asymptotic statement,
  without a certified finite-N crossover.
- The complete cube enumerator has H^3 poly(n) selector cost, including all
  failures. Its real-root membership precision can be polynomial in n.
  This is a specified algorithm and a cost argument, not an implementation run.
- A real-root slab saves at most the stated factor in a deterministic norm
  *upper bound*, with eta = 1 - lambda/2. No density or smoothness probability
  follows from this upper bound.

Rejected or narrowed:

- “At most d relations” is accepted only for the normalized irreducible
  quadratic subset. Card C says it rejects constructions “that merely
  reproduce previously counted products”; that can admit products with new
  linear factors. H008’s enumerator imposes the stricter filter.
- Pairwise padded resultants zero implies a common **projective** factor,
  identical irreducible quadratics, or a triangle. For actual degree-two
  polynomials the factors in the common-linear/triangle cases are affine
  linear. If degree-one inputs are admitted, a factor at infinity must be
  allowed. Omitting this qualification makes the extension false.
- A common linear factor does not bound relation rank by d. Its matrix
  contribution has rank at most one *per common-factor family*, in addition
  to the potentially large matrix from the remaining linear factors.
- No theorem here requires B rows for every factoring approach. The d-row
  bound contradicts Card C’s stated conventional B-scale population premise;
  it does not prove that every smaller set has full rank or gives trivial gcds.
- Continuous slab volume is not an integer-point count. Treating its inverse
  as a finite L[1/3,tau] loss is invalid at the proposed tolerance scale.
- No whole-family rejection of small resultants, or new factoring upper or
  lower bound, is accepted.

## 2. Corrected exact lemma, including zero constant terms

For g = c0 + c1 X + c2 X^2 and h = e0 + e1 X + e2 X^2, define

\[
 D_2(g,h)=\det\begin{pmatrix}
 c_0&c_1&c_2&0\\
 0&c_0&c_1&c_2\\
 e_0&e_1&e_2&0\\
 0&e_0&e_1&e_2
 \end{pmatrix}.
\]

Use this same 4-by-4 determinant even if an outer coefficient is zero. It is
the degree-two homogeneous resultant, up to the harmless choice of sign.
When both original polynomials have degree exactly two, it is their ordinary
resultant up to sign, even when c0 or e0 vanishes.

**Lemma.** Let H >= 1, epsilon >= 0, alpha in C, and g,h have degree at most
two with integer coefficients bounded in absolute value by H. If

\[
 |g(\alpha)|,|h(\alpha)|
 \le \epsilon H(1+|\alpha|+|\alpha|^2),
 \tag{1}
\]

then

\[
 |D_2(g,h)|\le72\epsilon H^4.                 \tag{2}
\]

If g,h are nonzero and 72 epsilon H^4 < 1, their degree-two homogenizations
have a common nonconstant homogeneous factor over Q. For genuine quadratics
this is an ordinary common polynomial factor. If both are primitive irreducible
quadratics, they are equal up to sign.

**Proof of the estimate.** For |alpha| <= 1, replace the first column of the
displayed matrix by C1 + alpha C2 + alpha^2 C3 + alpha^3 C4. This preserves
the determinant. Its entries are g(alpha), alpha g(alpha), h(alpha),
alpha h(alpha); each has magnitude at most 3 epsilon H. Each complementary
3-by-3 minor has six signed terms of magnitude at most H^3. Expansion down
the replaced column gives 4 * 3 * 6 epsilon H^4, exactly the claimed 72.
This deliberately loose bound is valid for complex entries and for zeros.

For |alpha| > 1 put z = 1/alpha and use the **padded** reversals
g*(X) = c2 + c1 X + c0 X^2, h* similarly. Their heights remain at most H,
and |g*(z)| <= epsilon H(1+|z|+|z|^2), likewise h*. Reversing all four
columns of the original matrix and then swapping rows 1 with 2 and rows 3
with 4 gives exactly the matrix for g*,h*. These permutations preserve the
determinant here; in particular their magnitudes agree. This is a polynomial
matrix identity, so it remains true when g* or h* loses degree. Apply the
first part to the padded reversals. No nonzero-constant assumption is needed.

The determinant is an integer, hence magnitude **strictly less than 1**
forces it to be zero. The sufficient condition is <, not <=; the estimate
at equality alone cannot rule out an integer determinant of magnitude 1.
No optimality of the numerical constant is asserted.

For completeness, homogenize to G(X,Z) = c2 X^2 + c1 XZ + c0 Z^2 and Hh
similarly. The Sylvester matrix represents the map from two homogeneous
linear forms A,B to A G + B Hh. If G,Hh are coprime in Q[X,Z], a kernel
element would imply G divides B, impossible for nonzero B of degree one;
then A is also zero. Conversely, a common degree-one factor gives a kernel
element (Hh/D,-G/D); proportional degree-two forms also give a kernel.
Thus zero determinant is equivalent to a common homogeneous factor.
For genuine quadratics neither form has Z as a factor, so it dehomogenizes
to an affine common factor. Irreducibility forces proportionality, and
primitive integral coefficients force the proportionality to be +1 or -1.
This proves every assertion. □

The original proof is therefore correct on its stated domain. Reversal of a
zero-constant polynomial is not an error in that proof, which explicitly
excluded it; padded reversal is the necessary repair when extending the domain.

### Union and tolerance accounting

For a fixed f, assign each retained irreducible quadratic a witnessing root.
Two different normalized quadratics cannot have the same witness once (2)
is below 1. Thus the union has at most the number of distinct roots, <= d.
For real coefficients, conjugate roots impose identical conditions; if f
has r1 real roots and r2 nonreal conjugate pairs, r1+r2 is a sharper bound.

N > 1 implies epsilon_1 >= epsilon_(3/2) >= epsilon_2. Taking their union
is exactly taking epsilon_1. The rounded tolerances
E_lambda = 2^(-floor(lambda log2 N/d)) remain nested and satisfy
epsilon_lambda <= E_lambda < 2 epsilon_lambda. Use the exact condition
72 E_1 H^4 < 1; the simpler 144 epsilon_1 H^4 < 1 is sufficient.
There is no extra factor three in the candidate bound.

In the proposed regime,

\[
 \log(1/\epsilon_\lambda)
  =(\lambda/\delta+o(1))t^{2/3}\ell^{1/3},\qquad
 \frac{\log(1/\epsilon_\lambda)}{\log H}
  \sim\frac{\lambda}{a\delta}(t/\ell)^{1/3}\to\infty.
\]

Consequently the threshold holds eventually, uniformly over the embeddings
of each f. Polynomially many f’s still supply only polynomially many
irreducible candidates. J fields supply at most Jd, but combining different
fields’ relations requires additional accounting and does not follow from
this count.

For a real alpha, one coefficient of (1,alpha,alpha^2) has magnitude at
least (1+|alpha|+|alpha|^2)/3. Holding the other two continuous coordinates
fixed, the allowed interval in that coordinate has length at most
6 epsilon H. Thus the continuous cube fraction is at most 3 epsilon.
If comparable discrete density were assumed, inverse acceptance would have
L[2/3,lambda/delta] scale. That assumption is not a lattice-point theorem:
exceptional exact factors can survive a vanishing-volume window. The
resultant argument supplies the rigorous restricted count instead.

## 3. Pairwise-zero families: proof of the precise extension

Normalize primitive, nonzero, degree-two homogeneous forms up to sign.
Suppose every pair has D2 = 0. Then one of the following holds:

1. The family consists of a single irreducible quadratic form.
2. Every form has a common rational homogeneous linear factor U.
3. There are three distinct rational linear factors U,V,W and the family
   consists of the three normalized products UV, UW, VW. In particular it
   has at most three members.

The alternatives need not be made disjoint for families of size <= 2; every
such reducible pair already has a common linear factor. The third alternative
with no global common factor necessarily contains all three products.

**Proof.** If an irreducible quadratic is present, its common factor with
any other member must have degree two. Every other member is proportional
to it and normalization identifies them.

Otherwise each form splits over Q into two linear factors, with repetitions
allowed. Record its support as a set of size one or two of linear factors
up to scalar. By the resultant criterion, these supports intersect pairwise.
If their total intersection is nonempty, choose U in it and obtain case 2.

Suppose the total intersection is empty. No support can be a singleton,
since its factor would have to occur in every support. Choose a support
{U,V}. Some support misses U and therefore has the form {V,W}, with
W distinct from U,V. Some support misses V; meeting both displayed supports
forces it to be {U,W}. Any further support of size at most two must meet
all three. If it contained a factor outside {U,V,W}, its one remaining
factor would have to be in the empty intersection of those three pairs,
an impossibility. A singleton also cannot meet all three. Therefore it is
one of {U,V}, {U,W}, {V,W}. Primitive normalization makes each such product
unique. This proves the triangle claim rather than assuming it. □

For genuine affine quadratics, neither U,V,W nor a common factor can be Z,
so this proves exactly the requested affine classification, including X as
a factor and hence zero constant terms. If degree <= 2 includes linears,
the projective qualification is essential: X and X+1 have padded D2 = 0
because their homogenizations XZ and (X+Z)Z share Z, although they have no
common affine factor. A whole arbitrary family of linears has this same
factor at infinity. Dehomogenizing Z gives the constant 1, so this case
simply retains the ordinary linear elements; it is not a quadratic novelty.

Apply the classification separately to each embedding’s set at the widest
tolerance. A union of d embedding sets is not itself necessarily pairwise
intersecting. For bookkeeping, assign each row to one witnessing embedding.
There are at most d common-factor groups and at most 3d rows in all
non-common-linear groups. These bounds do not bound the sizes of the
common-factor groups.

## 4. Linear-factor heights, population and exact dependency accounting

### Heights and availability

A primitive reducible integral quadratic factors as g = u v with primitive
integer linear u,v after choosing their signs. To justify the integrality
normalization, clear denominators in its rational linear factors and take
primitive parts. A product of primitive integer polynomials is primitive:
for every prime p the two nonzero reductions have nonzero product in Fp[X].
Thus the remaining rational scalar is an integer by integrality of g and
is +/-1 by primitivity. With g’s leading coefficient positive, both linear
leading coefficients can be chosen positive and g = uv exactly. This avoids
silently dropping a sign column. If signs are instead arbitrary, absorb
the sign into v and retain it in all parity maps below.

For an integer linear u = aX+b, M(u) = max(|a|,|b|) = H(u).
Mahler measure is multiplicative by its root-product definition, and
M(g) <= ||g||2 <= sqrt(3) H. Hence the stronger useful bound is

\[
 H(u)H(v)\le\sqrt3 H,
 \qquad H(u),H(v)\le\sqrt3 H.                 \tag{3}
\]

The second assertion uses H(u),H(v) >= 1, not an assumption that a factor
has unit height. A direct verification of the measure inequality is to
integrate log|g(e^(i theta))|, apply concavity of log to |g|^2, and use
orthogonality of the powers of e^(i theta). The rootwise identity for the
integral is log max(1,|root|), obtained from the power series for log(1-z)
inside the unit disk and a limiting integral at its boundary. This gives
log M(g) <= (1/2) log(sum |coefficient|^2).
The same coefficient bound is recorded in the primary research paper
[Abbott, §3.2](https://arxiv.org/pdf/0904.3057), checked in this review.

For a fixed common u of height U, every v therefore has height at most
sqrt(3) H/U. There are at most
(2 floor(sqrt(3) H/U)+1)^2 coefficient pairs, before primitivity and
normalization. Thus a common-factor family can have O((H/U)^2) rows.
It need not have O(1) rows. For example, at alpha = 0 all primitive
X(aX+b) with |a|,|b| <= H satisfy every slab exactly. This example is a
counterexample to a universal constant-size reducible count, not an example
of a root of the irreducible f assumed by Card C.

All linear factors of all primitive reducible height-H quadratics lie in
one ordinary linear coefficient square of radius sqrt(3) H. Thus there
are O(H^2) possible distinct factor polynomials in total. Moreover the
number of reducible quadratics in the entire cube is O(H^2 log(2H)):
group H(u) into dyadic ranges [2^j,2^(j+1)); each range gives O(2^(2j))
choices for u and O((H/2^j)^2) choices for v by (3), and there are
O(log(2H)) ranges. Overcounting ordered factors only helps this upper bound.
The broader selector therefore has at most O(H^2 log(2H)) + d candidates,
not the H^3 raw coefficient population. This is still L[1/3,2a], which
can be large; it is not a d-rank theorem or by itself an impossibility proof
for the original smoothness target.

### One common factor: what the extra parity coordinate actually means

Let theta be the class of X in K = Q[X]/(f), for monic irreducible f of
degree > 2. Exclude zero rational evaluations before forming a relation.
Work first with the **exact** F2 square-class space

\[
 (\mathbb Q^*/\mathbb Q^{*2})\oplus(K^*/K^{*2}),
 \qquad q(w)=[(w(m),w(\theta))].
\]

This is an abstract algebraic space; computing its coordinates is not
being assumed free. The same identities hold for any defined multiplicative
parity map recording rational primes, prime ideals, signs and appropriate
character data. A finite set of necessary parity tests need not describe
the exact square-class kernel. Ordinary NFS still needs its square-root and
exceptional-prime checks; see
[Stevenhagen, §§6–10](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).

For k rows g_i = u v_i set c = q(u), let V have columns q(v_i), and let R
have columns q(g_i). With 1 the length-k all-ones vector,

\[
 R=V+c\,1^{\mathsf T},\qquad
 Rx=Vx+c(1^{\mathsf T}x).                    \tag{4}
\]

Consequently

\[
 K_0:=\ker\begin{pmatrix}V\\1^{\mathsf T}\end{pmatrix}
  =\ker R\cap\ker(1^{\mathsf T})
  =\ker V\cap\ker(1^{\mathsf T}).            \tag{5}
\]

K0 has codimension at most one in each of ker R and ker V. All even-cardinality
dependencies are exactly the dependencies of the v_i with one extra
even-cardinality condition. The odd dependencies, if present, are the one
coset specified by Vx = c and 1^T x = 1. They must not be erased by claiming
that u always cancels. Equivalently, include the one additional column c
and map x to (x,1^T x) in ker[V c]. In particular

\[
 |\operatorname{rank}R-\operatorname{rank}V|\le1,
 \quad |\dim\ker R-\dim\ker V|\le1.          \tag{6}
\]

These are finite-dimensional statements on the span of the finitely many
columns, even when the ambient exact square-class space is infinite.

The multiplicative identity underlying the even case is literal:
prod g_i = u^(2r) prod v_i for 2r selected rows. If square roots of the
v-product are available, multiply them by u(m)^r and u(theta)^r to obtain
the roots for the g-product. No factorization or smoothness of u is needed
to know that u^(2r) is a square. Conversely division by this known square
transfers squarehood in the fields. Modular division requires a unit;
gcd(u(m),N) must be checked, returning a proper factor if one is found,
and zero/nonunit exceptions must be retained rather than silently inverted.
This identity does not price the computation of the v-product roots.

Thus the phrase “ordinary linear v_i plus one parity coordinate” is correct
for the even subspace; a complete statement also retains the possible odd
coset, or the extra ordinary linear element u. Merely noticing reducibility
does not make an unprocessed v_i redundant.

For s common-factor groups, let T mark the group of each column and let C
contain their s common-factor vectors. Then R = V + CT. Requiring Tx = 0
cancels all common factors and costs at most s independent parity conditions;
|rank R - rank V| <= s. Assignment to witnessing embeddings gives s <= d.
This counts the *additional conditions*, not the rank of V.

In the triangle case q(uv)+q(uw)+q(vw)=0, so the three rows have rank at most
two and an explicit product (uvw)^2. The natural square roots of this
polynomial identity agree under theta -> m and give a trivial congruence
by themselves. Other dependencies or square-root choices need their own
success analysis; the identity is not a proof that the entire factoring
method can never succeed. Squares u^2 have the analogous limitation.

### Smoothness and cost qualifications

The algebra above does not assume u or v is smooth. Under Card C’s *fully
smooth* rational/ideal admission, however, that property is inherited:
g(m) = u(m)v(m) is a product of nonzero integers, and the principal ideals
of u(theta),v(theta) are integral because f is monic. Their nonnegative
valuations add. No outside rational prime or prime ideal can disappear in
the product. Thus an admitted fully smooth g supplies fully smooth u and v
on the same support convention. Norm multiplicativity gives the analogous
integer-norm statement. Bad-prime handling and sufficient square conditions
still have to be done correctly.

Primitive quadratic factorization itself needs only an integer discriminant
square test, gcds and exact division, at poly(log H) bit cost, not a hidden
integer factorization oracle. Recovering the rational roots and clearing
denominators produces the factors in (3). Their values and norms have
polynomial-in-n bit length. Decomposing those values into rational primes
and ideals remains charged work.

If the policy admits unsmooth u once and cancels it across pairs, it can
indeed avoid factoring u for even combinations. Its remaining arithmetic
is the ordinary linear v_i problem with (5), plus the cost of finding u
and the chosen v_i. If unsmooth v_i are also retained, all their residual
dependencies must be represented. That is a different partial-relation
policy from the two-sided full-smoothness probability used by Card C.

For the explicit full cube scan, enumerating the containing ordinary linear
square would take H^2 poly(n) candidate work. The quadratic scan costs
H^3 poly(n) and obtains no new reducible square-class span outside those
linear factors. This is a precise containment/comparison of candidates,
not a theorem that every possible biased generator of those factors costs
H^2 or that every linear combination yields an equally useful gcd.

## 5. Norm gain and the conditional constants

Put A = H(f), with f monic of degree d, and m ~ N^(1/d), A = O(m).
From M(f) <= sqrt(d+1) A and 1+r+r^2 <= 3 max(1,r)^2,

\[
 |\operatorname{Res}(f,g)|
  =\prod_j|g(\alpha_j)|\le(3H)^d(d+1)A^2,
 \qquad |g(m)|\le3Hm^2.                    \tag{7}
\]

Passing a real-root slab multiplies the first bound by epsilon_lambda
(or E_lambda). Thus, writing S = t^(2/3) ell^(1/3), its algebraic logarithm
is bounded by

\[
 \big(a\delta+(2-\lambda)/\delta+o(1)\big)S.
\]

The rational logarithm is at most (2/delta+o(1))S. Therefore the combined
coefficient is a delta + (4-lambda)/delta, agreeing with Card C’s
2(1+eta)/delta + a delta when eta = 1-lambda/2. The three real-slab eta
values are 1/2, 1/4, 0. The rounding factor below two is lower order.

A genuinely nonreal disk reduces both conjugate factors, so its formal
mapping is instead eta = 1-lambda. More generally a total damping exponent
Lambda, counting both members of a nonreal pair, gives eta = 1-Lambda/2.
Negative algebraic upper exponents cannot be interpreted as negative-size
integers: since f is irreducible of degree > 2, a nonzero g has a nonzero
integer resultant. If the entire bound tends below 1, the candidate set is
empty. Do not extrapolate a smoothness formula past that feasibility check.

Within the original unproved model, let K = (r-1)(1+eta) > 0.
The no-selection-loss feasibility condition is
ra >= b + (K/delta+a delta)/(3b). Minimizing in delta gives
delta^2 = K/a and K/delta+a delta = 2 sqrt(Ka). Put x = ra.
Feasibility then requires
b^2 - xb + (2/3) sqrt(Kx/r) <= 0. Its discriminant must be nonnegative,
so x^3 >= 64K/(9r). Since c >= x, this is a lower bound on c within the
model. Equality is attained at b = x/2, hence ra = 2b, proving

\[
 c^3=64K/(9r).
\]

For unselected quadratics eta=1, r=3, this is 256/27, worse than ordinary
GNFS’s 64/9. For selected quadratics it is 128(1+eta)/27. The checked
comparison c_C^3 = (92+26 sqrt(13))/27 gives precisely eta <
(92+26 sqrt(13))/128 - 1, about 0.4511. The exact Coppersmith constant and
its square-congruence scope were checked in
[Lee–Venkatesan, Remark 4.31](https://arxiv.org/html/1805.08873v1).
The [original Coppersmith publication record](https://research.ibm.com/publications/modifications-to-the-number-field-sieve)
confirms reuse of smoothness computations across polynomials.

These are conditional model calculations, not bounds achieved by the
selector. For the irreducible branch the candidate-count premise is false.
For the reducible branch the H^3 raw tuple count is not H^3 independent
quadratic opportunities; multiplicative factors and their correlations must
replace the generic norm/smoothness model. The deterministic norm upper
bound alone supplies neither a typical-size distribution nor independence.

## 6. Setup, certification, enumeration and completion costs

The real-root reference enumerator is adequate for its claimed selector
upper bound. Given an actual integer monic f, construct isolating intervals
for its real roots; determine their signs exactly. Set k by the integer
comparisons 2^(kqd) <= N^p < 2^((k+1)qd), with a binary search, for
lambda = p/q. The comparisons have polynomial operand width; evaluating
a floating-point logarithm is unnecessary.

At a real root of sign s, slab membership with E=2^(-k) is equivalent to
both H(1+sX+X^2) +/- 2^k g(X) being nonnegative there. For a nonzero one
of these polynomials Q, height K0 <= (2^k+1)H, irreducibility and d>2 give
gcd(f,Q)=1. With R0=A+1,

\[
 |Q(\alpha)|\ge(3K_0R_0^2)^{-(d-1)}
\]

by the nonzero integer resultant and the upper bounds at the other roots.
The derivative bound |Q'| <= 5K0 R0 on the relevant real interval verifies
the H008 interval width and sign test. The identically zero Q is handled
exactly. Root signs likewise require certified isolation, not a guessed sign.
The required number of bits is O(d(k+log H+log(A+1))).
[Sagraloff–Mehlhorn, Theorems 2–3](https://arxiv.org/pdf/1308.4088v2)
give polynomial-bit real-root isolation/refinement; the integer-polynomial
refinement bound is soft-O(d(d^2+d log A+p)) for requested p-bit intervals.
The general reducible-f fallback needs square-free gcds and actual factor
heights as stated in H008; it does not interpret a reducible quotient as a
single number field.

The exact raw cube count is (2H+1)^3, including zero, imprimitive,
reducible, wrong-sign and failed-slab tuples. There are at most d membership
tests per tuple at the widest tolerance, or 3d if tags are recorded.
Resultants against f are determinants of size at most d+2 with polynomial
bit length, computable by exact polynomial-bit elimination per tuple.
The total selector cost is H^3 poly(n), a genuine cost even if no tuple
survives. Root data and tuple streaming are polynomial space; storing all
reducible survivors would instead require their actual O(H^2 log H) count
times record size. The polynomial-space accepted-list statement in H008
uses its irreducible filter and cannot be transferred to the broader set.

The complex-disk count is proved without an implementation. The displayed
real Q-sign procedure and cited real-root routine are not themselves a
specified complex-disk enumerator. Certified complex membership, including
its algebraic comparisons involving |alpha|, would need its own description
and charge before making an implementation claim. It is unnecessary for
the distribution-free count or for the real-selector rejection.

No cheaper lattice enumerator has been supplied or analyzed. A complete
algorithm must still add polynomial/field selection, rational and ideal
bases, smooth/cofactor processing, bad-prime and character data, filtering,
matrix storage and algebra, algebraic square roots, gcds and restarts. For
J separate full scans, the displayed implementation pays J(2H+1)^3 visits
plus setup, even if it finds only Jd irreducible elements. A shared-cost
multiple-field algorithm requires a different explicit analysis.

For a completed trial of cost T with proper-factor success probability
sigma_N, any independent-restart expected-cost assertion must charge
T/sigma_N. The revised selection bias has no established lower bound on
sigma_N. The possibility that a few exceptional rows are already dependent
does not supply a useful-splitting probability, and is not contradicted by
the d-row result.

H008’s conditional large-root observation is also correct: for |alpha| >=
2H+2 and a2 != 0, |g(alpha)| > |alpha|^2/2 prevents (1) at epsilon <
1/(6H). Existence of such a root is not guaranteed for every base-m f.
No part of the accepted separation theorem depends on that observation.

## 7. One specific next mechanism outside the rejected hypothesis

**Next proof target: a global-resultant tail for irreducible quadratics,
with no per-embedding thin-slab condition.** Fix the same f,H and take
eta = 2/5. Define the integer baseline

\[
 C_0=(3H)^d(d+1)A^2
\]

and enumerate the complete coefficient cube once. After the primitive,
positive-leading and irreducible filters, compute Rg = |Res(f,g)| and
retain precisely when

\[
 R_g^{5d}N^6\le C_0^{5d}.                   \tag{8}
\]

This exact integer test imposes Rg <= C0 N^(-6/(5d)), the algebraic target
H^d N^(4/(5d)) times the explicit lower-order factors of (7). It corresponds
to eta=2/5, below the comparison threshold. It does not require any one
evaluation to have the much smaller relative size N^(-lambda/d).
An evenly distributed total damping of N^(-6/(5d)), for example, asks for
per-root damping N^(-6/(5d^2)), which has log scale log H, instead of the
larger t/d scale that forced H008’s separation. This observation is an
explanation of a changed hypothesis, not a construction of such g’s.

There is no unpriced search primitive in (8): the proposed selector costs
(2H+1)^3 poly(n) visits and bit work, including every rejection; the
exponentiated comparison still has polynomial-in-n operand width. It can
stream outputs. Computing roots or a lattice is unnecessary. This is a
fully specified *selector and counting question*, not a new factoring
algorithm or an asserted plentiful tail.

The next decisive analytic obligation is a lower bound on distinct
survivors of (8), with a joint rational/ideal smoothness and useful-row
model. Under Card C’s otherwise unchanged conditional costs, a tail
fraction L[1/3,-tau] would need

\[
 3a\ge b+\tau+
 \frac{14/(5\delta)+a\delta}{3b},\qquad
 \max(3a,2b)<c_C.                           \tag{9}
\]

A count upper bound incompatible with (9), or a demonstrated larger search,
processing or dependency cost, rejects this replacement. A lower count
alone would not prove smoothness or useful factor extraction. Generic
smoothness probabilities cannot silently stand in for joint data.

Even the downstream costs can be bounded conservatively: enumerating primes
through B and trial-dividing the rational values and integer norms of all
survivors costs at most H^3 B poly(n), before ideal and square-root work.
That yields a generation/processing exponent 3a+b, not the optimistic 3a
in (9). Any attempt to claim the smaller cost must actually specify and
price the sieving/batch processing that saves this factor. This review
offers (8) as the next exact counting mechanism, with its unavoidable
known scan cost and its unresolved completion costs exposed.

No experiment is run here. If a finite diagnostic of (8) is authorized
later, it must first freeze f construction, N/H/d values, all caps and
rejection criteria, retain every failure and source hash, and stay within
the required 60-second cap. Larger parameter sweeps are not implied by
this handoff.

## 8. Evidence, sources and handoff limits

All nine local input/report hashes in H008-resultant-provenance.json matched
when first recomputed in this review, including the complete original H008
report. At final provenance capture, research/STATE.md had changed in the
shared workspace; this reviewer did not edit it. Its initial and final
hashes are both retained, and the other eight still match. The mathematical
review uses the original H008 and Card C versions, which remain unchanged.
Hashing W001-baselines.md verifies its recorded bytes; this
review does not claim to have independently reviewed that entire ledger.
The sources directly used here were opened through the web tool:
Stevenhagen’s chapter, Sagraloff–Mehlhorn v2, Lee–Venkatesan v1, the original
Coppersmith publication record and Abbott’s research paper.
[Bai–Brent–Thomé v1, §§2.4–3](https://arxiv.org/pdf/1212.1958v1)
was also checked for the cited polynomial-optimization context; it
does not establish a density theorem for this selector. An attempted AMS
Mignotte PDF retrieval returned an internal error and is **not** claimed as
verified text; the height argument above is supplied explicitly and checked
against Abbott §3.2. No external source is evidence of novelty for the
elementary lemmas in this review.

The review’s input hashes, checked URLs, failed source retrieval and final
report hash are retained in `H008-review-provenance.json`. This is
documentation provenance, not an experiment. Experimental allocation was
zero seconds, with no trials, seeds, successes, failures or censored runs.
No code, Lean, shared state or original report was changed; no packages,
delegation, commit, publication, scheduler or giant experiment was used.
The project code checks were not run because this is a report-only proof
review with no implementation change.

The parent can accept the original restricted lemma as independently
reviewed informal mathematics and archive the three proposed single-root
tolerances as failing their irreducible quadratic population premise.
For the broader Card C, record the reducible branch as a reduction to
bounded-height linear factors with the exact parity qualifications above.
It has not supplied a new complexity improvement, but it is not ruled out
by an erroneous d-row or d-rank bound. Any major use of the new extension
should itself undergo the project’s independent-review criterion.

**Best supported result:** an exact obstruction for this particular
irreducible quadratic selector, plus a proved structural and dependency
reduction for its reducible extension. **Next action:** audit the exact
global-resultant tail (8) at its charged scan cost, beginning with its
counting obligation rather than assuming rare lattice points are available.
This is not a lower bound on factoring and establishes no new factoring
bound. Verified improvement remains **NONE**.
