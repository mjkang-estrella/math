# H031 — Adjacent rotations and the actual mass of productive packets

2026-10-08. **Scoped algebra and per-trial bound accepted after independent
review and local completions. Verified COMPLETE classical factoring complexity
improvement: NONE.**

Coordinator update: the [independent review](H031-independent-review.md) is
adopted with the execution-order, localization, cost and prior-art clarifications
below. The identical [submitted draft](H031-submitted-draft.md) preserves the
original bytes named by the original manifests. This current report is a finite
on-paper construction, not a tested implementation or a machine refinement.
See the [disposition](H031-disposition.md) for acceptance and unresolved work.

**Disposition:** close the selected adjacent-rotation realization as a proposed
new complexity improvement. It is a finite on-paper, fully charged instance
of the existing multiple-field reconstruction mechanism, with an unproved
useful-output law. This is neither an impossibility result for these rotations
nor an exclusion of other coupled-field constructions. No computation of the
proposed algorithm, finite mathematical experiment, sweep, benchmark or replay
was performed.

The concrete trial below uses

    f_1=f_0+t(X-m),  f_2=f_0+(t+1)(X-m),

where every parameter and the distribution of t are specified from N. It
constructs one joint dependency, takes at most two actual algebraic roots,
and tests the resulting packets. Conditional on the retained data, its exact
success probability is

    0,                         if the productive character is trivial;
    2^(-c_t-1),                otherwise,                         (0.1)

where c_t is the codimension of the dependencies which are actual squares in
both fields inside the sampled parity kernel. This formula counts nonsquare
root attempts as failures. It does **not** give a positive lower bound: neither
small c_t nor a nontrivial productive character has been proved for this law.
The deliberately elementary complete trial implementation has the conservative
upper bound L_N[1/3,3+o(1)], with no finite expected successful-factoring bound
unless its actual success probability is positive. This is not the
Lee–Venkatesan randomized sampler or its leading constant.

## 1. Dependencies and exact prior-art boundary

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, current STATE, the complete H031 brief/intake, H027's
disposition/prior-art note, and all 866 lines of the corrected H028 report
plus its disposition. The five hashes supplied in the brief matched:

- H031 intake: `1710ce436ebf3fd5aac0011b0041ac9d1f7099c47ab5facac8f50c225504f51f`.
- H031 brief: `8486e3a488d306661e8a27cb7dc95373d9254f1b087851dad6919e4b245b0078`.
- H027 disposition: `9c5c87da61246748592d23d2bd84f17735b35981e71efb3fe91c837d66eea6db`.
- Corrected H028 report: `5f6cbbdc021c2fa1772442339920745243529dd6518f7367ea81411714a66f50`.
- H028 disposition: `96a78eb16fa4cc0bcae3c04f268ea47e8e069e79219a73d81aa3b7eef3fffc54`.

These supply accepted accounting and reconstruction scope, not an actual
useful-yield law. H030's draft, sources and task handle were not inspected;
the checkpoint's description of its ownership was respected.

Primary sources inspected, with archived bytes identified in
[provenance](H031-roots-provenance.json):

1. **Don Coppersmith, “Modifications to the Number Field Sieve,” Journal of
   Cryptology 6 (1993), 169–180, DOI 10.1007/BF00198464.** Sections 2–3,
   especially pp. 174–177, already give this rotation family, shared rational
   columns, separate algebraic/character blocks, fieldwise roots and a global
   rational square. Figure 1 on p. 175 was also inspected visually. Page 170
   labels the smoothness-based estimates heuristic; p. 177 charges roots
   across participating fields. No new parity cancellation is claimed here.
   [Primary PDF](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf),
   [archive](H031-roots-source-coppersmith1993.pdf).
2. **Jonathan D. Lee and Ramarathnam Venkatesan, “Rigorous Analysis of a
   Randomised Number Field Sieve,” arXiv:1805.08873v1.** Theorem 2.1 concerns
   square congruences. Theorem 2.3's productive Blum-semiprime result assumes
   Conjecture 7.82. Section 7 defines the productive character and its
   independence requirement; Remark 7.85 extends the mechanism to multiple
   fields. Definition 4.28 specifies a different polynomial distribution.
   The terse semigroup wording in Remark 7.85 is **not** evidence of an
   omitted global parity condition or a new gap. Coppersmith's explicit
   reconstruction resolves that point directly.
   [Primary text](https://arxiv.org/html/1805.08873v1),
   [archive](H031-roots-source-lee-venkatesan-v1.html).
3. **Peter Stevenhagen, “The Number Field Sieve,” Algorithmic Number Theory,
   MSRI Publications 44 (2008), §§6–10**, especially pp. 93 and 97–98:
   ideal parity, actual element squares, the derivative order multiplier,
   and extraction are separate obligations.
   [Primary chapter](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf),
   [archived text](H031-roots-source-stevenhagen2008.txt).
4. **A. K. Lenstra, “Factoring polynomials over algebraic number fields,”
   Proceedings of EUROCAL 1983, pp. 245–254**, Algorithms 4.1/4.4 and
   Theorem 4.5 on p. 253. This supplies a terminating field-polynomial
   factorization algorithm, including small-prime selection, finite-field
   work, lifting and lattice reduction. The displayed arithmetic-operation
   and operand-width bounds were checked on the page image, not only OCR.
   It will be applied to a degree-two polynomial over each field, not to
   integer factorization of N.
   [Primary record](https://ir.cwi.nl/pub/2541),
   [primary PDF](https://ir.cwi.nl/pub/2541/2541D.pdf),
   [archive](H031-roots-source-lenstra1983.pdf),
   [inspected page](H031-roots-lenstra-p253.png).

This is a targeted source check, not an exhaustive novelty search or an audit
of the complete analytic proofs in those papers. The submitted deductions now
have independent review at their stated scope; the opening coordinator note
identifies the adopted completions.

## 2. One exact input-only pair law

The claimed input domain is only N=pq with distinct primes p,q both 3 modulo 4.
The program receives N, never p,q or a certificate describing their residues.
Let n be its bit length, and define using integer comparisons:

    k = ceil(log_2 n),
    d = largest odd integer >=3 with d^3 k <= n,
        or d=3 if there is no such integer,
    e = least positive integer with e^3 >= n k^2,
    E = B = 2^e,
    Q = 2^(2k),
    m = floor(N^(1/d)).                                  (2.1)

Integer roots in (2.1) use binary search with exact powering. For the finite
exceptional range where m<2d, this trial uses ordinary trial division through
floor(sqrt(N)) and returns the verified split. Charge that entire branch.
The inequality m/d -> infinity shows that this branch has only finitely many
inputs and does not determine the asymptotic bound. It is not a free fallback
used after unsuccessful relation collection.

Otherwise expand N in base m:

    N = m^d + sum_(j=0)^(d-1) c_j m^j,  0<=c_j<m,
    f_0(X)=X^d+sum_(j=0)^(d-1)c_j X^j.                  (2.2)

This really is monic of degree d. In fact m^d<=N<(m+1)^d and
(1+1/m)^d<=exp(1/2)<2 when m>=2d. Thus the leading digit is one.

Read exactly 2k uniform random bits to obtain t uniform on {0,...,Q-1}, and set

    f_1=f_0+t(X-m), f_2=f_0+(t+1)(X-m), g=1.           (2.3)

Both polynomials have f_i(m)=N and are different as polynomials. There is no
assertion that they always define nonisomorphic fields. Their exact heights
are the maxima of the unchanged digits, 1, and

    |c_0-i m|, |c_1+i|,       i=t or t+1.

Consequently each height is at most

    H=(Q+1)m+Q.                                         (2.4)

There is no minimization over an uncharged menu. Each trial attempts precisely
two fields. Factor both defining polynomials over Q by a fixed deterministic
polynomial-time rational-polynomial algorithm before checking reducibility.
Order monic irreducible integer factors by degree, then coefficient tuple.
Inspect reducible-factor gcd(h(m),N) in field order, then this factor order,
returning the first actual proper gcd. If at least one field is reducible and
none of these tests split N, declare the pair failed. Values 1 or N do not
count as splits. With both fields irreducible, process derivative gcds in field
order, stopping on a proper split or the specified failure. Use increasing
base primes, the stated lexicographic pair order, field order, deterministic
exact algebra routines and leftmost matrix pivots thereafter. Root sign can
be fixed arbitrarily because the character below is sign-independent.

For each irreducible f_i, write K_i=Q[X]/(f_i), alpha_i=X mod f_i. Compute
its discriminant Delta_i and D_i=f_i'(m). Test gcd(D_i,N). A proper gcd is
success, gcd=N is pair failure, and gcd=1 permits the root reduction below.
No maximal order, discriminant factorization, class group or unit group is
computed or assumed available. The coefficient and discriminant bit lengths
are polynomial in n; all these attempted operations are charged.

The exact coupling gives useful bookkeeping identities but no sign law:

    Res(f_1,f_2)=Res(f_1,X-m)=(-1)^d N=-N,
    f_2'(m)=f_1'(m)+1.                                 (2.5)

The resultant follows by multiplying alpha-m over the d roots of monic f_1.
It is the already known composite N up to sign, not its factorization.
In K_2 one has f_1(alpha_2)=m-alpha_2, which is nonzero. Thus the formal
assignment alpha_1 -> alpha_2 is not a field homomorphism; the shared modular
root supplies no transport of field roots. These statements neither exclude
other isomorphisms nor assert independence of the two fields.

## 3. A completely specified paid relation stream

After successful field setup, sieve the integers up to B to construct the
common list of primes b_1,...,b_s. Test gcd(b_j,N) for each. A proper gcd
finishes the trial. In this branch all remaining base primes are units.
Let

    R_cap=(2d+1)s+1.                                    (3.1)

Enumerate every (a,b) with 1<=a,b<=E in lexicographic order. Discard
nonprimitive pairs after their gcd computation. For a primitive pair set

    r(a,b)=a+bm>0,     u_i(a,b)=a+b alpha_i,
    G_i(a,b)=Norm_(K_i/Q)(u_i)=(-b)^d f_i(-a/b).         (3.2)

Test gcd(r,N). Return a proper gcd, discard a row if the gcd is N, and
otherwise trial-divide r by **all** base primes, extracting full valuations.
Keep it as a rational survivor only when the residual is one. This is a
simple exact smoothness procedure, with its full cost below; it is not an
assumed fast smoothness oracle.

For each rational survivor evaluate both homogenized integer norms by Horner
arithmetic, test gcd(|G_i|,|Delta_i|), and discard the corresponding field row
if that gcd is not one. For each remaining norm, extract full valuations by
trial division over the same base. Admit the row exactly when the absolute
residual is one. Negative norms retain their sign as metadata; no norm-sign
test is substituted for a field-square test. For accepted irreducible fields
u_i and G_i are nonzero.

Retain only the first R_cap admitted rows in each field. Continue the specified
scan, pricing even admissible rows discarded after that cap. Let R_i be the
actual retained counts and R=R_1+R_2. Empty or unfilled quotas do not get replaced
by imagined relations or another field. Identical values are allowed with their
original (i,a,b) provenance; no independent-rank credit is assigned to them.
There is no deduplication or filtering algorithm whose lifting map is hidden.

Each prime ell dividing an admitted norm is good: ell does not divide Delta_i.
Also ell cannot divide b, since the pair is primitive and f_i is monic. Attach
its full valuation to the degree-one ideal label

    (i, ell, -a/b mod ell).                             (3.3)

This is the unique ideal above ell dividing a+b alpha_i, and its valuation
is the integer ell-valuation of G_i. Separate field labels are indispensable.
Sort the observed labels and assign column numbers, charging the records and
accesses. At most d s labels occur in either field. There is no need to build
all root tables in advance; the rational prime list is the only common base
construction. Excluding the bad-prime rows is exact but has no proved
favorable effect on supply.

The coupling is visible in the actual integers:

    G_2(a,b)-G_1(a,b)=b^(d-1)r(a,b),                    (3.4)
    r <= (m+1)E,    |G_i| <= (d+1)H E^d.               (3.5)

Here d is odd, so the sign in (3.4) is positive. These are identities and
height bounds. Neither implies a smoothness rate for this generated stream,
nor a favorable conditional law after any of the stated rejections.

## 4. Match parities by a joint matrix, then compute the roots

Orient matrices as maps on the vector of selected rows. Let P_i be the
s-by-R_i rational valuation-parity matrix and A_i the at-most-ds-by-R_i
good-ideal valuation-parity matrix. Construct

             [ P_1  P_2 ]
    M_t =    [ A_1   0  ],     V_t=ker_F2 M_t.          (4.1)
             [  0   A_2 ]

This realization uses **zero extra algebraic character columns**. It will
actually test squarehood; failures are part of its success probability.
There is no claim that ideal parity is sufficient. Omitting the character
filter is not an improvement and may make useful probability very small.

Use ordinary dense binary Gaussian elimination with a fixed leftmost-pivot
rule. Store the reduced equations and the original column-to-row mapping.
Set every free variable to an independent uniform bit and solve for pivots.
This samples v=(v_1,v_2) uniformly from V_t, including zero. It assumes no
parity uniformity in the original stream. RREF/back-substitution already
provides every needed lift to actual rows.

For clarity, if L_i=ker A_i and W_i=P_i L_i, then (4.1) is exactly the set
of pairs in L_1 x L_2 with equal rational image. Its map to W_1 intersect W_2
is onto, with kernel

    ker(P_1 restricted to L_1) x ker(P_2 restricted to L_2).

This explains how intersections and all their fibers are represented without
a birthday search. It gives neither a favorable intersection dimension nor
actual roots of any lift. No basis of packets is constructed.

For the sampled subset form, by exact multiplication modulo f_i,

    U_i=product_(selected field-i rows) (a+b alpha_i),
    r_i=product_(same rows) r(a,b),                     (4.2)

retaining the complete exponent vector for the positive integer r_i. An empty
product is one. Factor T^2-U_i in K_i[T] using Lenstra's specified algorithm.
A linear factor gives an actual root w_i; if the polynomial is irreducible,
declare the trial failed. The algorithm decides nonsquareness and terminates;
it is not enumeration over unbounded potential roots. Perform at most one
such factorization for each field and verify w_i^2=U_i exactly. A nonsquare
on the first side may stop the second call early, without a success credit.

Because U_i is integral, w_i is integral. Put A_i=Z[alpha_i] in this paragraph
and delta_i=f_i'(alpha_i). The map alpha_i -> m extends to
A_i[delta_i^(-1)] -> Z/NZ because D_i is a unit. No map on all of K_i is
asserted. The trace-dual identity A_i^vee=delta_i^(-1)A_i gives
delta_i O_(K_i) subset A_i, so the standard order multiplier gives

    h_i=f_i'(alpha_i) w_i in Z[alpha_i].

Compute this element, check its integer power-basis coefficients and the
identity h_i^2=f_i'(alpha_i)^2 U_i, and evaluate

    x_i=h_i(m) D_i^(-1) mod N.                         (4.3)

First multiply and cancel rational denominators in the exact field to obtain
the integral h_i coefficients; never invert a scalar output denominator or
the field discriminant modulo N. The D_i inverse was justified by the actual
setup gcd, not by assuming every denominator failure yields a factor. Then
x_i^2=r_i mod N. Verify that congruence and gcd(x_i,N)=1. Positivity and the
factorization of r_i are literal properties of this construction. The factored
representation avoids a needless decimal/integer expansion; its exponent
bit lengths and all modular exponentiations are still charged.

There are now two actual packets with equal rational parity. Apply §5 and
return a factor only after testing 1<gcd(rho-1,N)<N and divisibility. Otherwise
return failure. In particular identical packets are not counted as useful:
opposite normalized Jacobi signs themselves certify the necessary distinction.
An empty packet may participate, so a split achievable entirely in one field
is credited as success but is not evidence of a benefit from coupling.

## 5. Packet normalization and the exact failure-inclusive sign law

### 5.1 The organizing identity, with the sign restriction respected

For an actual packet r_i=product_j b_j^(a_ij), put

    v_ij=a_ij mod 2,
    c_i=product_j b_j^floor(a_ij/2) mod N,
    z_i=x_i/c_i mod N.

Every divisor is a unit. Then z_i^2=product_j b_j^(v_ij) mod N. Since
(4.1) forces v_1=v_2=v, rho=z_1/z_2 satisfies rho^2=1. Write J for the
Jacobi symbol modulo N. For distinct Blum primes the four CRT roots of one
are (+,+), (-,-), (+,-), (-,+); J takes respectively 1,1,-1,-1 because
(-1/p)=(-1/q)=-1. Thus

    J(z_1) != J(z_2)  <=>  J(rho)=-1
                      <=>  gcd(rho-1,N) is proper.     (5.1)

This proves the intake criterion for its stated family. It is not a sampler.
All r_i here are positive. For signed products one would need the sign in the
matching data and a new normalization argument; replacing a negative r by
|r| without changing x is invalid. That issue is avoided by (3.2), not assumed
away in a signed stream.

There is an exact comparison to ordinary global rational reconstruction. Let

    Y=product_j b_j^((a_1j+a_2j)/2) >0.

Then Y=c_1 c_2 product_j b_j^(v_j), as an integer before reduction, and

    x_1 x_2/Y = z_1/z_2 = rho mod N.                   (5.2)

So matching two normalized packets computes precisely the productive root
ratio of the familiar global-rational-square construction.

### 5.2 Which dependencies actually have roots?

Fix a t reaching the matrix stage and all its deterministic retained data.
Define the mathematical subspace

    S_t={v in V_t: U_1(v_1) is a square in K_1
                    and U_2(v_2) is a square in K_2},
    c_t=dim(V_t)-dim(S_t).                              (5.3)

S_t is not supplied to the algorithm as an oracle. Its sampled membership is
decided by the two paid root calls. It is a subspace: for any row subsets
v,w, their symmetric-difference products obey

    U_i(v_i+w_i)=U_i(v_i)U_i(w_i)/U_i(v_i intersect w_i)^2.

Equivalently, row multiplication induces a homomorphism to
K_i^*/K_i^*2. Taking both kernels and intersecting V_t gives (5.3).
Even ideal exponents, all unit and class obstructions, and field-root
nonexistence are thereby distinguished exactly. No bound on c_t is inferred
from the number of rows, fields, or generic quadratic characters.

For v in S_t define

    chi_t(v)=J(x_1(v_1)x_2(v_2)/Y(v)).                  (5.4)

This does not depend on the two field-root signs, since J(-1)=1. It is a
character on S_t. To justify reduction without an arbitrary field-fraction
map, let C_i be the product of coordinate occurrences common to v_i and w_i.
For s=v+w and some epsilon_i in {+1,-1}, the roots satisfy the cleared identity

    delta_i C_i h_i(s) = epsilon_i h_i(v) h_i(w)

entirely in Z[alpha_i]. Reduce this equality first. The image r_Ci of C_i is
a product of retained rational units, so x_i(s)=epsilon_i x_i(v)x_i(w)/r_Ci
is a legitimate modular division. Positive global roots satisfy
Y(s) r_C1 r_C2=Y(v)Y(w). The overlap factors therefore cancel, giving
rho(s)=epsilon_1 epsilon_2 rho(v)rho(w). Since J(-1)=1, this proves
chi_t(v+w)=chi_t(v)chi_t(w), including empty subsets and duplicate occurrences.

If chi_t is nontrivial, exactly half of S_t has chi_t=-1. Uniform sampling of
V_t lands in S_t with probability 2^(-c_t). Therefore (0.1) is the exact
probability of a proper split on this fixed matrix, including all nonsquare
root attempts. If chi_t is trivial it is zero. Zero-dimensional kernels,
empty packets and nonproductive dependencies remain in the denominator.

Here the root routines are exact and uncapped. A proposed capped, approximate
or different extraction routine would have an additional success event; (0.1)
must not be imported for it without a proof of completion and correctness.

### 5.3 Actual complete-trial probability

Use the fixed execution order in §2. For its nonexceptional branch, let A_N
be the set of t values whose
deterministic preprocessing/stream gcd tests already return a proper split.
Let G_N be the disjoint set reaching the matrix stage with valid fields,
maps and retained data. Other t values fail. Then the specified trial has

    sigma_N = |A_N|/Q
            + (1/(2Q)) sum_(t in G_N)
                  2^(-c_t) 1_{chi_t is nontrivial}.     (5.5)

The small-input trial-division branch has probability one and its separately
charged cost. Formula (5.5) averages over the actual finite pair law, not over
an assumed distribution of fields or abstract characters. A rare successful
field filter contributes its actual weight, never weight one. Truncation,
missing relations, duplicates and bad-prime rejections affect the actual
V_t,S_t,chi_t appearing here. No independent restart theorem is needed to
derive this single-trial identity.

A common unit mask on both normalized roots leaves their ratio unchanged.
Replacing either field root by its other sign changes rho at most to -rho;
J(-rho)=J(rho). Neither operation makes (5.5) positive. Distinct fields or
independent choices of the two global signs do not supply independent CRT
signs. Large ambient character spaces do not identify the law of chi_t.

## 6. Full cost and storage ledger for this realization

All bounds here are classical bit-operation bounds with ordinary schoolbook
integer arithmetic and explicit records. They are conservative upper bounds,
not timing predictions, optimal costs or lower bounds. Polynomial factors in
n include index widths, polynomial degrees and the explicitly bounded scalar
widths. Fixed deterministic loop orders and sequential scans suffice; no
unit-cost access to arbitrarily wide addresses is assumed.

Write w for a bound on the bits of a rational value or individual norm. From
(2.4),(3.5),

    w=O(log(d+1)+log(H+1)+d log(E+1))=poly(n),
    log|Delta_i|=O(d log d+d log(H+1))=poly(n).          (6.1)

The maximum number of retained rows and matrix constraints is

    R <= 2((2d+1)s+1)=O(dB),
    D_mat <= (2d+1)s=O(dB),
    W <= R poly(n),                                    (6.2)

where W is the actual input nonzero count. These are pathwise caps, valid
even when every tested integer is smooth. They are not expectations of quotas.

The complete ledger is as follows.

1. **Pair generation and maps:** n and the integer parameters, base-m digits,
   both attempted defining polynomials, their full rational factorizations,
   reducible-factor evaluations, discriminants and derivative gcds cost
   poly(n). Exactly 2k bits choose t. Every failed field attempt is included.
2. **Common base:** sieve all primes through B, store their values and perform
   all gcds with N. Cost and storage are B poly(n). Separate ideal labels are
   constructed from the retained/processed records, with no maximal-order
   or discriminant-factorization oracle. No extra character preparation is
   hidden; this trial deliberately prepares none. One sequential implementation
   emits j^2,j(j+1),...<=B for each integer 2<=j<=sqrt(B), externally sorts
   these O(B log B) composite records, and complements their distinct values
   in [2,B]. Thus the prime-construction bound does not rely on free random
   access to a B-cell sieve array.
3. **Entire stream:** at most E^2 pairs incur primitive/unit checks and rational
   trial division; at most 2E^2 norms are evaluated and processed. Testing
   every base prime with full valuation extraction costs
   O(E^2 B poly(n)). Horner evaluations, bad-prime gcds, rejects, late cap
   discards and their status records are included. A work tape streams the
   rejected data and stores only bounded retained records. Its cost counts
   rejected input bits even if R=0.
4. **Labels and matrix:** sorting all retained labels and constructing the
   actual dense matrix costs O((R+D_mat)^2 poly(n)). Dense binary elimination
   costs O(D_mat R min(D_mat,R) poly(n)); its memory is O(D_mat R poly(n)).
   Pivot/free-column records map directly to original triples. Uniform free
   bits, back-substitution and reading each selected relation cost at most
   O((D_mat R+R) poly(n)). There are no uncharged joins, intersection bases,
   filtered-matrix lifts or Krylov retries.
5. **Each algebraic product:** multiplying by one linear factor modulo a monic
   f_i increases the maximum coefficient by at most E(H+2). For a subset of
   ell_i rows, the reduced U_i therefore has coefficient bit length at most
   1+ell_i log_2(E(H+2)), up to integer rounding. In particular this is
   O((R_i+1)poly(n)), which is **not** polynomial in n alone. Sequential exact
   multiplication has a conservative O((R_i+1)^3 poly(n)) bit bound.
6. **Each root call:** apply Lenstra's Algorithms 4.1/4.4 and Theorem 4.5 to
   T^2-U_i, with defining polynomial f_i. For coefficient bit length h the
   theorem gives O((h+1)poly(n)) arithmetic operations on integers of
   O((h+1)poly(n)) bits after fixing the polynomial degree to two. Schoolbook
   arithmetic gives O((h+1)^3 poly(n)) bit work. This includes chosen primes,
   their construction, finite-field factorizations, lifting precision,
   denominators, lattices and nonsquare determinations. Substitution of the
   preceding bound gives O((R_i+1)^3 poly(n)) per call. There are at most two
   calls. No field roots for a whole dependency basis are being credited as
   one call.
7. **Verification and output:** retain the full rational exponent sums, form
   the derivative multipliers, verify the field identities, evaluate and
   invert the unit denominators, verify packet congruences, normalize, compute
   Jacobi symbols and perform proper gcd/divisibility tests. Exact root
   coefficient/denominator widths are covered by the previous call bound;
   modular values have n bits. This remaining work fits the same conservative
   cubic bound. Full exponent-vector and provenance storage is paid.

For precision in item 6, rename Lenstra's polynomial degree nu=2, field degree
d, input denominator b_den=1, and coefficient maximum f_max=max(1,|coeff U_i|).
His defining F is our f_i, with |F|<=sqrt(d+1)H; his common output denominator
is D_L=|disc(F)|, not the modular derivative D_i. The displayed theorem gives

    arithmetic operations:
      O(nu^6 d^6 + nu^5 d^6 log(d|F|) + nu^5 d^5 log(b_den f_max)),
    operand bit length:
      O(nu^3 d^3 + nu^2 d^3 log(d|F|) + nu^2 d^2 log(b_den f_max)).

Use 1+log at small values. Both are O((h+1)poly(n)) here. The auxiliary prime's
numerical size is O((h+1)poly(n)), not necessarily poly(n). Prime enumeration,
finite-field work and lifting are included; no inert-prime or factor oracle
is assumed. Root factors have logarithmic height
O(d log(d|F|)+nu+log f_max), with common denominator D_L of polynomial-bit
length. Lattice/polynomial arrays have poly(n) entries. Sequential access to
their O((h+1)poly(n))-bit data fits the schoolbook work per operation. The
[review, section 7](H031-independent-review.md) gives the detailed substitutions,
prime construction and output checks from the primary source.

For the remaining access costs, labels can be sorted by label and then matrix
position before filling zeros sequentially. At each pivot copy its row to a
work tape and scan all rows; resetting heads and row exchange fit the same
dense cubic bound. Back substitution and merging selected flags with retained
rows are sequential. Use additive 1 in matrix/control bounds for empty data.
Each prime-list reset in the full stream costs B*poly(n) and is included.

For the nonexceptional trial, these bounds imply

    T_trial <= [1+E^2 B + (dB+1)^3] poly(n)
             <= B^3 poly(n)
             = L_N[1/3,3+o(1)] as an upper envelope.   (6.3)

This includes data movement using sequential row/prime scans. A safe space
bound is also B^3 poly(n) bits, simply bounded by the bit work; no small-space
claim about the root routine is needed. Dense matrix storage alone can be
B^2 poly(n). Cold preprocessing is redone and charged each trial. There is
no precomputed factory shared across inputs.

The asymptotic equality uses k~log_2 n and
e~n^(1/3)(log_2 n)^(2/3), so log B~(log N)^(1/3)(log log N)^(2/3).
The field degree is asymptotic to (log N/log log N)^(1/3), and
log H=log m+O(log n); none of these size observations is a yield theorem.

For iid cold restarts with fresh t and free-variable bits, if sigma_N>0,

    E T_until_split = E T_trial / sigma_N.             (6.4)

This remains valid when a trial's cost and success correlate. If sigma_N=0,
restarting never produces a split. A strategy that keeps some fields or
adaptively changes caps is a different procedure and needs its own
conditional probability/cost analysis. Expected useful rows alone cannot
replace either (5.5) or the pathwise full-work bound (6.3).

On the promised distinct-semiprime domain a proper split supplies p and q;
verifying both primalities and their product adds polynomial work. No all-input
recursive factoring theorem follows for arbitrary composites. Even a future
inverse-polynomial bound on (5.5), with this deliberately conservative trial,
would give constant 3, not a preserved 1.92299 or 1.90188 constant. Reducing
the matrix or root cost would require an actually specified replacement and
a fresh ledger. It would still not establish productive probability.

## 7. The precise failure and handoff

The first unjustified step in a proposed uniform successful-factoring proof
would be assigning inverse-polynomial mass to useful retained data from this
specific adjacent-rotation law. The construction alone does not prove that
enough t values survive field/map setup, that the retained relation stream
contains appropriate dependencies, or that those dependencies are squares.
Equations (2.5) and (3.4) supply none of those lower bounds.

Even granting such preparation, the decisive unsolved step is a positive
weighted mass in (5.5): a nontrivial chi_t on the **actual** square subspace,
with sufficiently small c_t on sufficiently many actual t values. Asserting
independence of this character from constraints raises the same kind of
productive-character issue as Lee–Venkatesan Conjecture 7.82/Remark 7.85,
under a different, separately unanalysed sampling law. Their conjecture or
proof does not transfer to this one-parameter pair, positive relation stream,
bad-prime exclusions, capped prefixes or actual-square subspaces. Nontriviality
on a larger smooth semigroup would not imply it on our retained prefix.
Formula (5.2) identifies the common reconstruction mechanism, not an equivalence
of sampling theorems. Generic character counting supplies no missing law here.

Thus the report provides a concrete attempt and a finite probability identity
whose missing hypotheses are visible; it does **not** provide the requested
inverse-polynomial useful-congruence theorem. It also provides no sampler
with only polynomial overhead relative to the best rigorous square-congruence
pipeline, and no improved matched full bound. The constant in (6.3) is an
upper bound for a failing-or-successful trial, not a factoring claim or a
lower bound excluding faster implementations of this family.

**No revised proof question is selected.** Merely asking for the weighted
positivity in (5.5) would rename the original problem, not supply a new
constructive lemma. Reopening this realization requires an arithmetic
mechanism that proves useful mass for the specified law, together with a
matched cost argument. No finite computation is needed to establish this
closure; none is proposed for execution. A later diagnostic would need a
separate preregistration and could not establish the uniform theorem.

The coordinator owns independent review and all shared dispositions,
registries, checkpoints, code and Lean files. This proposer wrote only this
report and adjacent H031-roots-* source/provenance artifacts. Source retrieval,
text extraction, page rendering and document hashing were the only executed
data-processing operations. No package, recursive delegation, outside-project
write, commit, publication or scheduler was used.

**Best supported result:** an independently reviewed finite two-field trial
with the execution conventions above, a conservative per-trial upper ledger,
and the failure-inclusive character identity. No useful-mass lower bound,
tested implementation or formal machine refinement is supplied.
**Verified COMPLETE factoring complexity improvement remains NONE.**
