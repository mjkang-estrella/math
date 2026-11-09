# H017 — A conditional obstruction to stronger-tail supply

Date: 2026-10-08. **New informal derivation awaiting independent review.**
Overall disposition: **inconclusive for arbitrary ordinary-base inputs and
randomized field selection; a sharper, computably conditional supply bound.**
Verified factoring complexity improvement: **NONE**.

The eta = 1/10 window can be closed for polynomials passing an explicit root
geometry condition. The bound counts primitive irreducible quadratics, not
continuous volume. It does not require a smoothness theorem to count them;
its comparison with the required attempt exponent uses precisely Card C's
unproved joint-smoothness model.

The mechanism is this: three separated embedding evaluations determine the
three coefficients of a quadratic. Consequently at most two evaluations can
be small relative to its actual height. A global resultant in the requested
tail must therefore come either from a substantially smaller height cube or
from an evaluation so small that H008's integer-resultant separation permits
at most one primitive irreducible quadratic per witnessing embedding. Roots
too large for any allowed quadratic to nearly vanish are handled separately.

At the stated parameters, if the remaining root geometry loses only
exp(o(D)), where D=(log N)^(1/3)(log log N)^(2/3), the new primitive-irreducible
upper exponent is at most **1.521508**, uniformly allowing the number of very
large roots permitted by the ordinary-base height bound. With o(d) such
roots it is **1.070511**. Reducibles have exponent at most **1.53** separately.
These are below the required **1.881197**. No claim is made that ordinary-base
polynomials uniformly satisfy the geometry condition.

## 1. Scope and prior input

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md and research/hypotheses/H017.md; also
W001 Card C and its shared accounting, H008-disposition.md and
H008-independent-review.md, H013-global-resultant.md and H013-disposition.md,
and the full H014-resultant-enumerator.md. The user's narrower ownership and
no-delegation instructions control this subtask.

H013's count/full-scan disposition is accepted with its model limitations.
H014's construction remains under separate review. This report neither
reimplements nor independently reviews it. H016 owns smoothness/ideal
processing costs; none of that work is duplicated here.

Let f be monic, square-free, integral of degree d, with height A. For the
original route it is the actual ordinary nonnegative base-m expansion of N,
m=floor(N^(1/d)), f(m)=N. Degree and monicity must be checked. A number-field
interpretation further requires irreducibility of f, not merely square-freeness.
The new counting lemma itself also applies to square-free reducible f.

Let H>=1 be integral, and retain genuine quadratics

    g=aX²+bX+c,   1<=a<=H,   |b|,|c|<=H,

at the exact threshold

    |Res(f,g)|^(5d) N^9 <= [(3H)^d (d+1) A²]^(5d).       (1)

In the proof write T=(3H)^d(d+1)A² N^(-9/(5d)); computation uses integer
powers, never floating membership decisions. Actual height is
h=max(a,|b|,|c|). Primitive irreducible means gcd(a,b,c)=1 and no rational
linear factor. The positive leading coefficient fixes the sign convention.

No experiment was run: no geometric input sample, cube enumeration, sieve,
adaptive parameter sweep, or tiny-height admission ratio. Exact rational
arithmetic checked the constants below, not population data. No shared code,
Lean, state, registry, hypothesis, or prior evidence was changed.

## 2. Geometry with the large-root contribution removed

Write the roots of f as alpha_i and put

    w_i=max(1,|alpha_i|)²,
    E_i(g)=|g(alpha_i)|/w_i,
    M(f)=product_i max(1,|alpha_i|).

Thus

    |Res(f,g)| = M(f)² product_i E_i(g).                 (2)

Choose any set F of r roots certified to satisfy |alpha_i|>=2H+2. They
need not be all the roots satisfying this inequality. Let J be the remaining
k=d-r roots, and require k>=3. For i in F,

    E_i(g) >= a-H/|alpha_i|-H/|alpha_i|² > 1/2.         (3)

This uses a>=1. No root-separation premise is needed for these factors.

For distinct remaining roots set

    Delta_ij = |alpha_i-alpha_j| /
               [max(1,|alpha_i|) max(1,|alpha_j|)],

and define the dimensionless, positive quantity

    kappa_J = (1/6) min_{i,j,l distinct in J}
                        Delta_ij Delta_il Delta_jl.    (4)

Any certified rational 0<kappa<=kappa_J is sufficient in everything below.
This is a condition to compute, not an assumption that f has separated roots.

Removing F matters. Two enormous roots can be close in these normalized
coordinates while both obey (3) for every allowed g. Applying (4) to them
would introduce an artificial loss. Ordinary-base coefficient structure can
indeed produce two very large roots; it does not justify assuming that all
roots have bounded modulus.

### The three-evaluation lemma

For every g of actual height h, at least k-2 indices in J satisfy

    E_i(g) >= kappa h.                                  (5)

Proof: for any three distinct indices, the evaluation matrix has rows

    (alpha_i², alpha_i, 1)/w_i.

All entries have modulus at most 1. Its determinant has magnitude exactly
Delta_ij Delta_il Delta_jl, by the Vandermonde identity. Every 2-by-2 cofactor
has magnitude at most 2, so every row sum of the inverse is at most 6 divided
by the determinant magnitude. Applying this inverse to the three evaluations
g(alpha_i)/w_i gives

    h <= 6 max(E_i,E_j,E_l) /
              (Delta_ij Delta_il Delta_jl).

Three values strictly below kappa h would contradict this inequality.
Ordering all k values proves (5), including equality cases. This argument
works for real roots and nonreal conjugate pairs without alteration. It does
not suppose independent embedding factors or randomly distributed digits.

Let e=min_{i in J} E_i(g). Combining (2), (3), and (5) gives

    |Res(f,g)| >= M(f)² 2^(-r) e² (kappa h)^(k-2).      (6)

The second-smallest E_i is at least e, which justifies e². In particular,
multiple moderately small evaluations cannot all be assumed free: k-2 of
them already have the lower bound in (5).

## 3. A height cutoff and an exact discrete supply theorem

The elementary coefficient bound A<=2^d M(f) follows by expanding the monic
root product and bounding each elementary symmetric sum by its binomial
coefficient times M(f). Consequently

    T/M(f)² <= 12^d(d+1) H^d N^(-9/(5d)).               (7)

Define the positive real cutoff

    Y = kappa^(-1) [20736 * 2^r * 12^d * (d+1)
                    * H^(d+6) * N^(-9/(5d))]^(1/(k-2)). (8)

**Conditional supply theorem.** Under the assumptions in Sections 1–2,
every admitted quadratic of height h>=Y has a root alpha_i in J at which

    E_i(g) <= 1/(144 H³).                               (9)

Among these high-height quadratics there are at most k normalized primitive
irreducibles. More generally, if an integer h_*>=1 satisfies h_*>=Y, then
the total number S_pi of primitive irreducibles admitted by (1) obeys

    S_pi <= (h_*-1)(2h_*-1)² + k.                       (10)

The count can also be capped by the containing height-H cube and by H013's
accepted upper count. The interesting case is h_*<=H.

Proof: (6)–(8), together with |Res|<=T, imply (9). Since
w_i<=1+|alpha_i|+|alpha_i|², (9) implies the H008 condition

    |g(alpha_i)| <= epsilon H(1+|alpha_i|+|alpha_i|²),
    epsilon = 1/(144 H^4).

For two height-at-most-H quadratics at that same root, H008 bounds the
absolute integer padded resultant by 72 epsilon H^4=1/2. It is zero.
Primitive irreducibility and positive-leading normalization force the two
quadratics to be identical. Assign each high-height member one witness i;
there are at most k members. The rest have integral height at most h_*-1,
giving the first term of (10) directly. No volume-to-lattice inference occurs.

Conjugate witnesses give identical conditions for real-coefficient g, so
the k term can be reduced to the number of conjugacy orbits represented in
J. The looser k bound suffices. The proof does not assert a rank bound for
reducibles or a smoothness upper bound.

The factor 20736 is 144²; the power H^(d+6) is H^d times H^6 from squaring
the inverse of the small-evaluation threshold. All degree dependence is
displayed. There is no fixed-d implicit constant being extrapolated.

### Fully rational finite certificate

For rational kappa and integer h_*, h_*>=Y is equivalent to

    (kappa h_*)^[5d(k-2)] N^9
      >= [20736 * 2^r * 12^d * (d+1) * H^(d+6)]^(5d).   (11)

Clear the denominator of kappa. This is an exact integer comparison of
polynomial width when d, log A, log H and the certificate precision are
polynomial in bitlength(N). Equality is accepted safely.

A concrete target is h_*=ceil(H^(4/5)), obtained as the ceiling fifth root
of H^4. Passing (11) then certifies S_pi=O(H^(12/5)+d), without enumerating
the H² coefficient lines or producing a single smoothness attempt.

## 4. Reducibles, contents, and zero resultants

These populations must not be credited as distinct new quadratic directions.

For a primitive reducible genuine quadratic g=u v with primitive integral
linears, H008 establishes H(u)H(v)<=sqrt(3)H. Grouping H(u) dyadically gives
O(H² log(2H)) such g in the entire cube, hence also in this tail. For a
common u their parity columns satisfy R=V+c 1^T; the even-cardinality
condition and any odd dependency coset must be retained. No rank-at-most-d
assertion about them is made here.

Nonprimitive reducibles have the same O(H² log(2H)) bound: write g=t g_0
with primitive g_0, and sum O((H/t)² log(2H/t)) over 1<=t<=H. The sum of
t^(-2) is bounded by an absolute constant.

For high-height nonprimitive polynomials irreducible over Q, write g=t g_0.
If g satisfies (9), so does g_0, whose height is at most H. H008 therefore
allows at most k distinct primitive rays for these high-height outputs,
with at most H positive multiples per ray. Adding the low-height cube and
all reducibles yields the optional all-output bound

    S_all = O((1+Y)³ + H² log(2H) + dH).                (12)

An integer h_*>=Y may replace Y. This is a supply bound only, not a new
enumerator or a re-review of H014. It includes outputs rejected by its filters.

If f is irreducible of degree >2, no genuine quadratic has resultant zero.
For arbitrary f, a primitive irreducible quadratic of resultant zero must
be a distinct irreducible quadratic factor of f; there are at most floor(d/2)
such normalized polynomials, regardless of multiplicity. Their positive
multiples number at most dH/2. Zero-resultant reducibles are covered by the
separate reducible bound; they can be numerous when f has a linear factor.
Zero resultants are not smooth nonzero norms or valid number-field elements.

For nonsquare-free f the positive kappa condition can fail outright. The
algorithm should report that status, not apply the square-free theorem to
f's square-free part while keeping d and the original threshold unchanged.
The zero-resultant classification and the reducible bound remain valid.

## 5. Consequences for the eta = 1/10 witness

Use the question's scaling and exact constants

    log H = (a_0+o(1))D,       a_0=153/200,
    d = (delta+o(1))(log N/log log N)^(1/3), delta=21/10,
    b_0=189/200, K=11/5, Q=9/5,
    q=Q/delta²=20/49,
    u_required=b_0+(K/delta+a_0 delta)/(3b_0)
              =4479883/2381400 = 1.8811971949... .

Suppose r/d<=rho+o(1) for a fixed rho<1, and the certified geometry obeys

    log(1/kappa) <= (lambda+o(1))D,    lambda>=0.

Here a_0-q=3497/9800>0. Equation (8) gives

    log Y / D <= (a_0-q)/(1-rho) + lambda + o(1).       (13)

Indeed (d+6)log H/(k-2) and (9 log N)/(5d(k-2)) give the displayed leading
terms. The logarithms of 20736, 2^r, 12^d and d+1 contribute o(D) after
division by k-2. This remains valid for growing d and r=Theta(d).

Thus (10) and (12) give the upper exponents

    s_pi <= 3[(a_0-q)/(1-rho)+lambda],
    s_all <= max(3[(a_0-q)/(1-rho)+lambda], 2a_0).       (14)

These are upper bounds, never achieved density assertions. A strict upper
bound below u_required excludes the population premise at this witness
under the specified unchanged smoothness model. Adding processing, rank,
square-root and restart losses cannot repair that model contradiction.

### If only o(d) roots are removed

At rho=0, lambda=0 the primitive upper exponent is

    3(a_0-q)=10491/9800=1.0705102040...,

and all outputs have upper exponent 2a_0=1.53. More generally the strict
condition closing this witness is

    lambda < u_required/3-a_0+q
           =193057/714420=0.2702289969... .             (15)

For the specific finite h_*=ceil(H^(4/5)) certificate, it suffices
asymptotically that lambda<12503/49000=0.2551632653... . The certified
primitive exponent then is at most 12a_0/5=459/250=1.836<u_required.

### Without assuming a small number of large roots

The ordinary-base height constraint supplies a useful uniform bound on r.
Every removed root contributes at least log(2H+2) to log M(f). Since
M(f)<=sqrt(d+1)A and A<=N^(1/d) for this digit construction,

    r log(2H+2) <= log M(f)
                     <= log N/d + (1/2)log(d+1).

The upper Mahler/l2 inequality here is the same one established and used
in H008's reviewed height accounting. Hence

    limsup r/d <= 1/(a_0 delta²)=20000/67473<1.         (16)

This needs neither a random digit model nor a bound on how many roots are real.
Substitute this worst-case rho into (13):

    beta_max=(a_0-q)/(1-20000/67473)
            =4815369/9494600=0.5071692330... .

At lambda=0, s_pi<=3 beta_max=1.5215076991... and s_all<=1.53.
A fully uniform *conditional* version therefore closes the witness if

    lambda < u_required/3-beta_max
           =4066368961/33915660660=0.1198964986... .    (17)

For the finite H^(4/5) certificate, the corresponding sufficient asymptotic
margin is lambda<4976631/47473000=0.1048307669... .

An elementary sufficient condition for (17) is a normalized pair separation
Delta_ij>=exp(-(mu+o(1))D) on J with
3mu<0.1198964986... . Equation (4), rather than a minimum pair distance
alone, is the sharper quantity to measure. Neither condition is asserted
uniformly for ordinary-base f.

## 6. A computable N-only certificate and its cost

This section specifies a feasible future diagnostic, not an implemented or
executed experiment. Its work is polynomial in input/certificate bit lengths;
it performs no H² line search and needs no information about factors of N.

1. Construct the exact ordinary-base f from N and the public degree. Check
   degree, monicity and square-freeness using gcd(f,f'). Retain failures as
   explicit statuses. Irreducibility/field admissibility is separate.
2. Compute certified disjoint complex root disks. Include all d roots,
   including conjugates; certify the multiplicity/count rather than trusting
   floating approximations. Mark as F only roots whose entire disk is outside
   |z|=2H+2. Unresolved boundary cases remain in J.
3. For disk i with rational complex center z_i and rational radius t_i, use

       U_i=max(1, |Re z_i|+|Im z_i|+t_i),
       L_ij=max(0, max(|Re(z_i-z_j)|,|Im(z_i-z_j)|)-t_i-t_j).

   These are rational, U_i>=max(1,|alpha_i|), and
   L_ij<=|alpha_i-alpha_j|. If a required L_ij vanishes, refine within the
   preregistered precision/budget or return unknown. Otherwise set

       kappa_cert = (1/6) min_{i,j,l in J}
                   L_ij L_il L_jl / (U_i² U_j² U_l²).

   It is a valid lower bound on (4), computable in O(d³) rational operations.
4. Set h_*=ceil(H^(4/5)), or another single preregistered integer cutoff,
   and verify (11). Output the finite upper count (10), the reducible bound,
   r, kappa_cert, and the exact comparison operands/hashes. Failure of (11)
   means this certificate is inconclusive; it is not positive supply evidence.

Certified complex isolation/refinement is not a real-number oracle.
Mehlhorn–Sagraloff–Wang give polynomial bit bounds for integral polynomials,
including disks to prescribed precision: soft-O(d³+d² tau+d p) for
coefficient bits tau and p bits of refinement. Their integral specialization
and treatment of the number of distinct roots apply here after the exact
square-free check. This is the only additional algorithmic primitive used
in this diagnostic description. [Primary paper, introduction and integral
specialization](https://arxiv.org/pdf/1301.4870v2).

One can independently verify proposed simple-root disks by Taylor/Rouche
certificates. For z_i rational complex, rational t_i>0, upper bounds u_j on
|f^(j)(z_i)/j!| and a lower bound l_1 on |f'(z_i)|, check

    l_1 t_i > u_0 + sum_{j=2}^d u_j t_i^j.             (18)

On the circle the linear term dominates the remainder, so there is exactly
one root inside. Rational l1-norm upper bounds and max-component lower
bounds suffice; comparisons contain no irrational oracle. Disjoint disks
passing this test for all d roots cover them all. A failed sufficient test
must be refined or reported unknown, not relabeled root-free.

A fixed polynomial precision cap can be chosen conservatively. For example,
with Z=d+bitlength(A)+bitlength(H)+10, p=100 Z^6 is a polynomial cap, not a
practical performance claim. Monic square-free integral f has root modulus
at most A+1; its nonzero integral discriminant gives

    sep(f) >= [2(A+1)]^(-(d(d-1)/2-1)).

This crude bound already gives polynomial logarithmic separation. Sufficient
refinement gives rational disk bounds within fixed factors of the pair and
triple quantities, except that roots unresolved at the chosen large-root
boundary are conservatively retained. The classifier is sound with any
precision, and may return unknown at the cap. For asymptotic uses of a strict
geometry margin, fixed-factor losses have logarithm o(D). Do not turn the
theoretical polynomial envelope into a claim of a 60-second implementation.

### Ordinary-digit check that can simplify the root split

For any rational R>0 and index k, the entirely N-derived inequality

    f_k R^k > sum_{j!=k} f_j R^j                       (19)

certifies exactly k roots in |z|<R by Rouche, since these coefficients are
nonnegative. In particular, success with k=d-2 at R=2H+2 certifies two
roots outside that radius. Success also at a smaller public R_0 certifies
that all the other roots are inside R_0. Both tests are sufficient, not
assumed. This is useful when the actual coefficient f_(d-2) dominates;
neither uniform digits nor generic coefficients are being invoked.

## 7. What remains missing, and what would decide it

The new exact missing geometric quantity is the joint behavior of

    r/d  and  log(1/kappa_J)/D

for the **actual** N-derived polynomial (or the explicitly specified
field-selection distribution). At the witness, a primitive population at
exponent u_required is incompatible with

    limsup [(a_0-q)/(1-r/d) + log(1/kappa_J)/D]
          < u_required/3.                             (20)

This is a necessary geometric escape condition for a large population,
not sufficient population. Even if (20) fails, the admitted irreducibles
can still be sparse, nonsmooth, dependent, or useless for splitting. The
coarse minimum triple may be controlled by very few roots, so failure of
this particular obstruction can be substantially weaker than actual supply.

The conclusions have four different quantifiers:

- **Every input, fixed ordinary base.** The finite implication (11)->(10)
  is proved for every input meeting its checkable hypotheses. No theorem here
  says every composite's ordinary-base polynomial passes those hypotheses.
- **Random N.** Estimating how often the geometry certificate passes under
  a declared distribution of N is an average-case statement. It cannot be
  transferred to each fixed composite or to independent random base digits.
- **Random field selection for a fixed N.** One must specify the N-only
  field generator, its rational evaluation/norm bounds, and its probability
  of escaping the obstruction on each N. A special bad family for the
  ordinary base does not reject such a different randomized algorithm.
- **Exceptions.** Close root clusters, failed monicity, reducible/repeated
  f, equality boundaries and failed precision/budget all remain visible.
  An isolated resultant-1 unit is consistent with the at-most-k exceptional
  high-height irreducibles; it provides no density or rank theorem.

If a selector tries independent field draws at per-draw construction and
certificate cost C_sel(N), and theta_N is its probability of producing a
field not rejected by a fixed such screen, reaching a screen survivor costs
C_sel(N)/theta_N in expectation for identically costed independent draws.
With variable costs, charge the actual expected work per draw. This is only
a lower stage of a success argument: a survivor may still have no useful
relations. There is no bound here on theta_N, conditional useful yield,
rank, algebraic square roots, or final splitting probability. Restarting
the deterministic ordinary-base construction with unchanged public degree
does not alter f at all.

**Decisive feasible next test:** after independent review, implement only
the root-disk certificate and exact inequality (11), then preregister a
single fixed list of N-only inputs at meaningful growing degrees/widths,
one h_*, the source/seed/input/reference/precision/criterion/budget hashes,
and one <=60-second execution. The reference should independently verify
each root disk by (18), its root count/disjointness, the rational bounds,
and (11). Preserve errors, failures, unknowns, timeouts and unstarted cases.
Passing produces a rigorous finite upper supply bound, not a fitted density;
failing only leaves this obstruction unresolved. There is no registered or
authorized run hidden in this report and no proposal for a full sieve.

For an asymptotic decision, the next proof is a uniform bound on the
quantity in (20), or a costed field-selection mechanism that escapes it
with sufficiently large probability on each N **and** proves actual
primitive useful supply. Under random-N claims, replace that requirement
by a theorem for the explicitly declared input distribution. Finite tests
cannot by themselves establish either asymptotic quantifier.

## 8. Targeted source check and disposition

Beresnevich–Bernik–Gotze, *Integral polynomials with small discriminants and
resultants*, Theorem 2, counts pairs where both polynomials vary with the
same fixed degree and height bound; its constants and sufficiently-large
threshold depend on the degree. It does not provide a fiberwise lower bound
at this fixed N-derived f, unequal degrees d and 2, or uniform constants
in growing d. Its construction is therefore not imported as a population
lemma here. [Primary text, definitions and Theorem 2](https://arxiv.org/html/1501.05767v1).

The three-evaluation bound and its combination with H008 are proved above;
no external source or numerical result is represented as independent review
or as a novelty certificate. This was a focused source check, not a survey.

**Best supported result:** the new conditional discrete bound (10), its
separate reducible/zero accounting, the quantified strict obstructions
(15)/(17), and the polynomial-bit N-only certificate (11). These are
informal mathematics requiring independent review before acceptance.
They sharpen H013 on certified root geometries and isolate a concrete
necessary escape condition for the narrow eta=.1 witness.

**Unsettled:** a uniform all-input bound for that geometry, a usable
field-selection escape probability, and any lower supply of useful smooth
independent relations. The overall stronger-tail proposal remains
inconclusive; it is neither validated nor globally rejected here.

Provenance and exact constant checks are in H017-tail-provenance.json.
No implementation changed, so shared code/Lean checks were not run. No
delegation, packages, commits, publishing, scheduler, or factor advice was
used. **Verified factoring complexity improvement remains NONE.**
