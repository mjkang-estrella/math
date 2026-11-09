# W011 two-color independent review

2026-10-08. **Disposition: revise the scope of the auxiliary sampling laws;
accept identities (1)-(5) for their stated fixed-map, distinct-odd-semiprime
setting. The frozen-map proposal survives this mathematical audit as a
diagnostic candidate only. Verified factoring complexity improvement: NONE.**

The map really removes fresh deep training, and separate absorbing colors really
remove inevitable one-atom masking. Neither fact establishes useful rational
basin supply. This review did not run or inspect the concurrent basin diagnostic,
sample parameters, search for favorable fields, or alter its preregistration.
The parent remains principal researcher. B owns the diagnostic and its outcome.

The main qualifications are:

- `2 v_res` is the **local raw locally legal** image-selected increment. A
  globally clean update also requires the other component's chart to survive.
  For a fixed odd map and fresh CRT training input its raw clean contribution
  at p is at least `2 v_p m_q`, where `m_q` is residual mass outside `0,+1,-1`.
  Given a clean chart, the local increment is at least `2 v_p/m_p`.
- Fresh-flat bounds must distinguish `6/p` per raw local draw from
  `min(1,6/(p-3))` per locally accepted draw; parameter-chart factors are an
  additional paid success channel. Uniform anchors do not make `b(a)` uniform.
- The cubic's fixed-depth average **number** of roots is exactly `k+1` per
  target. This is a prime limit with k fixed, not a statement at a fixed prime
  with k increasing, nor a uniform estimate for k depending on p.
- Over characteristic zero the cubic is a known critically fixed polynomial.
  The quintic is a normal family with two fixed critical points, but is not an
  all-PCF family. An exact 3-adic certificate below disproves that stronger
  classification. Neither map is conjugate over C to a power, Chebyshev, or
  Lattes map. This does not identify it with W009's isogeny/torus schedules.

## Frozen scope and evidence

The seven repository input snapshots and their original paths/hashes are in
[the input manifest](W011-two-color-review-inputs-manifest.json). The frozen
[W011 note](W011-two-color-review-input-research--hypotheses--W011.md) supplies
the complete construction and preregistration reviewed here. The supplementary
[brief](W011-two-color-review-brief.txt) preserves assignment constraints and
prior context. The snapshot of STATE predates this review; this review does not
change STATE or adopt historical archived claims as independently rechecked.

Primary PDFs, extracted text, selected rendered pages, access failures and
passages actually used are preserved in
[the source manifest](W011-two-color-review-sources-manifest.json).
The [standard-library certificate](W011-two-color-review-certificate.py)
checks 40 exact polynomial identities, including a characteristic-five
identity, and passes with [this output](W011-two-color-review-certificate-output.json).
It does not implement a factoring candidate, compute a functional graph, or
iterate a numerical orbit. All-depth and probabilistic proofs appear below;
passing the finite algebra certificate is not a machine proof of those theorems.

## 1. Map, chart, and factorization

Write `D=2a(a+1)^2` and temporarily regard `b` as an independent coefficient.
The family has the particularly useful form

    F_b(T) = b T^5 - (1/2+2b) T^3 + (3/2+b) T,
    F_b'(T) = (T^2-1)[5b T^2-b-3/2],
    F_b(T)-T = T(T^2-1)[b T^2-b-1/2].

Thus it is odd, fixes `0,+1,-1`, and is critical at both colors. Substituting
`b=(a+2)/D` gives exactly

    D(F_a(T)-1) = (T-1)^2(T-a) Q_a(T),
    D(F_a(T)+1) = (T+1)^2(T+a) Q_a(-T),
    Q_a(T) = (a+2)T^2+(a+2)^2T+2(a+1)^2.

Both signs, `F_a(a)=1`, and `F_a(-a)=-1` are verified. No square root of the
quadratic discriminant is needed by this evaluator. Its discriminant is
exactly `a(a+2)(a^2-2a-4)`; being a quadratic factor does not give its roots
to the algorithm.

For odd N, first testing the three individual gcds and proceeding only when
all are one makes D a unit. The `a-1` test is stronger than what inversion
alone requires, but ensures that the supplied fibers are outside the colors.
Return any proper factor; a full gcd is not an excuse to suppress subsequent
scheduled chart tests. After all tests, reject any remaining full chart. This
agrees with the frozen diagnostic's more explicit rule. One inversion then
suffices for the frozen coefficient. Arithmetic, gcds, inversion, randomness,
and operand widths remain charged in a complete implementation.

The probability formulas in this report assume `N=pq` for **distinct odd
primes**. They are not formulas for arbitrary prime powers or integers with
three or more prime factors. The local clean-parameter discussion assumes
`p>3`: for p=3 the local chart is empty, and p=2 needs the preliminary factor
test. This is a scope condition, not permission to discard such inputs from
an eventual all-composite algorithm.

### Degree loss and all root-collision cases for p>3

All statements in this paragraph concern geometric roots over an algebraic
closure of the local field; they do not claim rationality of the roots.

- `a=-2` is legal and gives `b=0`, `Q=2`, `D=-4`, and `F=C` of degree three.
  Its +1 fiber has root 1 of multiplicity two and root -2 of multiplicity
  one. The -1 fiber is the reflected one. In a clean map modulo N this
  reduction may occur at one prime only; retain it without rejection.
- Otherwise the polynomial has degree five. Put
  `R=3a^2+9a+8` and `S=a^2+3a+1`. Then

      Q(1)=R,              Q'(1)=(a+2)(a+4),
      Q(a)=2(a+1)S,        Q'(a)=(a+2)(3a+2),
      Q(0)=2(a+1)^2,       Q(-1)=a(a+1).

  Generically the +1 fiber has multiplicities `2,1,1,1`: 1, a, and the
  two quadratic roots. If R=0, the target 1 has multiplicity three. If
  S=0, a has multiplicity two. If `a^2-2a-4=0`, Q has a double root
  `-(a+2)/2`, different from 1 and a, with multiplicity two in the fiber.
  These three collision cases are mutually exclusive on the legal chart
  in characteristic p>3. They each leave three distinct roots. With no
  collision there are four distinct roots. Reflect for the opposite color.
- To check exhaustiveness without dividing by possibly zero coefficients,
  use `R-3S=5`, `R-(a+4)(3a-3)=20`, and
  `9S-(3a+2)(3a+7)=-5`. Any extra overlap would force p=5 after excluding
  p=2,3, and then a=1, which is not legal. These identities also exclude
  a double Q-root at 1 or a. There is no hidden higher target multiplicity
  on a legal chart.
- In characteristic five one must not solve the displayed derivative by
  dividing by `5b`. Instead it becomes `(1-b)(T^2-1)`. On this chart

      b(a)-1 = -(a-1)^3/[a(a+1)^2]  in characteristic five,

  so `b=1` (the inseparable `T^5` specialization of the b-family) is
  unavailable for legal a, even over the algebraic closure. The actual
  degree-five maps are separable; the preceding fiber counts still apply.

In particular every clean map over F_p has the four distinct rational inputs
`+1,-1,+a,-a` absorbed by depth one. Literal empty target basins cannot occur:
`h_p(0)=2/p` and `h_p(1)>=4/p`. A zero-success entry for a completed clean map
with the prescribed inclusion of step zero would therefore signal an error;
preserving zero/unknown statuses remains appropriate for validation and
censored records. There may be no further ingress after a small basin fills.
Since 0 is fixed, `h_p(k)<=1-1/p`; the brief's h=1 illustration is an idealized
limiting masking check, not an attainable finite-field state here.

## 2. Endpoint extraction and the complete stopping law

Fix the maps before drawing a fresh uniform seed modulo pq. Its two local
coordinates are independent uniform seeds. For an odd map fixing the colors,
negation pairs the two target fibers, so each has probability `h_p/2`.
The three disjoint endpoint success events are: only p is colored; only q
is colored; both are colored with opposite signs. Their total is

    h_p(1-h_q)+h_q(1-h_p)+(1/2)h_p h_q
      = h_p+h_q-(3/2)h_p h_q.                       [equation (3)]

Both uncolored gives two gcds equal to one. Both with the same color gives
a full gcd and no proper factor. Opposite colors give a proper factor at
the first gcd. Thus order `P-1` then `P+1` does not change this endpoint law.
The identity

    S_end = h_p(1-h_q/2)+h_q(1-h_p)

proves `S_end>=h_p/2`, and symmetrically the advertised maximum bound.
At the idealized `h_p=h_q=1` it gives one half exactly.

For stopping, let `tau_p` be the first hit of either color, possibly infinity,
and `epsilon_p` its color when finite. Because negation preserves first-hit
time and reverses color,

    Pr[tau_p=j, epsilon_p=+1]
      = Pr[tau_p=j, epsilon_p=-1] = Delta h_p(j)/2.

This equality holds **separately for every first-hit time**, not only at the
endpoint. The p and q pairs are independent for the fixed maps and fresh CRT
seed. A trial succeeds if the earlier first-hit time is at most k, except
when both first hits are simultaneous and their colors agree. Consequently

    Pr[no hit by k] = (1-h_p(k))(1-h_q(k)),
    Pr[full-gcd failure by k]
       = (1/2) sum_(j=0)^k Delta h_p(j) Delta h_q(j).

Their complement is precisely equation (4). At unequal first-hit times,
the earlier hit already exposes a proper factor, including paths which
would have ended at a common color if one had failed to check earlier.
At a full gcd both components are at the same absorbing color; further
updates cannot rescue the current seed in this protocol. These are
unconditioned probabilities including full-gcd failures.

The j-th map update is executed exactly when both first-hit times exceed
`j-1`. Summing these survival indicators gives equation (5). The formula
requires gcd checks at step zero as stipulated; omitting them changes the
cost and stopping distribution. In particular

    S_stop(0)=S_end(0)=2/p+2/q-6/(pq)>0,
    E[updates at cap 0]=0.

Also

    S_stop(k)-S_end(k)
      = (1/2)[h_p(k)h_q(k)-sum_j Delta h_p(j)Delta h_q(j)] >= 0.

The bracket contains the unequal-time pairs. This is a useful exact audit
check for B, not a new diagnostic run or change to its registered data.
Absorption also makes each h nondecreasing. Fixed independent-of-seed
schedules of odd color-fixing maps admit the same argument; the selected
frozen-map case needs no extension of scope to be valid. One must not
replace this fresh-seed law by a success-conditioned or survived-history law.

## 3. Fresh-flat and image-selected laws pay different chart costs

### Flat anchors

For a current local value `t` outside `0,+1,-1`, the exact identity

    2(F_b(t)-1)=(t-1)^2[2b t(t+1)^2-(t+2)]

shows that `F_a(t)=1` iff `b(a)=b(t)`. Oddness gives the -1 equation
`b(a)=b(-t)`. For any fixed c,

    2c A(A+1)^2-(A+2)=0

is a nonzero polynomial of degree three when c is nonzero, and the linear
equation `A=-2` when c is zero. Thus there are at most three anchors per
target, at most six total. This handles the cubic degeneration as well.
At t=0 the hitting probability is zero; a previous target remains absorbed.

For p>3, a raw uniform local anchor therefore gives legal absorption with
probability at most `min((p-3)/p,6/p)` for this residual t. Given a locally
legal uniform anchor, the bound is `min(1,6/(p-3))`. For any current law
independent of the fresh anchor, the expected increment is bounded by this
accepted hazard times its residual mass outside `0,+1,-1`. A union bound
over k accepted fresh stages gives at most `6k/(p-3)` additional target
probability, capped by available mass. This does not price or bound the
entire global factoring protocol by itself.

For a raw uniform anchor modulo pq, global cleanliness has probability
`(p-3)(q-3)/(pq)`. Conditioned on clean, its local anchors remain independent
uniform points of the two local legal charts. The raw **clean** local hazard
at p is at most `(6/p)(1-3/q)`, capped by cleanliness. Separately, all chart
outcomes are exactly

    clean:          (p-3)(q-3)/(pq),
    full failure:   3/(pq),
    proper factor:  3/p+3/q-12/(pq).

Full failure means the same one of `0,+1,-1` at both components; any other
non-clean combination exposes a factor in the sequence of three individual
gcds. These probabilities sum to one. Reporting `6/(p-3)` as the complete
raw success hazard would discard this additional factor channel and the
work of every rejected chart. Repeating until a clean chart is also not
free. Finally, the induced coefficient law is the pushforward under the
degree-three rational function b; equal a probabilities do not imply equal
probabilities on distinct map shapes.

### Image-selected anchors

Condition on a fixed current odd local map P and put

    mu(t)=Pr[P(r)=t],
    L=F_p minus {0,+1,-1},
    m=sum_(t in L) mu(t),    v=sum_(t in L) mu(t)^2.

For each actual legal anchor a, let `G(a)` be the new target mass after
appending `F_a`, less the old target mass. The fibers at a and -a are
disjoint from each other and from the targets, even when Q collides with
one of them. Oddness gives

    G(a)>=mu(a)+mu(-a)=2mu(a).

Extra quadratic roots can only add mass; roots already listed must not be
counted twice. With one fresh raw image draw, the valid local conclusion is

    E[1_(a in L) G(a)]>=2v.

When m>0 the locally accepted conclusion is `E[G(a)|a in L]>=2v/m`.
When m=0 there is no legal update and v=0; do not divide by m.

For a fixed global P and a fresh independent uniform r modulo pq, the two
anchor laws factor by CRT. A globally clean update requires both anchors
legal, and hence

    Pr[clean]=m_p m_q,
    E[1_clean G_p(a_p)]>=2v_p m_q,
    E[G_p(a_p)|clean]>=2v_p/m_p          (m_p m_q>0),
    Pr[full chart failure]=mu_p(0)mu_q(0)+h_p h_q/2,
    Pr[chart factor]=1-m_p m_q-mu_p(0)mu_q(0)-h_p h_q/2.

The same assertions hold with p and q exchanged. Thus the brief's wording
"raw locally legal" is essential: **do not use the unweighted 2v_p as a
raw global continued-process drift bound**. A low m_q suppresses clean
updates, while chart factors may separately help. If one instead averages
over adaptive histories, first establish these conditional fixed-P laws and
then average with their actual history probabilities. Fresh acquisition
requires evaluating the depth-j P to generate its anchor: k attempted
stages have O(k^2) depth-sum work in the natural evaluator, before retry,
gcd and bit costs. No sampler from the current image is supplied for free.

## 4. Cubic factorization, multiplicities, and the prime limit

The scale-normalization calculation is exact:

    [(aT)^3-3a^2(aT)]/(-2a^3)=(3T-T^3)/2=C(T).

It requires the indicated scale to be a unit. With `L(T)=(T+1)/2`,
`L o C o L^(-1)=g`, where `g(X)=3X^2-2X^3`. This conjugacy is defined
over every field of odd characteristic and is a permutation of that field.

Starting from `g(U)=U^2(3-2U)`, induction immediately gives

    g^k(X)=X^(2^k) product_(j=0)^(k-1)
                        [3-2g^j(X)]^(2^(k-1-j)).

This includes k=0 with an empty product. For p>3, set `H_j=2g^j-3`.
Each H_j has degree `3^j` and is squarefree geometrically. Indeed,

    (g^j)'(X)=6^j product_(i=0)^(j-1) g^i(X)[1-g^i(X)].

A repeated root of H_j would therefore have an earlier iterate 0 or 1,
which stays fixed and cannot later equal 3/2. For j=0 the derivative of
H_0 is 2. The H_j are pairwise disjoint in their roots: after reaching
3/2 the next value is 0 forever. None contains 0. It follows that the
distinct geometric zero count is exactly

    1+sum_(j=0)^(k-1) 3^j = (3^k+1)/2.

The root 0 has multiplicity `2^k`; a root of H_j has multiplicity
`2^(k-1-j)`. The displayed geometric count holds at **every p>3**, not
merely at an unspecified collection of good primes. Characteristic three
has `g=X^3`, and characteristic two has `g=X^2`; their collapse is precisely
why these primes are excluded from this geometric argument. Reflection
`g(1-X)=1-g(X)` gives the target-one factorization and counts. The two
target root sets are disjoint.

For all integers j>=0, `g^j` lies in Z[X], has constant term zero, and

    g^j(X) mod 3 = X^(3^j),
    lc(g^j)=(-2)^((3^j-1)/2).

Thus H_j has constant term -3, leading coefficient not divisible by 3,
and every other coefficient divisible by 3. The constant term is not
divisible by 9. It is primitive (its leading coefficient is a power of
two up to sign, and its constant coefficient is -3) and is Eisenstein at
3. This includes `H_0=2X-3`, where irreducibility is also immediate from
degree one. Every H_j is irreducible over Q. Multiplicity in g^k does not
alter these distinct irreducible factors.

Here is the precise prime-average consequence. Fix j once and for all;
let `r_j(p)=#{x in F_p:H_j(x)=0}`. In its finite splitting field over Q,
the Galois action on roots is transitive. At good primes r_j(p) is the
number of fixed roots of a Frobenius element. Chebotarev with **natural
prime density**, followed by the elementary orbit-counting identity,
therefore gives

    lim_(X -> infinity) [1/pi(X)] sum_(3<p<=X) r_j(p)
      = [1/|G_j|] sum_(sigma in G_j) #Fix(sigma) = 1.

The source for the Frobenius/root correspondence and natural-density
theorem is [Lenstra, Fact 2.1 and Theorem 3.1, p. 3](https://websites.math.leidenuniv.nl/algebra/Lenstra-Chebotarev.pdf).
The orbit-counting step and this application are our deductions.

Generally one excludes primes dividing the leading coefficient or
discriminant, and primes ramified in the fixed splitting field. Here the
squarefreeness proof and power-of-two leading coefficient show that **2
and 3 are a sufficient excluded set for every fixed j**. Inverting 2
makes H_j monic up to a unit, and its root algebra is etale at each p>3;
the splitting field is unramified there. The squarefree product of the
finitely many distinct factors for any fixed k has the same property.
Excluding any larger finite exceptional set would leave the limit intact.

Let `R_p(k)=#{x:g^k(x)=0}`. For fixed k it follows that

    lim_(X -> infinity) [1/pi(X)] sum_(3<p<=X) R_p(k)=k+1,
    lim_(X -> infinity) [1/pi(X)] sum_(3<p<=X) p h_p^C(k)=2(k+1).

The second formula counts both colors under the rational affine conjugacy.
It is a mean of root **counts**, not an equality asserting a uniform
`h_p(k)=2(k+1)/p`. No GRH, independence among factors, or knowledge of the
full iterated Galois group is needed for these fixed finite-depth limits.
No uniform error term in k is obtained. Even though the excluded prime set
can be fixed, the number field and its degree/discriminant change with k.
Interchanging limits, extrapolating to `k=k(p)`, or inferring full-basin
counts at fixed p is unjustified.

An affine conjugacy defined over F_p bijects transported target basins and
preserves every first-hit histogram. It does not provide a new independent
map shape. Conjugacy merely over an algebraic closure need not preserve
F_p-point counts; this is relevant to the complex normalizations below.

## 5. Focused primary prior art and exact scope

**The cubic is already an explicit critically fixed example.**
[Aitken, Hajir and Maire, *Finitely ramified iterated extensions*,
arXiv:math/0408170v1, section 2.4, pp. 7-8](https://arxiv.org/pdf/math/0408170v1)
give `z^3+(3/2)z` as Example 2.6 and the degree-d normal form
`z^d+d z/(d-1)` in Proposition 2.9 for critically fixed simply ramified
polynomials in their algebraically closed characteristic-zero discussion.
Taking `s^2=-2` gives

    s^(-1) C(sz)=z^3+(3/2)z.

This is an explicit algebraic/complex conjugacy, not an assertion that s
lies in each prime field. Their usage of “generalized Chebyshev” for
two-critical-value/Shabat polynomials is broader than dynamical conjugacy
to the classical Chebyshev polynomial. Those meanings must not be conflated.

[Geyer, *Classification of critically fixed anti-rational maps*,
arXiv:2006.10788v2, section 7.1.2, p. 23](https://arxiv.org/pdf/2006.10788v2)
explicitly displays the **holomorphic** critically fixed polynomials
`3z^2-2z^3` and `10z^3-15z^4+6z^5`, whose complex conjugates enter that
paper's anti-polynomial classification. It also gives their general
integral form. We use the displayed holomorphic examples only; we do not
apply the paper's anti-rational theorems to W011's holomorphic maps.

The W011 b-family specializes at `b=3/8` to the latter quintic under
`T=2z-1`, since

    [F_(b=3/8)(2z-1)+1]/2=10z^3-15z^4+6z^5.

This b value is attained over characteristic zero by the legal roots of
`3a^2+9a+8=0`: the parameter equation is
`3a(a+1)^2-4(a+2)=(a-1)(3a^2+9a+8)=0`.
This identifies a known special member, not the entire varying family.

**The whole quintic family is not PCF.** The general derivative leaves
two additional critical points with `c^2=(b+3/2)/(5b)` in characteristic
zero when these are distinct. Fixing the two colors says nothing about
these remaining orbits. More decisively, at the exact rational parameter
a=2 we have b=1/9 and

    F(T)=T^5/9-13T^3/18+29T/18,
    c^2=29/10,
    F(c)=(203/450)c.

The last identity is certified by

    F(T)-(203/450)T
      = T(T^2-29/10)(T^2/9-2/5).

At any extension of the 3-adic valuation normalized by v(3)=1, v(c)=0
and v(F(c))=-2. All three nonzero coefficients of F have valuation -2.
Whenever v(z)<0, its leading term has uniquely least valuation, so
`v(F(z))=5v(z)-2`. The critical orbit then has unbounded negative
valuation and is infinite. This is an exact algebraic/valuation
certificate of a non-PCF member, **not a numerical orbit run or a
finite-field basin counterexample**. No full classification of PCF
parameters is claimed.

**Power/Chebyshev/Lattes conjugacy is excluded over C.** Every legal
member has at least three distinct critical fixed points on the sphere:
1, -1 and infinity. Power maps `z^d` have only two critical points;
`z^(-d)` has those points in a two-cycle. Classical signed Chebyshev
maps have no finite periodic critical points and only infinity as a
critical fixed point. Genuine Lattes maps have no exceptional point,
whereas a polynomial's infinity is exceptional (it has finite backward
orbit). These are conjugacy invariants. The relevant definitions and
properties are read in [Milnor, *On Lattes Maps*, arXiv:math/0402147v2,
section 2, pp. 2-3](https://arxiv.org/pdf/math/0402147v2).
The exclusions are our deductions from those properties and the verified
critical fixed points. They do not assert that every map with fixed
critical points is an isogeny, a torus map, or a group-order algorithm.
Nor do they rule out accidental exceptional behavior after reduction in
small characteristic; the specific p=5 issue was handled algebraically.

For perspective, solving the two linear constraints on an odd polynomial
`c_5 T^5+c_3 T^3+c_1 T` imposed by `F(1)=1` and `F'(1)=0` gives exactly
the displayed one-dimensional b-family. Thus it is a natural normal
family with two prescribed superattracting fixed points. Distinct nonzero
b values really give distinct affine conjugacy classes in characteristic
zero: the vanishing degree-four coefficient forces an affine conjugacy
between these centered quintics to fix 0, and the multiplier there is
`3/2+b`. This does not remove the multiple a values with the same b, or
make the induced map-shape law uniform. The narrow
source review did not identify the exact rational anchor parametrization
as a named prior factoring method or establish its novelty. Complex
superattraction and PCF classification provide no finite-field basin
concentration theorem in this review.

## 6. Computational survivor, falsifier, and the remaining supply question

The strongest supported computational survivor is concrete: sample one
N-only anchor, pay its chart and coefficient acquisition, then evaluate a
fixed degree-three or degree-five map along fresh seed walks at constant
arithmetic work per update, checking the two colors separately and
stopping exactly as in (4)-(5). This saves the depth-sum fresh acquisition
work. Its successful outputs remain ordinary verified proper gcd factors.
The stopping improvement and two-color extraction are valid independently
of whether useful basins occur.

A general elementary size restriction is also available. For a degree-d
polynomial with a critical fixed target, the number B_k of distinct
geometric inputs hitting that target by k satisfies

    B_0=1,       B_(k+1)<=d B_k-1,
    B_k<=((d-2)d^k+1)/(d-1).

The subtraction occurs because the fiber over the fixed target has at
most d-1 distinct roots; all other fibers have at most d. For the legal
quintic this yields

    h_p(k)<=min(1-1/p, (3*5^k+1)/(2p)).

For the cubic the exact geometric count above gives
`h_p(k)<=min(1-1/p,(3^k+1)/p)`. In particular constant depth cannot
produce a positive asymptotic fraction of the field; for balanced pairs,
`5^k=o(sqrt(p))` cannot pass an asymptotically small version of the
optimistic ratio in (6), even using the universal quintic bound and a
unit cost numerator. This restriction neither predicts deeper basins
nor contradicts possible useful logarithmic-depth behavior.

The selected decisive cheap falsifier remains **B's unchanged frozen
preregistration**: its exact small-field reverse-BFS diagnostic, all
scheduled seeds and statuses, all registered depths and cubic controls,
the eight-of-sixteen condition on each largest pair, and its original
60-second budget including setup. The hidden-factor graph construction
is an oracle diagnostic, not a candidate preprocessing step. Passing
licenses only independent validation plus a realizable N-only depth
schedule. Failing rejects this finite window under that rule. A deadline
preventing primary-pair evaluation is inconclusive as registered. This
review reports no pass/fail outcome, changes no threshold, and authorizes
no rerun, extra search, or tuned parameter.

For any eventual iid restart protocol, let A be its unconditional expected
paid work and S its unconditional factor probability per trial. If A is
finite and S>0, the renewal equation `E=A+(1-S)E` gives `E=A/S` even when
cost and success within a trial are correlated. The maps sampled across
trials must be included in both expectations. One cannot replace this
ratio by a mean or minimum of per-map ratios.

For example, with one fresh uniform anchor per trial, one seed for a
clean chart, and a depth rule k determined from public inputs, the exact
distinct-semiprime success denominator is

    S_total = Pr[chart factor]
                + E_a[1_clean(a) S_stop(a,k)],

and the numerator includes every raw chart, rejected/full trial,
coefficient inversion, seed draw, map operation, gcd, and bit cost.
Keeping several seeds for one acquired map would require its own paid
restart/accounting rule. B's `min_k` statistic uses hidden basin knowledge
as an optimistic oracle; it is not this N-only rule.

The unresolved supply question is therefore precise: **for the actual
raw N-only parameter law, can one prove enough probability of local
first-hit distributions with sufficiently large early target mass that
the resulting unconditional paid A/S is substantially below the
sqrt(p) collision control, using an implementable public depth rule?**
The parameter law, all chart outcomes, slow maps, degree drops, short
basins, full gcds and restarts belong in that theorem. No such supply or
cost theorem is established here. Even solving that comparison would
not alone establish an ECM/GNFS improvement or the all-composite target.

No source/Lean implementation or shared-state change is selected by this
review. The next evidence that can change the frozen pilot's disposition
is B's already registered result; a later mathematical advance would
need the supply and paid-cost statement just specified.
