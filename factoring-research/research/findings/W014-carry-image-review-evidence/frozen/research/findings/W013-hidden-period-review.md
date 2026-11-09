# W013 hidden-period consumer: independent review

2026-10-08 UTC. **Verified new complete factoring improvement: NONE.**

**Disposition: accept the conditional consumer and identities (1)–(5), with one
cost-table correction and explicit normalization guards.** The fixed-degree
integer-root procedure, component-order checks, global-match removal, and batch
gcd recovery are correct for any composite with a covered prime factor, including
non-semiprimes. The linear construction has a paid `N^(1/5) poly(log N)` envelope
using known ingredients. It supplies no novelty or improvement over those
ingredients.

The material correction is in the higher-degree budget paragraph: the proposed
quartic optimum has `E/H ≍ X^(1/10)`, outside its small-tolerance hypothesis.
`11/40` is a formal extrapolation, not the stated sufficient Dirichlet budget.
The saturation-aware quartic budget gives **`5/18`**, still worse than `1/5`.
All these exponents describe a particular sufficient-budget recipe, not lower
bounds, and higher-dimensional approximation acquisition remains separately owed.

For rational normalization, `b<0` requires a sign change to enter the original
`q≥1` contract; `b=0` requires a separate nonzero-polynomial branch. An identically
zero recovery polynomial cannot be removed as an unsuccessfully checked finite
root list while still claiming coverage. The continuation already identifies
the degeneracy; the explicit guard below completes its algorithmic interpretation.

## Review objects and scope

The frozen continuation has SHA-256
`5492510aa1661e7a1d9f8ab58ecde8c29913d3f95f764d7cc60989d488e725d4`.
The original W013 brief has SHA-256
`f20282daba4ebd972246328c4641d80ac5472c5173065c48e1b52acc43bfb2f9`.
The [input manifest](W013-hidden-period-review-evidence/inputs-manifest.json)
records exact bytes and hashes for these, AGENTS, RESEARCH_TEAM, RESEARCH_LOOP,
README, SPECIFICATION, STATE, and the prior polynomial-filter review. The latter's
accepted quartic obstruction is background; it is not re-proved here. STATE was
read for context, not treated as a mathematical premise. No residual-cycle or
W012 geometry audit was undertaken.

[Harvey's primary paper](https://arxiv.org/html/2010.05450) was independently
read at §§2.2–2.4, Algorithm 4.1/Proposition 4.1, Algorithm 4.2/Proposition 4.2,
with the adjacent linear-recovery discussion. Its downloaded HTML/MathML and
text reading aid are frozen; see the
[source manifest](W013-hidden-period-review-evidence/harvey-source-manifest.json).
This is a narrow machinery check, not a current-best-bound or broad novelty survey.

## 1. Transfer (1), signed errors, and domain

State the consumer for `N>1` composite, integer blocks `X≥2,H≥1`, `q≥1`,
integer coefficients, fixed degree bound `d`, certified integer `E≥0`, and a
covered prime `p|N` with `X≤p<X+H`. Set `Q=N/p`. No primality or coprimality
condition on `Q` or `q` is needed. For factor-search coverage one may truncate
blocks to `[2,isqrt(N)]`; a covered prime of a composite is proper regardless.

For every integer polynomial, `u≡v mod m` implies `A(u)≡A(v) mod m`.
Because `p-X≡1-X mod p-1` and `N-Q=(p-1)Q`,

    D-e = A(1-X)-A(p-X)-q(N-Q) ≡ 0 mod p-1.

This proves (1), including `p=2`, where congruence modulo one is automatic.
Fermat's theorem then gives `alpha^D=alpha^e mod p` for a unit `alpha mod N`.
Signed exponents are interpreted using the same inverse modulo N, which reduces
to the inverse modulo p. No uncomputed group-order reduction of exponents is
allowed. Compute the inverse once by extended gcd and charge its cost.

The integer error is exactly `e=A(p-X)-qQ`. There is no extra rounding allowance.
If a supplied bound is rational, an exact outward integer bound suffices; the
continuation already supplies integer E. Translate the entire signed interval:

    0≤e+E≤2E,     e+E=kB+j,     0≤j<B,
    0≤k<ceil((2E+1)/B).

Consequently `D+E-kB≡j mod p-1`. The sign of E and of `kB` in the giant
exponent is correct. `E=0`, `B=1`, an endpoint error, and a partially occupied
last chunk cause no omission. Extra positions may give `e'>E`; they are charged
and may be checked as written. They cannot equal the true pair after the order
check if their proposed error is outside the true interval.

## 2. Component checks and safe global-collision removal

The input promise `ord_N(alpha)≥B` implies `alpha^j≠1 mod N` for
`1≤j<B`. Thus any nonunit `alpha^j-1` has gcd strictly between 1 and N.
If all these differences are units, no prime divisor r of N has
`ord_r(alpha)<B`: otherwise the check at its order would fail. Equivalently,
the B baby powers are distinct modulo every prime divisor. All pairwise baby
differences would give the same condition because

    alpha^v-alpha^u = alpha^u(alpha^(v-u)-1).

For `B=1` the check is empty and component order at least one is automatic.
For `p=2` and `B>1`, it necessarily returns a proper gcd before proceeding,
provided the supplied global-order promise is valid.

Fix a covered prime and its true tagged giant `(i,k0)` and baby index j0.
If that giant also matches baby j globally, reduction modulo p gives
`alpha^j=alpha^j0 mod p`. Since `0≤j,j0<B≤ord_p(alpha)`, one has j=j0,
hence `e'=k0B+j-E_i=e`. Therefore p is an integer root of (2):

    F_e(p)=p(A(p-X)-e)-qN=p(qQ)-qN=0.

The coefficient identity `F_e(0)=-qN≠0` rules out the zero polynomial.
Checking every integer root in the block and validating proper divisibility
must therefore recover a factor before this true giant can be discarded.
This is the precise justification for removal; a global equality alone is not
an exact error certificate.

Every tagged global match needs its own recovery check. Deduplicating equal
giant residues before checking all associated tags can lose the true certificate.
The continuation puts optional deduplication after those checks, which is safe.
Baby values are globally distinct, so there are at most G tagged matches.

The necessity of the component check has a fixed exact control. Take N=21,
alpha=2, B=4, X=3,H=1,q=1,A=7,E=2. Global order is 6, but the component
check at j=2 returns 3. If deliberately bypassed, the true error zero uses
`(k,j)=(0,2)`, while that giant equals baby 0 globally. Its wrong recovery
equation is `9x-21=0`. The other giant gives `3x-21=0`, whose root 7 is
outside the specified block. Removing both after only the specified block-root
checks loses coverage. This is a counterexample to the bypass, not to the
reviewed algorithm, which immediately returns 3.

## 3. Batch gcds, including repeated prime factors

After removing global matches, every retained leaf `beta_j-gamma` is nonzero
modulo N. Form `P(Y)=prod(Y-gamma)` and evaluate at each baby. A retained
true collision makes `gcd(P(beta_j0),N)>1`.

If that gcd is proper, return it. If it equals N, at least one leaf is a
nonunit: a product of units cannot be zero modulo N. Because no leaf is zero
modulo N, every nonunit leaf has a proper gcd. A single linear scan of at most
G leaves therefore succeeds, or a product-tree descent can select a nonunit
child until reaching a leaf. Once such a scan is started, success is guaranteed;
there is no B-times-G recovery cost. Empty retained lists mean P=1 and cannot
contain a still-unrecovered true collision.

Nothing uses squarefreeness or a two-prime CRT. In a prime power, several leaves
may accumulate enough valuation to make the product zero modulo N even though
each leaf has only a proper prime-power gcd. This still satisfies the proof.
Deleting duplicate retained residues also remains safe: only one prime-component
collision is needed, not preservation of the product's full valuation.

The certificate includes N=35 with retained giants 8,16: at beta=1 the product
gcd is 35 and leaf gcds are 7,5. It also includes N=49 with giants 43,36:
the product gcd is 49 and both leaf gcds are 7. Duplicate 43s behave correctly,
and deduplication changes the product gcd to the still-useful 7. These are exact
branch fixtures, not estimates of success rates.

## 4. Finite-degree integer roots and bit cost (3)

For fixed degree, integer-root finding here needs no factorization of q, N,
or the polynomial's constant coefficient. One elementary exact procedure on
an integer interval `[L,U]` is the finite-difference recursion in the prior
review. Recursively partition `[L,U-1]` into sign runs of
`Delta F(t)=F(t+1)-F(t)`, whose degree drops by one. On a run, F is monotone
on the corresponding integer interval including the next endpoint. Binary
search locates its negative/zero/positive transitions. Merge repeated endpoints;
handle constants and singleton intervals explicitly.

A degree-r nonzero polynomial has at most r real roots. Its integer sign
sequence consequently has `O(r)` runs. The recursion uses
`O_r(log(U-L+2))` exact evaluations for fixed r, with a degree-dependent
constant. A zero-polynomial recursive subproblem is a constant sign run; the
top-level F is nonzero. Its zero run cannot contain more than r distinct integer
points, so producing the roots is finite and bounded by r. Multiple roots,
degree drops, negative leading coefficients, and roots at either included
endpoint do not invalidate this algorithm. All candidate roots still receive
an exact proper-divisor test: roots of F can divide qN without dividing N.

Let n be the bit length of N, and let ell bound all coefficient, parameter,
exponent, endpoint, tag and list-index bit lengths. Translation from A(h) to
A(x-X) increases coefficient size by at most `O_d(log(|X|+2))`; subtracting e
and qN adds their actual bit lengths. Root recovery costs `poly_d(n+ell)`
per matched tag. This is the relevant bound, not a unit-cost algebraic oracle.

For list work, generate babies incrementally, compute each initial giant by
binary exponentiation, and advance it by the shared `alpha^(-B)`. This costs
`O(B+G)` modular multiplications plus K exponentiations with their actual
exponent lengths. Sorting costs `O((B+G) log(B+G))` comparisons of the actual
records. At most G root calls and B initial gcds are required. Fast polynomial
products and monic remainder-tree evaluation work over Z/NZ; they do not invert
arbitrary nonunits. Kronecker packing has coefficient width
`O(n+log(B+G))`, so fast integer multiplication yields near-linear list work
up to logarithmic factors. The one recovery scan adds at most G gcds.

Thus an honest general form of (3) is

    (B+G+K) poly_d(n+ell) + C_certificates + C_alpha,

with storage bounded by the same linear-list scale times polynomial/logarithmic
factors. Under the note's polynomial-in-n bit bounds this becomes its stated
`(B+G+K) poly(log N)` bound. Degrees growing with n, exponentially long
coefficient encodings, explicit target expansion, or a slow polynomial engine
would require different accounting. No such implementation is certified here.

Writing `S=sum_i(2E_i+1)`, one has `S/B≤G<S/B+K`, proving the envelope
`K+B+S/B`. Its unconstrained optimum is `K+O(sqrt(S))` for K≥1. This is
conditional on acquiring a suitable base at the chosen B; if that base cannot
be supplied, neither the optimum nor a free restart is justified. If coverage
is absent, failure means only that these supplied certificates found no factor,
not that N is prime.

## 5. Linear and dyadic one-fifth envelopes, including acquisition

For integer Q0≥1, continued fractions of the public rational `-N/X²` give
`1≤q≤Q0` and `|q(-N/X²)-a1|≤1/Q0` in polynomial bit time. A terminating
convergent with denominator at most Q0 is exact; otherwise the last convergent
before its denominator exceeds Q0 gives the bound. Negative slopes cause no
special difficulty. Set a0 to a nearest integer to qN/X.

The exact degree-one reciprocal remainder gives the rational certificate

    |A(h)-qN/(X+h)|
      ≤ 1/2 + H/Q0 + q N H²/X³
      ≤ 1/2 + H/Q0 + Q0 N H²/X³.

Round this bound outward. On a balanced range `N≍X²`, `1≤H≤X`, choose an
integer Q0 comparable to `sqrt(X/H)`. Then `E=O(1+H^(3/2)/sqrt(X))`.
For `K=O(X/H)`, the constant-error contribution `sqrt(K)` is absorbed by K,
leaving `X/H+(XH)^(1/4)`. Balancing gives `H≍X^(3/5)` and cost
`X^(2/5)=N^(1/5)`. This calculation passes.

Here is an explicit rounding/coverage completion for the claimed exponent.
Let `t=ceil(N^(1/5))`, obtained by integer arithmetic, and first screen for
prime divisors at most `M=t²`. The square-root interval-product bound is
`O(t poly(log N))` [Harvey, Proposition 2.5](https://arxiv.org/html/2010.05450#S2.SS3).
Handle the finitely many small-N rounding exceptions directly. If the screen
does not return a factor, cover the remaining integers through `isqrt(N)`
by dyadic ranges `[Y,2Y)`, starting at Y=t² and truncating the last range.
For each range use

    H=floor(Y/t),       Q0=floor(Y/t²),

and truncate each final block as needed. If U is its actual left endpoint,
approximate `-N/U²` with that Q0 and round qN/U for its intercept. Since
`Y≥t²`, these parameters are positive, with

    H/Q0 ≤ 2t,
    Q0 N H²/U³ ≤ N/t⁴ ≤ t.

Thus the same public integer bound `E=3t+1` works for every block, and each
range has at most `2t+1` blocks. There are `O(log N)` ranges. Choose the
shared baby size B=t. Then `K=O(t log N)`, every block has O(1) giants,
and `G=O(t log N)`. Coefficients, bounds, shifts and exponents all have
`O(log N)` bits. Continued-fraction acquisition and certifying each bound
cost polynomial bit time per block, already within the same exponent.

Base acquisition is not an assumption about random elements. Harvey's
Proposition 2.7 supplies, for `N^(2/5)≤D0≤N`, an element of order greater
than D0, a proper factor, or a primality conclusion, in
`O(sqrt(D0) log²N)` bit time. Use `D0=t²` here, treating small exceptions
directly. This costs `O(t log²N)` and supplies more than the required order.
The imported theorem is stated for arbitrary N; I checked its statement and
use, not Hittmeir's underlying proof. [Primary statement](https://arxiv.org/html/2010.05450#S2.SS4)

Every composite has a prime factor at most its square root. It is either found
by the small-factor screen or covered above; the consumer proof does not require
the cofactor to be prime. This establishes how the linear construction can be
completed at **known** `N^(1/5) poly(log N)` scale using imported primitives.
It is not an implemented splitter, a refined machine proof, a new bound, or a
claim to Harvey's precise logarithmic factors. In the general envelope, a
possible acquisition choice is `D0=max(ceil(N^(2/5)),B)` when at most N;
its square-root cost must be added before optimizing B.

## 6. Weighted Dirichlet table: necessary correction of its regime

The small-tolerance calculation is algebraically correct where applicable.
Let `D_d=d(d+1)/2`. With fixed-degree constants to divide the total error
among coordinates, the denominator budget is

    q ≤ O_d(H^D_d/E^d).

At balanced N, the Taylor budget is `q H^(d+1)/X^d≤O(E)`. Equating these
sufficient budgets gives

    E ≍ H^((d+2)/2)/X^(d/(d+1)).

Balancing `K=X/H` with `sqrt(KE)` gives E≍K and

    H ≍ X^[2(2d+1)/((d+1)(d+4))],
    cost exponent in N = (d²+d+2)/(2(d+1)(d+4)).

But the pigeonhole box count is, in general,

    q ≤ O_d(product_(j=1)^d max(1,H^j/E)),

not a product allowing fewer than one box in a coordinate. Coordinates whose
tolerance is already of constant size or larger must saturate. Equivalently,
an unconstrained coefficient can be rounded with error at most 1/2, but it
cannot contribute a fractional factor that reduces the number of boxes needed
in the other coordinates.

At the formal optima the exponents of E/H in X are respectively
`-1/5, -1/9, 0, 1/10` for d=1,2,3,4. Therefore:

- d=1: `1/5` is within the small-tolerance regime; continued fractions price
  acquisition as above.
- d=2: `2/9` is a valid sufficient-budget optimization in that regime;
  constructive acquisition is still a separate obligation here.
- d=3: `1/4` is a boundary value. Constant factors and saturation affect its
  constants, not this exponent.
- d=4: `11/40` lies outside the regime and cannot be presented as the
  resulting sufficient budget. At its formal `H=X^(9/20),E=X^(11/20)`,
  the missing first-coordinate saturation underprices q by `X^(1/10)`.

For d=4 with coordinate 1 saturated and coordinates 2,3,4 active, use
`q≤O(H^9/E^3)`. The Taylor budget becomes

    E⁴ ≍ H^14/X⁴,       E ≍ H^(7/2)/X.

Set `E≍X/H` to balance the list costs. This yields
`H≍X^(4/9)`, `E≍X^(5/9)`, `q≤O(X^(7/3))`, and cost
`X^(5/9)=N^(5/18)`. The regime is consistent: `E/H` grows, while
`E/H²` decreases. This is the corrected saturation-aware sufficient-budget
optimum. The required tolerance constants can be allocated among the fixed
number of coefficients and remainder without changing exponents.

None of these denominator budgets is a lower bound on the actual denominator,
the error of correlated reciprocal coefficients, or any factoring algorithm.
Merely exhibiting pigeonhole boxes does not provide a fast search through them.
Even a degree-at-most-four method can choose the linear construction instead;
`5/18` is not a lower bound on every quartic algorithm. The parent's conclusion
that this generic higher-degree recipe supplies no improvement survives, but
its fourth numerical entry requires replacement or explicit labeling as an
invalid-regime formal extrapolation.

## 7. Rational normalization (4)–(5) and its exceptions

Assume A and B have integer coefficients. Monic division gives
`B(x)=xC(x)+b`, with b=B(0), and define `U=A-NC` (the note calls U `A'`).
For `N=pQ`, cancellation of `pCQ=NC` proves

    A(p)-B(p)Q = U(p)-bQ.

At x=1 and for arbitrary x, direct polynomial algebra gives

    A(1)-NB(1) = U(1)-bN,
    x(A(x)-e)-NB(x) = x(U(x)-e)-bN.

These prove (4)–(5). More strongly, the residual identity holds at every nonzero
real x, `A(x)-B(x)N/x=U(x)-bN/x`, so a uniform bound on the *residual
numerator* is preserved, not just its value at factors. Coefficient values and
bit lengths need not remain equal; subtraction and translation must be charged.
For fixed degrees and polynomial-sized encodings these are polynomial bit costs.

In block coordinates use

    B_h(h)=(X+h)C_h(h)+b,    b=B_h(-X),    U_h=A_h-NC_h.
    D=A_h(1-X)-N B_h(1-X)=U_h(1-X)-bN,
    (X+h)(A_h(h)-e)-N B_h(h)
      =(X+h)(U_h(h)-e)-bN.

Thus the block remainder is B_h(-X), not B_h(0). Evaluation for the public
exponent is at `1-X`, not 1 in h coordinates. The frozen note's statement is
correct; the certificate verifies a nonconstant example with B_h(0)=61 and
B_h(-5)=-4.

To apply the original positive-denominator consumer:

- If b>0, take q=b and A=U.
- If b<0, take q=-b, A=-U, e_new=-e and D_new=-D. The same absolute bound E
  works and the recovery polynomial is negated, preserving its roots.
- If b=0 and U is nonconstant, a separately stated q=0 extension is valid:
  for each e the polynomial `x(U-e)` is nonzero of fixed degree. Ignore its
  root 0 by the proper block/divisor tests. The same collision proof applies.
- If b=0 and U is a constant t, the true error is t for every factor and
  the true-error recovery polynomial is identically zero. This certificate
  supplies no factor localization. Exclude it from the coverage claim or
  explicitly charge another recovery method; do not invoke finite root isolation.

For N≠0 the full characterization is exact. If `x(U-e)-bN` is the zero
polynomial, its value at zero forces b=0; then the integral-domain polynomial
identity `x(U-e)=0` forces U=e. The converse is immediate. The exact reciprocal
`A=N,B=x` has U=b=e=0. More generally `A=N+t,B=x` has U=t and remains
degenerate at e=t. In contrast `A=N+x,B=x` normalizes to U=x,b=0 and gives
`x(x-e)`, which is not identically zero; b=0 alone is not enough to reject it.

The rational-error formula
`e=B(p)(A(p)/B(p)-N/p)` requires B(p)≠0. When B(p)=0, the integer residual
and normalization still make sense, but a bound on that undefined ratio supplies
no certificate. To use a rational approximation bound, certify the denominator
domain and multiply by an actual magnitude bound for B on the relevant inputs.
For fixed-degree polynomials, even a conservative coefficient-sum magnitude bound
is computable; a smaller useful bound needs its own proof and cost.

There is no remaining mathematical overclaim once these guards are explicit.
Normalization does not prove rationally acquired certificates useless, nor that
all such strategies reduce algorithmically to an already-priced generator.
They may acquire useful U,b,E in a different way. It proves preservation of this
specific residual, exponent and recovery equation, while denying the inference
that small *ratio* error automatically means a small searchable integer error.

## 8. Primary machinery mapping and formal scope

In [Harvey's primary text](https://arxiv.org/html/2010.05450), §2.2 supplies
polynomial products and evaluation on a geometric progression. §2.3 supplies
the small-factor screen; §2.4 supplies paid large-order acquisition. Algorithm
4.2 checks component orders, sorts tagged global matches, tries quadratic
recovery, then removes them before Algorithm 4.1. Proposition 4.2 uses the
same uniqueness argument to preserve a true collision. Its theorem has a
prime/semiprime coverage contract; the arbitrary-composite consumer proof above
is independently justified and is not attributed to that contract.

For `A(h)=a0-a1h`, the exact error equation rearranges to
`a1 p+qQ=a0+a1X-e`. This is the relevant linear-combination form. The higher
degree recovery polynomial changes the finite recovery step, not the identified
shared-power search machinery. No claim of historical priority is made for
either the broader formulation or normalization identities.

I **actually inspected a frozen copy** of
`Factoring/ResidualNormalization.lean`, SHA-256
`e0bbeef165e0b3947d4686d6a38998c48c9dbe9ed46207b366548fe4a81072e1`.
See the [Lean source manifest](W013-hidden-period-review-evidence/lean-source-manifest.json).
Its five statements express pointwise residual conservation, pointwise recovery
conservation, public-exponent conservation, nonzero evaluation at zero when
N and b are nonzero, and the exact-reciprocal zero expression. Their mathematical
statements agree with this audit. They do not formalize polynomial division,
block-coordinate substitution, zero-polynomial iff, modular transfer, collision
correctness, approximation acquisition, or complexity. I did not edit, compile,
run an axiom audit, or certify the parent's build of that file. This is source
and mathematics inspection, not a new Lean verification claim.

## 9. Scoped evidence, failures, and next action

The [preregistered certificate](W013-hidden-period-review-evidence/preregistration.md)
fixed thirteen cases and budgets before script creation/execution. Its
[script](W013-hidden-period-review-evidence/certificate.py) completed once:
**13/13 cases, 205 assertions passed, exit 0, empty stderr**. The
[exact JSON output](W013-hidden-period-review-evidence/certificate-output.json)
and [run manifest](W013-hidden-period-review-evidence/certificate-run-manifest.json)
preserve all branches. Script SHA-256 is
`c07273c18fc22abe3417e2620a47d7d8b6055a9e66d66b619e4f705699a2c2bb`;
output SHA-256 is
`d381447691766533cd8dde832148d8fdbc8d0467da57eea22f2ee53553d28118`.

The only mathematical failure found in the frozen continuation is the quartic
budget's regime mismatch. The signed-denominator, zero-denominator and domain
guards above are specification completions. There were no failed certificate
assertions, replacement instances, source-download failures, package installs,
benchmarks, parameter sweeps, recursive delegation, publication, commits or
shared solver/Lean/state/registry edits. Early combined read output was truncated;
the relevant local passages were re-read in focused calls and retained in full.
No shared build/check was run: shared implementation was untouched, and the
review-owned certificate was executed directly under its fixed budgets. Its
tiny direct quadratic routine does not purport to implement the general root
algorithm or an N-only certificate generator.

The [drift record](W013-hidden-period-review-evidence/source-drift.json) found
concurrent changes to STATE and the continuation. The latter's delivery-observed
hash is `98aa8b95130017e8cb4db59e8fe9acc2c307f7c19e9931f4f7708f5e155d7fce`;
its [preserved diff](W013-hidden-period-review-evidence/consumer-drift.diff) only
updates the next-gate paragraph to describe the parent's Lean identities.
No reviewed mathematical claim changed. I read that diff; STATE's change is
recorded without treating it as a new proof premise. The frozen versions above
remain the principal review authority. The delivery manifest and SHA-256
inventory cover the report and scoped evidence without modifying parent files.

**Parent action:** correct the degree-four sufficient-budget entry, make the
b-sign/zero-polynomial guards explicit, and retain the consumer as known-scale
machinery. A material next proposal must give a paid construction reducing
coverage count K or total certified error S, or a specified shared operation
cheaper than the current explicit lists. Such a proposal needs its own success
and acquisition proof. Neither this accepted consumer nor its exact certificate
establishes a novel or improved complete factoring algorithm.
