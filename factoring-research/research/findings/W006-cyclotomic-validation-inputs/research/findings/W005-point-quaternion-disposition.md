# W005 — point and quaternion dispositions

Date: 2026-10-08. Verified new complete factoring improvement: **NONE**.
The parent consumed the complete A, B (including its sampler-law supplement),
and D reports. Their original reports and the parent's provisional submissions
remain unchanged. C has its separate accepted strip disposition. These are
reviewed mathematical deductions, not new Lean theorems or numerical evidence.

## Moving-trace points (A)

Accept the explicit section and its generic infinite-order proof, the genus-3
square cover and involution, the valuation obstruction for r=1+N/K, and the
modified branch's removal of that local obstruction. Infinite order over the
function field does not certify every rational specialization or useful lifts.
Accept the nodal reduction and its stronger consequence: the displayed section
reduces to lambda=4, so scalar multiplication there supplies a base-4 p-1
computation, not fresh ECM orders.

Correct the parent: nonsquare 5 obstructs the displayed point's square lift,
not all multiples. The review's k=3 square classes demonstrate the distinction.
The variable-c modular trace condition is s congruent to (1+c^2)R, not literal
equality; equality would split the rational quadratic. All mentioned divisors
and a in a^2=1+c^2 must be units before modular use.

Accept the fixed-u quartic's good-reduction model and generic non-torsion
seed difference. At fixed modular c, varying its twist gives **at most** two
quadratic twist classes, not two guaranteed distinct orders. The relevant
Montgomery families and square-triple construction have prior art. Rational
point height, modular trace eligibility, field distinctness and useful
ordinary-square completion remain unpaid.

## Quaternion extraction and actual sampler (B)

Accept the primitive odd-norm, norm-unit single-reflection equality:
both quaternion gcd norms equal gcd(N,2<w,A>). The factor 2 handles half-integral
Hurwitz coordinates. This rejects that reflection's extra splitting claim.
It does not cover exact cancellation of nonunit raw denominators or arbitrary
pairs. For arbitrary integral B and primitive A of odd norm N, adopt the
coefficient-content formulas for the right and left gcd norms, retaining
handedness and an integral Hurwitz basis.

The norm of A-B only gives a divisibility condition; a full scalar gcd N
does not rule out a proper quaternion gcd. The symbolic norm-15 example
correctly refutes that broader assertion. A*i is an explicit cancellation
escape, but fails for the specified remaining-input four-squares sampler.

Accept the precisely fixed Pollack–Treviño sampler variant and its **separately
derived** right-kernel law in the supplement. Conditional on successful r and
all auxiliary randomness, norm-fiber bijection (S2) gives independent uniform
lines in Omega_(p,e), of size p^(e-1)(p-chi). Gcd extraction and left-unit
normalization preserve them. This proves the stated match tails and the
balanced-semiprime Theta(N^-1/2) one-pair success rate. It does not establish
an image law or license adaptive right-unit normalization. The published
expected polynomial acquisition cost is charged; this is a scoped use of
the cited theorem, not a reproof of every analytic input in that paper.

The new useful computation is coefficient-content extraction without quaternion
quotients. Independent pair sampling still has the old rare-match cost.
Birthday samples alone do not pay for all-pairs detection or improve factoring.

## Orthogonal twins (D)

Accept N dividing g_V*g_W for every integer equal-norm orthogonal pair with
odd norm N, without needing primitivity. Outside the at-most-twelve signed
left/right unit rotations, both content gcds are proper. Accept the explicit
rank-three lattice basis, exact quadratic slice scan, and its bit accounting.
The N^(2/3) scan estimate requires a well-conditioned basis, not merely short
columns; it is not a new best upper bound.

Accept the sharper denominator statement: the reduced denominators of the
unique one-sided multipliers are N/g_V and N/g_W, whose product divides N.
Useful outputs therefore have nontrivial cancellable numerator content.
**Correct the parent's broader rotation claim:** an invertible left multiplier
modulo p preserves the right kernel; an invertible right multiplier preserves
the image. General rotations need separate analysis. The review's integral
two-sided counterexample is valid and uses an already factored construction.

The parent's review also accepts the reverse reduction: with primitive integer
A of odd norm N and a supplied proper divisor f, a Hurwitz gcd supplies
A=P*Q with Norm(Q)=f. At most one axis is exceptional for each of P and Q;
one of P*i*Q, P*j*Q, P*k*Q is therefore a useful twin. The primitivity and
odd-norm argument excluding two signed axes is sufficient. This is polynomial
work after a supplied factor, not a factor-blind generator. Thus with A
supplied, useful-twin search and factoring reduce to each other; a complete
shell scan cannot fail on that promised composite domain. The existing
factoring algorithm plus this construction is the appropriate upper-bound
comparator. The twin factoring connection is explicit prior art.

## Constructive continuation

The extraction failures identify acquisition and correlation as the central
costs. E's separate blinded Norm2 sampler changes the joint auxiliary
generation computation and remains under review. It does not change the
standalone N,R-only contract. The parent is developing an explicit
compatible-field construction and examining its root-choice dependence.
No useful packet probability or general factoring improvement is accepted.

Reports: [A](W005-point-validation.md), [B](W005-quaternion-validation.md),
[B's distribution proof](W005-quaternion-validation-sampler-law.md),
[D](W005-orthogonal-review.md), [C disposition](W005-strip-disposition.md).
