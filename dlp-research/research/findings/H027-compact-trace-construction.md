# H027 compact elliptic trace: construction, not scalar recovery

2026-10-08. Native Astra supplied this explicit construction; root checked the
local expansions/divisor calculation and read the relevant Couveignes–Lercier
definitions. Separate native Sol audit COMPLETED, GO for the scoped construction and
weighted differences, incorporating the cost/exception corrections below. A NEW
Factory Opus prior-art review and a separate Sol domain audit completed; see
H027-miller-priorart-reconciliation.md for attribution and corrected scope. Status: independently checked informal
construction; no novelty claim, executable implementation, numerical experiment,
Lean theorem or ECDLP gain claimed.

## Setting and exact proposed identity

Let E:y²=x³+Ax+B be nonsingular over Fp, p>3, with full rational group of prime
order q≠p. For Q≠O put z=−x/y, omega=dx/(2y) and
u_Q(X)=(y(X)+y(Q))/(x(X)−x(Q)), with removable values interpreted geometrically.
Let f_Q be the rational torsion Miller function with divisor q[Q]−q[O], scaled
so that f_Q=z^(−q)(1+a_Q*z+O(z²)) at O. The ratio defining a_Q is independent
of constant scaling. Residues of u_Q*omega at O,Q are −1,+1. On this short
model u_Q=−1/z+O(z) and omega=(1+O(z⁴))dz. Hence

`df_Q/f_Q = (q*u_Q+a_Q)*omega`.

The difference is regular everywhere and its constant multiple of omega is
determined by the first local coefficient at O. All occurrences of q in field
formulas mean its image in Fp.

The product of f_Q(X+T) over all T in E(Fp) has zero divisor: translation by Q
permutes the full group. It is thus a nonzero constant. Taking logarithmic
derivatives and using translation invariance of omega gives
q*(sum_T u_Q(X+T)+a_Q)=0. Since q≠p,

`sum_T u_Q(X+T) = −a_Q`.

A point b with pi(b)=b+G exists by the separable surjective Lang isogeny pi−1.
Its Frobenius orbit has length q and avoids the rational poles. Therefore

`Tr_(Fp^q/Fp)(u_Q(b)) = −a_Q`.

This trace identity does not require the additional qb≠O hypothesis used for
claiming the whole CL Omega family is a basis. No b or extension representation
is actually constructed by the coefficient algorithm below.

Primary interface: Couveignes–Lercier, §§2–3.1, local expansions and explicit
u_(O,Q), https://www.math.u-bordeaux.fr/~jcouveig/publi/ellbasisrev.pdf . Root and
proposer read those passages. The derivation here is not a quoted source theorem
or a claim that the paper supplies an ECDLP decoder.

## Compact coefficient evaluation

Maintain the point U=[n]Q and first normalized Laurent coefficient c_n of the
Miller function f_(n,Q), whose divisor is n[Q]−[nQ]−(n−1)[O]. Start n=1,U=Q,c=0.
Its pole order is mu_n=n−1+1[[n]Q=O], not n uniformly. Only the coefficient
following that leading Laurent monomial is retained.

A nonvertical Miller line/vertical factor, after leading-coefficient
normalization, has first coefficient +lambda(U,V). Thus a binary chain uses

`c_(2n)=2*c_n+lambda(U,U)`,
`c_(n+1)=c_n+lambda(U,Q)`.

Update U by the corresponding group operation. A vertical pair contributes
zero first coefficient because its factor x−x(U) has leading degree−2 and
no next Laurent term. An identity operation contributes zero. Dispatch these
cases explicitly, including the terminal addition reaching O. At n=q, c_q=a_Q.
Handle Q=O separately; set a_O=0 for group identities, not as the CL omega_0
value (omega_0=1 has trace q).

Work: O(log q) affine group operations/slopes and additional field additions,
O(1) field registers plus scalar-chain storage. Inversions are paid. Using
quadratic-bit extended Euclid and schoolbook multiplication yields the proposed
O(log q * log²p) bit bound. Fermat inversion with schoolbook multiplication would
instead give the looser O(log q * log³p) bound. No degree-q function table or
q-term Laurent expansion is constructed. This is a specified algorithmic
construction, not a measured runtime or a verified implementation.

## Addition defect and possible use

Comparing divisors in f_Q*f_R/f_(Q+R) proportional to g_(Q,R)^q gives, for
nonvertical finite operands (including tangent case),

`a_(Q+R)=a_Q+a_R−q*lambda(Q,R)`.

Vertical pairs give a_(−Q)=−a_Q. Thus a_Q is not an additive scalar coordinate.
Along a Miller chain from G, a_([n]G)=n*a_G−q*c_(n,G); the second term is not
independently available at the unknown scalar n just because a_Q is computable.
More generally any exactly additive Fp-valued correction on a q-group would
be zero, since q is invertible in Fp. This elementary observation does not rule
out nonlinear predicates, approximate correlations or other codomains.

The constructive gain is only removal of an alleged full-table requirement for
this particular functional c=1. No scalar-recovery advantage follows. The next
useful gate is a specified defect-canceling operation or mathematically motivated
scalar correlation with a paid decoder, not an unfocused feature benchmark.
Supported ordinary full-solver complexity remains square-root; verified gain NONE.

## Independently checked weighted extension

For fixed rational A≠O and Q≠O,A, the CL product identity gives

`Tr(u_A(b)*u_Q(b)) = X_b + Gamma(O,A,Q)*(a_A−a_Q)+q*(x(A)+x(Q))`,

where X_b=Tr(x(b)). Subtract the same expression at a fixed admissible Q0 to
eliminate X_b. The resulting weighted-trace difference uses a_Q and O(1) extra
base-field operations after paid reference setup. Q=−A uses the removable/tangent
value of Gamma; Q=A and Q=O are outside this formula's stated interface.
Explicitly, the evaluated difference is

`D_A(Q;R)=Gamma_A(Q)*(a_A−a_Q)−Gamma_A(R)*(a_A−a_R)+q*(x(Q)−x(R))`.

Gamma_A(Q)=(y(Q)+y(A))/(x(Q)−x(A)) is not the ordinary chord slope. Its removable
value at −A is −(3x(A)²+A_curve)/(2y(A)); if y(A)=0 then −A=A, already excluded.
For r fixed anchors, generate them with known logs and pay their/reference a-values
once. Each target then costs one Miller coefficient evaluation plus O(r) field
operations and paid inversions, with O(r) fixed storage; eligible inversions can
be batched. Q=O or a known anchor is a direct known-log case. The diagonal trace
has a different X_b coefficient and is not implicitly covered by the formula.

This supplies no independent information beyond (x(Q),y(Q),a_Q), nor arbitrary
bit-weighted dual functionals. Sol checked the extension and returned GO only
for these claims. No experiment or scalar information claim is admitted.

## Review evidence and limits

Astra proposed and developed the two explicit functionals; Sol independently
checked local residues, norm, Lang fibre, Miller pole order and exceptions,
addition defect, weighted formula and bit model. Root checked the same signs
and read CL §2 definitions/expansions plus Ben Lynn's Miller recurrence and final
vertical handling: https://crypto.stanford.edu/pbc/notes/ep/miller.html .
Sol verified the quadratic-bit inversion option against HAC Algorithm14.61 and
Notes14.63–14.64: https://cacr.uwaterloo.ca/hac/about/chap14.pdf .

No empirical runtime or correctness run occurred. No broad rational-degree
obstruction is accepted or needed. An unweighted and a restricted weighted trace
can be cheap without arbitrary dual coordinates being cheap, and cheap public
observables do not alone lower ECDLP cost. Prior-art review identifies the local-coefficient method with established
Rück/Semaev techniques whose recovery theorems use p-torsion. The ordinary trace
construction supplies no extension of those recovery theorems. Remaining
independent H027 idea roles have not yet delivered.
