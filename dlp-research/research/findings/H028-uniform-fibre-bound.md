# H028 uniform collision-fibre bound for the Miller-coefficient key

2026-10-08. Accepted independently checked PAPER proof, not a Lean theorem.
Astra found the residual-line argument during a focused fibre investigation.
NEW native Sol adversarial review checked the polynomial and exceptional cases.
Claude Opus r2 independently derived the same bound in its cost review, before
receiving Astra's finding. Root checked factorization, ordered-pair counting,
normalizations and implications. No experiment or complete-work gain claimed.

## Hypotheses and exact finite bound

E/Fp is nonsingular short Weierstrass y²=x³+Ax+B, p>3, full group prime order
q>3, q!=p. Use exact h(P)=a_P/q from accepted H027 local Miller construction,
h(O)=0, h(-P)=-h(P), and h(P+Q)=hP+hQ-lambda(P,Q) for finite nonvertical
addition, with tangent case included. No arbitrary learned/provisional key.

For nonidentity points define c(a)=#{P!=O:hP=a}, N=q-1,
M2=sum_a c(a)², c0=c(0). For each T!=O, count ordered equal-h pairs P,Q!=O
with P-Q=T. Then P=Q+T!=O excludes Q=-T, and

    hP=hQ  iff  lambda(Q,T)=hT.

Write T=(x,y), v=hT. On the finite line L(X)=y+v(X-x),

    X³+AX+B-L(X)²
      = (X-x) [X²+(x-v²)X+x²+v²x+A-2vy].

The bracket is MONIC quadratic. Each admissible Q!=T must be a root; its y
coordinate is fixed by the line. Q=T is included only if the line is tangent:
the residual evaluated at x is3x²+A-2vy, exactly the tangent condition.
It therefore consumes a residual root, not an extra intersection.

Q=-T is impossible on this line: at x it has ordinate y rather than -y.
There is no nonzero rational two-torsion in an odd-order group, so y!=0.
The finite-slope projective line does not contain O. A repeated residual root
counts once; an inflection leaves (X-x)², also only one candidate.
Conversely every rational residual root supplies an admissible Q and P=Q+T.
Thus at most2 ordered pairs have any given nonzero difference T.

The diagonal contributes N, and off-diagonal differences are unique. Hence

    sum_a c(a)(c(a)-1) <= 2N,
    M2 <= 3N.

Let d_t count NONIDENTITY points in canonical signed key bucket
min(rep(h),rep(-h)). Oddness gives c(a)=c(-a), so

    S2=sum_t d_t² = 2M2-c0²,
    1 <= rho=S2/(2N) <= 3-c0²/(2N) <= 3.

This is an aggregate second-moment bound, NOT a constant maximum-fibre claim.
Neither a random-function model nor an asymptotic point-count assumption enters.

## Exact discriminant consistency identity

The residual discriminant is

    Delta_T=v^4-6xv²-3x²-4A+8vy.

Over Fp, with quadratic character chi(0)=0, its number of distinct roots is
N_T=1+chi(Delta_T). Thus the exact consistency identity is

    M2 = N + sum_(T!=O) N_T = 2N + sum_(T!=O) chi(Delta_T).

Root/Astra checked this using the explicit quadratic; it is useful for the
diagnostic. It is NOT an operation the production solver must perform.

Astra additionally observed that repeated residual roots Q satisfy T=-2Q and
hQ=0; conversely each such Q yields a repeated root for T=-2Q. Root checked
these implications by tangent addition and oddness. This gives exactly c0
zero discriminants and the optional sharper bound
rho <= 3-c0(c0+2)/(2N). The simpler rho<=3 is sufficient for the candidate.

## Consequence for every input, after paid randomization

Use independent uniform s in Fq*, r in Fq, G'=sG, Q'=Q+rG. For fixed I
nonzero baby indices and J giant indices under full deterministic caps, actual
identity giants are dispatched before bucket lookup. The previously independently
checked finite expectation gives

    E(false matched records) = IJ*(S2-2N)/(q*N) <= 4IJ/q,
    E(all nonidentity raw matched records) = IJ*S2/(q*N) <= 6IJ/q.

Each original input Q has this law; the expectation is over paid s,r.
Dependence among record pairs does not matter. Early-stopped counts are bounded
by nonnegative full-cap counts. With I,J=O(sqrtq), expected refinements are O(1).

All fibre tables/discriminants here are PROOF devices, not advice, preprocessing
or an uncharged inverse lookup. This removes the candidate's former unproved
bounded-fibre-moment premise. Numerical rho values now check implementation
consistency; they are not evidence needed to assert an asymptotic moment bound.

## What remains open

One-square lazy reconstruction gives O(1) expected field refinements, with paid
archives/accesses/setup/final verification. Opus also proposed trying both signed
scalar candidates on every raw match: O(logq) expected verification work and no
archive. NEW Sol complete-cost review is checking that alternative; it is not
a measured or accepted complete-work advantage.

The regular key-generation saving remains2kell squarings per H019 block, but
field additions, canonicalization, record format, lookup/memory, finite batching,
exceptions and setup must be compared explicitly. No wall-clock, GPU, exponent
or matched complete-solver improvement is yet established. No universal
lower bound or novelty claim. A focused executable diagnostic is now justified,
after the exact protocol and code are independently checked.
