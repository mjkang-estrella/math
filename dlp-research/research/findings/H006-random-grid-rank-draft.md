# H006 T1: reviewed restricted random-grid dense-core obstruction

Root proposed the rank lemma; native Astra /root/h002_arithmetic_ideas independently
checked/developed this argument. Claude Opus independently accepted the scoped
paper argument subject to the repairs incorporated below. Raw objections are in
H006-rank-review-opus-raw.md. This file keeps its original draft path for traceability.
No numerical experiment, no Lean proof, no claim about all coordinate algorithms.
The original T1 has not specified a factor-base family: this freezes ONE analyzed
instantiation, not a universal rejection of its unspecified alternatives.

Family: nonsingular short-Weierstrass E/Fp, p>3, full odd prime order q comparable
to p; X_E is the valid affine x set, sizeN=(q-1)/2. Draw V uniformly without
replacement, |V|=B approximately q^(1/5), independently of uniform nonidentity R.
Use the SAME V in all five S6 tensor modes, and explicit dense TT cores throughout
an input-independent positive addition chain for entrywise powering to p-1.
Take B=q^(1/5+o(1)). Valid-x sampling can use rejection/root
checks; no full X_E table is free setup. All ordinary algorithm costs remain paid.

## Formal polynomial rank

If F(x0,y0)=0 and Fx(x0,y0)Fy(x0,y0)!=0 over an extension field of characteristic
p, and0<=t<p, expand F(x0+X,y)^t=sum c_k(y)X^k. For0<=k<=t,
ord_(y0)c_k=t-k. The unique least-order contribution is
binom(t,k)*Fx(x0,y)^k*F(x0,y)^(t-k); other partitions choose fewer nonconstant
factors and vanish more. Binomialcoefficients are nonzero since t<p. Therefore
c0..ct are independent, giving coefficient separation rank>=t+1. This alone
says nothing about a particular finite evaluation grid.

Evaluation bridge: for a polynomial G of coefficient separation rank at least r,
det[G(x_i,y_j)] is a nonzero polynomial. Over an infinite algebraic closure,
evaluation functionals span the dual of any finite-dimensional polynomial space:
otherwise a nonzero polynomial would vanish at every point. First choose y_j
so r column polynomials G(x,y_j) are independent, then choose x_i so their
evaluation matrix is invertible. This gives one nonzero determinant evaluation,
proving polynomial nonzeroness. Extension of the field does not change rank.

## S6 specialization

For generic geometric P3,P4,P5,R, the eight signed sums K=+/-P3+/-P4+/-P5+/-R
modulo global sign are distinct modulo sign and avoid E[2]. For K outside E[2],
P -> (x(P),x(P+K)) is generically injective with separable degree2 projections.
Its image C_K is an irreducible(2,2) curve defined by S3(x,y,x(K)). Indeed the only
possible second preimage is -P, and x(P+K)=x(P-K) forces 2P=0 or 2K=0.
C_K=C_K' only when K'=+/-K. Both degree-two projections are separable for p>3.
The defining zero property of S6 forces
F(x,y)=S6(x,y,x(P3),x(P4),x(P5),x(R))
to vanish on all eight curves. Nonzero specialization is a nonempty open condition
because S6 is nonzero and the x-map is dominant. Distinct signed sums and avoidance
of E[2] are also nonempty open conditions; their intersection in irreducible E^4
is nonempty. Degree bounds(16,16) force their product up to a
nonzero scalar, with no extra multiplicities. A generic point on one component
avoids the others and both projection-ramification loci, so FxFy!=0.
Each component's partial derivatives are nonzero on a dense open set: an
irreducible (2,2) polynomial cannot divide a nonzero partial of smaller degree,
and degree 2<p prevents identically vanishing partials. Remove these finitely
many exceptional points and intersections to obtain the required mixed point.
Semaev Theorem1 is the source of degree/symmetry/zero properties:
https://eprint.iacr.org/2004/031
The product/smooth-point reasoning is the reviewer's derivation, not a quoted theorem.

## Common finite valid-x grid

Let r=floor((B-3)/2), with r>=2 and 2r<p. In the fixed positive addition chain,
let t be its first exponent >=r. Both parents are <r, so r<=t<=2(r-1)<p.
This applies to either binary direction; left-to-right visits prefixes, not
powers of two. The draft's earlier power-of-two wording was incorrect.
Allocate r distinct V coordinates to rows, r to columns,3 to fixed c1,c2,c3,
using sampling order or another allocation independent of their values.
D=det[S6(x_i,y_j,c1,c2,c3,z)^t]_(i,j=1..r) is a nonzero polynomial by the
rank lemma, evaluation bridge and generic specialization. Include the evaluation variables and
fixed-coordinate parameters when considering nonzeroness; don't fix a possibly
bad tuple and claim it is good. A conservative total degree is96tr=O(B²).

Sample all these variables from X_E, withz=x(R) independently uniform, then
condition the base-coordinate variables to be distinct. Schwartz-Zippel bounds
zero probability before conditioning bydeg(D)/N; conditioning incurs division
by the distinctness probability, which is1-O(B²/q). Thus jointly overV,R,
Pr[D=0]=O(B²/q). This is not a statement for each predetermined V, nor a uniform
conditional success guarantee after adaptively choosing V or R.

D occurs in the2|3 unfolding with rows(x_i,c1), columns(y_j,c2,c3), and in the
3|2 unfolding with rows(x_i,c1,c2), columns(y_j,c3), by symmetry. Thus the same
event, without a union bound, gives both unfolding ranks>=r.
Every exact TT consequently needs middle dense core size r2*B*r3=Omega(B³)
=q^(3/5+o(1)). Materializing that core alone asymptotically exceeds square-root
work/space. Every unfolding factors through its TT bond; hence its rank is at
most the bond dimension. Oseledets §2 describes these cores; Theorem2.1 is the
converse existence/upper-bound direction, not the lower-bound citation:
https://users.math.msu.edu/users/iwenmark/Teaching/CMSE890/TENSOR_oseledets2011.pdf

The first-attempt expected materialization cost is at least(1-o(1))*B*r².
This is asymptotic, not a finite-size speed comparison. It does not reject
B<=q^(1/6), different m, sparse/implicit cores, a circuit avoiding
materialized powers, other hierarchical formats or structured/adaptive V.
The joint high-probability first-attempt obstruction suffices for this specified
uniform-target dense schedule; no unexplained per-relation independence required.

## Costs and relation recovery qualifications

Proposed raw-product coresO(Br^4), exact eliminationO(Br^6) and suffix-span entry
extraction are plausible conservative upper bounds; numerical orthogonality is
unnecessary over finite fields. Explicit S6 circuit construction has fixed but
potentially enormous constants and cannot be silently free in a practical claim.

Direct-Q recovery needs LESS statistical rank assumption than the proposer used:
independent uniform a,b make R=aG+bQ uniform and b independent of R. If decomposition
and row selection depend only on R,V and independent coins, the sign-folded
factor-base matrix M is independent of b labels. AfterB+1 valid relations, choose
any nonzero left dependencylambda(M). Thenlambda*b!=0 with probability1-1/q and
k=-(lambda*a)/(lambda*b). Full rank of M is not necessary. Yield and an actual
sparse randomized dependency algorithm/preconditioning/retries still need costs;
selection based on a,b would require another independence proof. This correction
does not rescue the intermediate-rank assumption.

D1 independent-target orbit yield is at most2^mB/q, so the named method requiring
Omega(B) relations paysOmega(q) expected trials; this is not a universal adaptive-
selection or arbitrary dependency-search bound. No experiment warranted for it.

Disposition: reject this random-V dense T1 schedule on reviewed paper evidence;
retain structured/adaptive V or different core representations as unspecified
alternatives requiring an actual mechanism and paid intermediate-work argument.
