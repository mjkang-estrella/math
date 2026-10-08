# H013 coordinate cards: concrete bridges and their paid obstacles

2026-10-08. Native Astra /root/h006_structured_relation_ideas independent
proposer; root checked calculations and qualifications below. No experiments,
new Lean claims or validated improvement. Known tools are not discoveries.

## Predeclared slope hashing

Sample L iid uniform affine-labelled points P_i=a_iG+b_iQ. Before the points,
choose H finite slopes. For each slope lambda bucket c_i=y_i-lambda*x_i.
Three distinct points in a bucket sum to O, yielding
k=-sum(a_i)/sum(b_i) when sum(b_i)!=0. Verify each recovered scalar. Infinity,
tangencies, repeated points and duplicate-point recovery are separate cases.

A fixed slope has at most(q-1)/3 three-distinct-point fibers. An iid index
triple has probability at most2/q^2 of forming such a fiber, so expected
certificates <=2H*binom(L,3)/q^2. Constant success THROUGH THIS CHANNEL requires
H*L^3=Omega(q^2). Literal HL scans plus L seed setup therefore require at least
Omega(q^(2/3)) work at a fixed budget: W>=HL and W>=L imply HL^3<=W^3.
Scalar starts, sorting, labels, verification and unsuccessful buckets only add
cost. Sequential slopes need O(L) stored records. Duplicate-point recovery can
already reach square-root; it does not make the triple channel a new gain.
This bound does not cover adaptive slope choice or every expected-stopping rule.
Prior-art lead: [Diem](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.815.pdf).
No prototype warranted for this literal operation.

## Labelled differential pair walk

State P=aG+bQ, S=cG+eQ and u=x(P),v=x(S),w=x(P-S). For y^2=x^3+A*x+C,

    z=x(P+S)=2*((u+v)*(u*v+A)+2*C)/(u-v)^2-w.

An independent coin replaces (P,S) by (P,P+S) or (P+S,S); the new difference
x-coordinate is v or u. Emit z with label(a+c,b+e). An x collision gives either
signed relation; both need denominator checks and final scalar verification.
Infinity/equal-x handling must be explicit and paid.

The literal formula costs3M+S+I plus additions/small constants; batched inversion
approaches6M+S per emission. This corrects an earlier provisional6M+2S ledger.
The existing block x-coordinate comparator in H006-net-schedules-proposal.md
approaches2.5M+S with paid block storage/setup. This is an arithmetic screen,
not a full-cost proof that every pair walk loses. The comparator is a different
sequence and collision yield/stopping still matters. No measured gain.

A collision in one emitted coordinate does NOT merge the complete two-point
state. The proposal supplies a high-memory collision table, not a proved
low-memory rho mechanism. A simple fixed-coefficient union bound only applies
when coefficient words are secret-independent. Coordinate-dependent exceptional
reseeding invalidates that conditioning shortcut; a full adaptive analysis was
not supplied. Root retains this disagreement rather than silently accepting a
generic lower-bound claim. Known xADD lead: Brier--Joye, BJ02espa.pdf on Joye's
author site. No engine without a favorable complete-work mechanism.

## Lang preimage and elliptic basis: actual recovery, expensive construction

Assume p>17, #E(F_p)=q odd prime, q!=p. Write pi for Frobenius and phi=1-pi,
a normalized separable degree-q isogeny with kernel E(F_p). The literal card
enumerates jG for every j, forms the normalized Velu map with codomain identified
with E, and writes phi_x=N/D. Let h(X)=N(X)-x(G)D(X).

For b in phi^-1(-G), pi(b)=b+G, so its orbit has length q. Its x-conjugates are
distinct: pi^i(b)=-b would imply2b=-iG, contradicting phi(2b)=-2G!=O. Thus h is
irreducible of degree q. In K=F_p[X]/h, y(b)=-y(G)/phi_x'(X) follows from the
normalized differential; the inverse is nonzero. All of this construction is
paid, not a primitive extension-field oracle.

Root checked [Couveignes--Lercier §3.1, Lemma1](https://www.math.u-bordeaux.fr/~jcouveig/publi/ellbasisrev.pdf):
if qb!=O, the functions omega_0=1, omega_j=u_(O,jG)(b) form a basis. On a short
Weierstrass model u_(O,jG)(b)=(y(b)+y(jG))/(x(b)-x(jG)). Here qb!=O follows
because Hasse gives q>(p-1)/2, so q cannot divide p-1; Frobenius on E[q] has
distinct eigenvalues1,p. If qb=O, then(pi-1)b=G and(pi-1)^2b=0 contradict that
semisimplicity. The paper's basis theorem, not its fast arithmetic alone, is
the relevant bridge.

For Q=kG!=O, v=u_(O,Q)(b) equals omega_k. Converting v to this basis therefore
reveals the index k and verification closes recovery. This genuinely contains
the scalar; public dependence is not an information-theoretic dismissal.

But the supplied construction already enumerates q points, Omega(q) work, and
could directly solve the target by comparing during that enumeration. A literal
q-by-q conversion matrix and naive cubic elimination cost still more. These are
costs of THIS explicit construction, not a theorem that extension degree forces
all compressed implementations to take q time. A sub-square-root compressed
basis construction and sparse-index extraction would be new paid operations;
none is specified. Preserve that opening, but do not build the expensive engine.
