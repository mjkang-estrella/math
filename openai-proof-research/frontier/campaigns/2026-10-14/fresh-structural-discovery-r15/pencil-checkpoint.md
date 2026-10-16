# Checkpoint: one-fresh-coordinate affine pencil extensions cannot work

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
This is a separate attempted construction, not a subclass replacement for LR.

Let q>=3 be a prime power and D the q+1 affine-plane directions. In part d
make one old vertex [d,L] for each affine d-line L, and any finite set T_d
of fresh vertices, all labels in all parts disjoint. For any chosen subset
X of F_q^2 use the ordinary edges

 e_x={ [d,x+d] : d in D }, x in X.

Allow any finite set of exceptional edges, each of the precise form

 f(p,g,t)={t} union { [d,p+d] : d in D, d!=g }, t in T_g.

Here p is any affine point. Centers, omitted directions, fresh labels,
ordinary points, and their numbers are arbitrary. Equal edges are retained
only once. Suppose the resulting nonempty hypergraph H is linear and
intersecting. Then EVERY part has at most q nonisolated vertices, and
therefore tau(H)<=q=r-1. Thus this whole construction cannot witness LR.

Proof. Fix an exceptional edge f=f(p,g,t), and write L=p+g.
No ordinary edge e_x can have x on L. For x=p, its intersection with f
has q old vertices, violating linearity. For x!=p on L, the only direction
in which the two pencils agree is g, and that label is omitted from f;
they are disjoint. Consequently the old label [g,L] occurs in no ordinary
edge.

It occurs in no exceptional edge either. An exception with omitted
direction g has a fresh vertex in that part. An exception f(p',h,t') with
h!=g could contain [g,L] only if p' lies on L. If p'=p, the two exceptions
share q-1 old labels, at least two since q>=3. If p'!=p, their unique
possible common old label would have direction g, omitted from f; they
have no common fresh label, because their fresh labels lie in different
parts. This would make them disjoint. Both cases are excluded. Thus
[g,L] is an UNUSED old vertex of part g in the entire H.

For each used fresh label t in part g, all centers of exceptions using t
lie on one g-line L(t). Otherwise two such centers have joining direction
h!=g, and the two edges share both t and [h,p+h], contradicting linearity.
The preceding paragraph shows that [g,L(t)] is unused.

The assignment t -> L(t) is injective on used fresh labels in part g.
If two different fresh labels had centers p,p' on the same g-line, then
p=p' would give q common old vertices, and p!=p' would give no common
old or fresh vertex. Either violates the hypotheses. Hence each used
fresh label pays for a DISTINCT unused old label. If u_g old labels are
unused, then |T_g used|<=u_g, and the total number of nonisolated vertices
in part g is at most (q-u_g)+u_g=q. If no exceptions use part g, that
bound is immediate. Selecting all nonisolated vertices of any part covers
all edges and proves the assertion. The same argument includes X empty.

The motivation was to use the q old labels of a punctured pencil to give
exactly one intersection with ordinary point-edges while adding a fresh
label. Using two or more exceptions with the same omitted line avoids
a degree-one fresh label, but the injection above shows why it still
cannot enlarge the usable part. This is an all-parameter obstruction,
not a finite search. It applies only to exceptions with ONE fresh
coordinate and an ordinary pencil in every other coordinate. Exceptions
with several fresh coordinates or old labels that are not one pencil,
and other linear-space constructions, remain outside the claim.

The elementary finite-plane and covering operations are established
background, not a substantial contribution claim. This theorem does not
assert anything about arbitrary linear intersecting hypergraphs beyond
its explicit construction class.
