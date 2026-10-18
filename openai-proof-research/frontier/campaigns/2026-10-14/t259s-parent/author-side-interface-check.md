# T259S author-side interface checks

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. These are parent
author contributions, communicated while the candidate was being written,
not an independent review or an acceptance. The frozen scope is unchanged.
The precise source and scope identities read here are in the adjacent receipt.

## Quotient and missing interior edge

Use the source notation u_0=1, u_i=u_(i-1) a b_i and w=u_99 a. Prescribe
q(a)=d, q(u_1)=c and q(u_i)=1 for i>=2 in F(c,d). These values determine
q(b_1)=d^(-1)c, q(b_2)=d^(-1)c^(-1), and q(b_i)=d^(-1) for i>=3.
As A is free on a,b_i, this defines a homomorphism on A. Extend to the
amalgam by q(t)=1; this respects every relation commuting t with J.
It is surjective since its image contains d and c=q(a b_1). Also q(w)=d.

Suppose an equivalence relation contains all B-edges and contains every
a-edge over a quotient-coordinate set E. The word w has one a-edge
starting at each yu_i, i=0,...,99. All these starting points have quotient
coordinate z except yu_1, whose coordinate is zc. If z belongs to E,
99 of these a-edges are available. The path y to yu_1 uses the known
a-edge at y and b_1. The path yu_1 a to yw uses b_2, then the known
a-edges at yu_2,...,yu_99 and the remaining b-edges. The w-edge connects
y to yw. Thus the one missing interior a-edge at yu_1 is recovered.

It matters that availability over E quantifies over every first coordinate.
For a prescribed point (x,zc), its predecessor under u_1 has quotient
coordinate z and an unrestricted first coordinate. Therefore the previous
paragraph establishes availability over Ec, not merely at some points in
each fiber. Iteration yields availability over the union of Ec^n, n>=0.
A complete cost-one argument still has to supply the small B-marker,
the one-sided c-marker, conull invariant restrictions and the cost lower
bound; those belong to the full author proof, not this interface note.

## A direct proof of the stated spectral bound

The source makes b_1,...,b_99,w a free basis of J. Consequently
H=<w,b_1> is free of rank two. Its images d,d^(-1)c are a free basis of
F(c,d): inversely d is the first basis element and c is their product.
Thus q restricted to H is an isomorphism.

As an H-space, Y is a Bernoulli product indexed by the disjoint union
Gamma disjoint-union F, with H acting freely on each index set by left
multiplication (on F through q). Choose a countable orthonormal basis
of L^2([0,1]) containing the constant one. Finite tensor products of the
nonconstant basis vectors at finitely many indices, together with the
constant vector, form an orthonormal basis of the product L^2 space.

The H-action permutes these tensor labels. Every nonempty finite-support
label has trivial stabilizer. Indeed a stabilizing h permutes its finite
nonempty support, so a positive power h^k fixes an index. The index action
is free, whence h^k=1; torsion-freeness of H implies h=1. Thus the
mean-zero representation is an orthogonal sum of copies of the regular
representation of H. This also applies to X alone, using the index set
Gamma without F. No independent spectral theorem about Bernoulli shifts
is needed for this decomposition.

For completeness let A be the adjacency operator of the Cayley tree of
H with the two generators and their inverses. Root that 4-regular tree at
the identity and orient each edge from parent p to child v. For finitely
supported complex f,

    2 Re(conj(f(p)) f(v))
       <= (1/sqrt(3)) |f(p)|^2 + sqrt(3) |f(v)|^2.

Every nonroot vertex receives coefficient 3/sqrt(3)+sqrt(3)=2sqrt(3).
The root receives 4/sqrt(3)<=2sqrt(3). Summing edges gives
<Af,f><=2sqrt(3)||f||^2. By density this holds throughout l^2(H).
The two-generator difference form equals 4||f||^2-<Af,f>, so it is
at least (4-2sqrt(3))||f||^2. Orthogonal sums prove precisely the
spectral inequality in the frozen T259S scope for Y and for X.

This argument supplies the lower bound, without needing a proof that
2sqrt(3) is the exact adjacency norm. It does not establish the cost
claim, a contribution verdict, or any assertion of mixing for Y. In
particular t has infinite order and fixes the Z factor, so a nonconstant
function of Z has constant correlation along t^n; mixing for Gamma
is not a consequence and is not claimed.
