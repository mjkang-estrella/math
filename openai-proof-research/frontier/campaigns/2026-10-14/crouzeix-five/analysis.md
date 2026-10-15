# Dimension-five scalarization: credited supporting deduction

Status: parent derivation, not independently reviewed and not a new campaign
acceptance. This extends the scope of the existing R016/R019 pair using a
published numerical-range theorem. It is not proposed as one of the ten
substantial new results.

## Exact claim and dependencies

The exact R016 statement holds with `1 <= n <= 5`: for every complex n by n
matrix A and every finite square matrix polynomial P, put
`M = max_{z in W(A)} ||P(z)||`. If M>0 and `||P[A]||=2M`, there are constant
unit coefficient vectors u,v such that `p(z)=v*P(z)u` satisfies
`||p(A)||=2M` and `max_{W(A)}|p|=M`. Moreover W(A) is a nondegenerate disk
`a+rho Dbar`, and `p(a+rho z)=M eta z^k`, with |eta|=1 and
`1<=k<=deg P`. The evaluation is base-first, as in R016.

Dependencies are the full reviewed R016 argument (including its stipulated
pinned OpenAI complete bound and credited scalar rigidity/interpolation
inputs) and the following external theorem:

Timothy Leake, Brian Lins and Ilya M. Spitkovsky, *Pre-images of boundary
points of the numerical range*, Operators and Matrices 8 (2014), 699–724,
Theorem 5.7 (printed p.710): a unitarily irreducible 5 by 5 matrix has at
most two multiply generated round numerical-range boundary points.
[Publisher PDF](https://files.ele-math.com/articles/oam-08-39.pdf).
The definitions on pp.699–700 and supporting-line characterization,
Theorem 2.1 on pp.700–701, are relevant. This published theorem is used as
an input, not claimed as a new result or independently re-proved here.

R016's analytic equality extraction, isotropic-subspace bound and scalar
interpolation steps are independent of the base dimension. Its only use of
`d<=4` is the proof that an irreducible attaining block has a direction with
a simple largest support eigenvalue. The following argument supplies that
step in dimension five.

## The missing simple-support step

Let B be a unitarily irreducible complex 5 by 5 matrix, and K=W(B).
First K has interior. Otherwise, after an affine rotation and translation,
B has Hermitian imaginary part zero and is normal, hence reducible.
K has no corner: if z is a corner, choose two nonparallel supporting
normals and a unit x with x*Bx=z. Positivity of each supporting Hermitian
slack makes x a zero vector of both slacks. Solving the two independent
real linear equations gives Bx=zx and B*x=conj(z)x, a reducing line.

Suppose the largest eigenvalue of `H(theta)=Re(exp(-i theta)B)` were
multiple for every theta. The directions whose support face is a
nontrivial segment are at most countable: their relative interiors are
disjoint nonempty open arcs of the boundary circle, and such arcs can
each be assigned a different rational boundary parameter. In particular,
the other directions form a dense set.

For each of these other directions the support face is a singleton z.
It is not a corner, so it is a round point in the terminology of the
published paper. Every unit vector in the top eigenspace of H(theta)
has numerical value z, since its value lies in that singleton face.
Thus z is multiply generated. By Theorem 5.7 all these z lie in a fixed
set S of at most two points. S is nonempty because there are singleton
directions. For every singleton direction,

    h_K(theta) = max_{z in S} Re(exp(-i theta) z).

Indeed, its supporting point belongs to S, and S is contained in K.
Both sides are continuous, so the identity holds in all directions.
The support function determines a compact convex set, giving K=conv(S),
which has empty interior. This contradicts the first paragraph.

Consequently a simple top eigenvalue exists. Simplicity persists on an
open interval. Analytic Hermitian perturbation theory gives analytic
lambda(theta) and its eigenvector there; the boundary parametrization is
`exp(i theta)(lambda+i lambda')`. Its curvature radius is

    lambda+lambda'' = 2 sum_{j != top}
        |v_j* H'(theta) v|^2 / (lambda-lambda_j) > 0.

All denominators are positive. Equality would make v an eigenvector of
both H and H', hence a common eigenvector of B and B*, contrary to
irreducibility. We therefore obtain an open regular analytic arc with
simple top support eigenvalue, exactly the input needed in R016.

## Applying the existing equality argument

Normalize M=1 and choose an irreducible reducing block B attaining norm
two. Its own polynomial maximum is one by the stipulated complete bound.
If its size is at most four use R016 unchanged. If its size is five,
R016's dimension-independent boundary limit argument yields, for a fixed
unit singular pair with matricizations X,Y,

    X*Y=0,    H_boundary^(1/2) (XX*-YY*) H_boundary^(1/2)=0 a.e.

Writing p=rank X and q=rank Y, the middle matrix has inertia
`(p,q,5-p-q)`. Thus `rank H_boundary <= 5-max(p,q)` almost everywhere.
On the regular arc proved above the original resolvent congruence gives
`rank H_boundary=4`. The arc has a positive-measure circle preimage.
Hence max(p,q)<=1; the unit singular vectors make both ranks equal to one.
This produces unit coefficient vectors u,v with scalar equality on B.

The remaining R016 scalar rigidity and unique Schur interpolation argument
gives its disk and monomial conclusion. The scalar channel is bounded by
one on the full W(A); the monomial forces W(A) to be contained in that
disk, whereas W(B) gives the reverse inclusion. This proves the stated
extension, subject to the explicitly inherited inputs.

Combined with the explicit R019 six-dimensional example, the extension
implies that six is the smallest possible base dimension of an attained
matrix-polynomial equality witness lacking every constant scalar
coefficient channel. This concerns a specified polynomial witness, not
all scalar polynomials, a strict scalar supremum, or nondisk rigidity.

## Validation, limits and contribution disposition

The parent read the full R016 and the R019 statement/construction, and the
publisher text of the definitions, Theorem 2.1, Theorem 5.7 and its final
proof (printed pp.715–716). The two technical lemmas used to prove the
published theorem were not independently audited. No numerical experiment
or formal proof is asserted. This note does not change either accepted
finding's historical scope or their frozen reviews.

The argument above is a short application of a 2014 theorem to the existing
R016 bridge. Minimality of the already accepted R019 construction is useful
supporting information, but a new substantial bridge has not been supplied.
Disposition: retain as a technical deduction; no new-result credit and no
paper or public submission from this note alone.
