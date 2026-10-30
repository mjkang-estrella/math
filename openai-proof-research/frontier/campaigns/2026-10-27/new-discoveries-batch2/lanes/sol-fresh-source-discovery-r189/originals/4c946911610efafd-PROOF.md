# Negative H-eigenvalue for the literal reflected Steiner tensor

Complete ordinary-mathematics refutation of the unnumbered question in Cooper–Du,
arXiv:2505.10501v1, final paragraph p10. No formal certificate or discovery credit.
This does not refute their separate hyperdeterminant sign conjecture.

## Exact objects

Let T be the star K_{1,29}, with vertices 0,...,29 and centre 0. This is a
connected, simple, finite tree: its 29 edges are {0,j}, 1<=j<=29, and every
noncentral vertex has degree one, so no cycle is possible. For ordered quadruples
of vertices define M_{ijkl} to be the number of edges in the smallest connected
subgraph containing {i,j,k,l}, allowing repeated indices exactly as in the source.
Let J be the 30 by 30 all-ones matrix, A=J/15-I, and define the literal tensor
C(u,v,w,z)=M(u,v,w,Az). Thus
C_{ijkl}=sum_h M_{ijkh} A_{hl}; this is source C1, p9, with k=4.
For a real vector x put g_i(x)=C(e_i,x,x,x)=M(e_i,x,x,Ax).
An H-eigenpair means x!=0 real and lambda real with
                 g_i(x)=lambda*x_i^3 for all i.
We exhibit lambda<0. No symmetry-to-positivity equivalence is used.

## A cut identity derived from the definition

For each leaf j, deletion of {0,j} gives parts {j} and its complement.
An edge belongs to the smallest connecting subtree of a tuple precisely when
that tuple meets both parts. Consequently, for ANY four real vectors u,v,w,z,
M(u,v,w,z) is the sum over leaves j of
 (sum u)(sum v)(sum w)(sum z)
 -u_j v_j w_j z_j
 -(sum u-u_j)(sum v-v_j)(sum w-w_j)(sum z-z_j).
This follows by distributing the four finite sums: the last two terms remove
exactly the tuples entirely on one side. It is also the polarized content of
source Theorem2.1, but the argument here supplies the full mixed identity.

Let s be real and x=(s+29,-1,...,-1), so sum x=s. Since A=J/15-I,
(Ax)_j=s/15-x_j, sum(Ax)=s. In particular, at a leaf
(Ax)_j=s/15+1, and the complement sums of x and Ax are s+1 and 14s/15-1.
Define
 D(s)=s^3-(s+1)^2*(14s/15-1),
 E(s)=s^3-s/15-1.
For i=0 every cut has i on the complement side, giving g_0=29D.
For a fixed leaf i, 28 cuts have i on the complement side, contributing D each;
the remaining cut contributes E. Thus g_i=28D+E for all leaves i.
Expanding, set
 d(s)=2s^3-26s^2+32s+30,
 L(s)=86s^3-728s^2+894s+810.
Then D=d/30, E=(30s^3-2s-30)/30, and
             g_0=29d/30,      g_i=L/30 (i>0).

## Exact algebraic witness and existence

Set P(s)=29d(s)+(s+29)^3 L(s). Its endpoint values are
 P(5)=-85,295,770<0,       P(8)=273,617,240>0.
As a real polynomial it is continuous. The intermediate value theorem supplies
s_* strictly between 5 and 8 with P(s_*)=0. Any such root suffices; uniqueness
and numerical root approximations are unnecessary.

For every 5<=s<=8 the exact factorization
 d(s)=(30-48s)+2s(s-5)(s-8)
shows d(s)<=30-48s<=-210<0. Define
 lambda=29d(s_*)/[30(s_*+29)^3] <0,
 x=(s_*+29,-1,...,-1) !=0.
The centre equation g_0=lambda*x_0^3 follows immediately. The equation P=0 gives
 L(s_*)/30=-29d(s_*)/[30(s_*+29)^3]=-lambda=lambda*(-1)^3,
so every leaf equation also holds. Hence this is a negative H-eigenvalue of the
literal first-free-index C1 tensor, in a genuine finite tree at order4.

This refutes the source universal all-positive-H-eigenvalue question at k=4 and
therefore its proposed extension to every even k. A counterexample at one tree
and order resolves those universal assertions; this is not a positive parameter
case offered as a full proof. No minimal n or classification is claimed.

## Positive definiteness and symmetrization are also addressed

At the rational vector z=(34,-1,...,-1), corresponding to s=5,
 g_0=-203,  g_i=-217/3 (i>0),
 C(z,z,z,z)=34*(-203)+29*(217/3)=-14413/3<0.
Thus positive definiteness fails directly, without invoking an H-eigenvalue
criterion for nonsymmetric tensors. C1 is not generally fully symmetric.
If a reader identifies the tensor with the symmetric tensor of its diagonal
quartic, the same negative quartic refutes that positive-definiteness question.
That symmetric tensor also has a negative H-eigenvalue: minimize its quartic F
on the compact real sphere sum x_i^4=1. The rational negative direction,
rescaled, makes the minimum mu negative. At a minimizer u, the constraint has
nonzero gradient 4(u_i^3), so Lagrange multipliers give
 grad F(u)=4lambda(u_i^3). Euler's homogeneous identity yields lambda=F(u)=mu<0.
Since grad F/4 is the symmetric tensor contraction, this is the H-equation.
The principal result above is stronger than relying on this alternate reading:
it supplies an eigenpair for the literal unsymmetrized source tensor.

## Validation and limits

check.py constructs distances independently as unions of unique graph paths and
contracts the original four-index tensor, without using the cut identity. At
s=0,5,8,9 it verifies ALL 30 contraction components against the two displayed
cubics. Each component is polynomial of degree at most3, so four-point
unisolvence verifies those identities, not just signs at some sampled points.
This covers 3,240,000 small tuple contractions under hard resource caps. Endpoint
and chord-factor arithmetic is exact integer/rational arithmetic. These checks
corroborate the proof; the all-real identity is proved above by finite sums.

The proof does not assume or contradict determinant nonvanishing, determinant
sign, conditional negativity on J-perp, or the positive definiteness of C1+C3.
It settles the explicitly asked C1 question, rather than promoting failure of a
proof strategy to refutation of the sign conjecture. Eligibility, novelty,
source-version completeness and formalization still require root's gates.
