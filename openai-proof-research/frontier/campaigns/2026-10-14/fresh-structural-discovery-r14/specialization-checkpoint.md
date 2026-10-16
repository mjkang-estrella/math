# Checkpoint 1: three attempted replacements for infinite-order separation

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

All assertions about altered data below are deductions, not additional
stipulated upstream theorems. The upstream construction itself is accepted.
None of the following proves or refutes frozen FT2.

## 1. The starting complex already detects every nonzero finite specialization

Use the ten-dimensional table in `algebra.tex`, (a:multiplication), over a
field k of characteristic two, replacing q by any nonzero scalar. Its
associativity verification is a polynomial identity, so the same table
remains associative. Its radical is the eight-dimensional positive-degree
span, with quotient k^2, for every such q. Let s be the f-simple.

Keep the DISPLAYED complex, not a newly computed minimal resolution:
R_0=Cf, R_j=Ce (j>=1), d_1=rho_u and d_j=rho_{ell_{j-2}} (j>=2),
where ell_i=x+q^i y and rho denotes right multiplication. The identities
ell_0 u=(x+y)u=0 and ell_i ell_{i-1}=0 imply that this is an augmented
complex. These products are in the order imposed by composition of
right-multiplication maps.

In the basis (e,x,y,z,t,j) of Ce the two relevant images are

 rho_u: (u,v,v,0,(1+q)n,0),
 rho_{ell_i}: (ell_i,q^{i+1}z,z,0,(1+q^{i+2})j,0).

Thus rank d_1=3 if q!=1, and rank d_j=3-1_{q^j=1} for j>=2.
These formulas follow because ell_i,z,j are independent and the only
possible disappearing direction is j. They use no finite search.

Suppose q has order L>1. In characteristic two L is odd, hence L>=3.
The augmentation is exact in degree zero. In every degree j>=1 the
homology dimension is

       dim H_j(R)=1_{L divides j}+1_{L divides j+1}.

For j=1 this follows directly from rank d_1=3 and rank d_2=3;
for j>=2 it is dim Ce-rank d_j-rank d_{j+1}, since the images are
contained in the kernels. In particular the FIRST nonzero homology is
in degree L-1, represented by the basis vector j; degree L has the
class of the basis vector t. At L-1 the incoming image has lost its j
direction, while the outgoing kernel retains it. At L the outgoing
kernel gains t, while the incoming image is spanned by ell_{L-1},z,j.
Each homology line is the f-simple: for [j], u j=z is a boundary; for
[t], u t=y+qx=q ell_{L-1} is a boundary, as is n t=qj.

If q=1, rank d_1=2 and every later differential has rank two.
The augmented homology in degree zero has dimension one (the class of
n in rad Cf), and every H_j, j>=1, has dimension two. The original
augmentation Cf->s is still surjective.

Every nonzero element of a finite field has finite order. Consequently
NO nonzero finite-field specialization retains the displayed infinite
resolution. Repairing it requires new projective terms at these defects;
one cannot retain the asserted polynomial stable-Hom profile merely by
specializing its generic formula. This is a failure of this construction,
not a proof that the repaired algebra cannot have some different witness.

## 2. Scalar comparison fails independently, even if the profile is granted

The pinned `stable.tex` (e:all-degrees), (e:twists), and `triangular.tex`
(t:projected-delta), (t:end-cohomology), supply these exact interfaces:

 H^{3m}=k[tau_1,tau_2]_m, dim H^{3m}=m+1,
 p^a Delta^a(g,h)=(U_1(g)+h,U_2(g)+h),
 0 -> coker Delta^{a-1} -> H^a End(P_Z) -> ker Delta^a -> 0.

For positive a, p^a is an isomorphism under the fiber-profile
hypotheses. If H_1,H_2 in k^* and r=H_1/H_2 has finite order L, then
at m=L the two rows (H_1^{-m},1),(H_2^{-m},1) coincide. On the
(m+1)-dimensional polynomial component, the kernel and cokernel of
Delta^{3L} both have dimension L+1. The exact sequence therefore forces
H^{3L} End(P_Z)!=0 and H^{3L+1} End(P_Z)!=0. Complete-resolution
comparison turns the positive-degree groups into self-Ext of Z.
This conclusion is CONDITIONAL on retaining the displayed profile and
cone construction. Section 1 shows why one cannot assert those hypotheses
for an actual naive specialization. The two separate failures must not be
combined into an unjustified calculation of the specialized module's Ext.

Larger scalar blocks do not fix the same comparison: for S,T in GL_b(k)
over finite k, there is an L>0 with S^L=T^L=I. The block map
(g,h)->(S^m g+h,T^m g+h) is then singular at m=L on every nonzero block.
This assertion concerns that power-action template, not every possible
matrix-valued homological construction.

## 3. Graded automorphisms of the same polynomial algebra cannot separate forever

Let k be finite of characteristic two and R=k[x,y], with both generators
in the same positive degree d. Let phi_1,...,phi_s be finitely many
graded k-algebra automorphisms. Each is determined by its invertible
linear action on R_d, so the group Gamma they generate is finite.
For x!=0 put

                      u=product_{gamma in Gamma} gamma(x).

R is a commutative domain, so u is nonzero and homogeneous of positive
degree d|Gamma|. Every phi permutes its factors. Thus u, and every
positive power of u, is fixed by every phi_i. This is the classical
orbit-product invariant operation, not a novel invariant-theory result.

Apply this to the source's polynomial positive stable self-Hom algebra,
IF a proposed finite-field replacement retains it. Suppose the two branch
functors act by phi_1,phi_2, their projections are injective in all
sufficiently large positive degrees as in the sparse fiber profile, and
the same cone comparison exact sequence holds. Choose a sufficiently
large power w of u. Naturality gives

            p Delta^{|w|}(w,w)=(phi_1(w)+w,phi_2(w)+w)=(0,0).

Injectivity of p implies Delta(w,w)=0. This is a nonzero kernel vector,
so the cone has a positive self-extension. Finite additional twists have
the same common invariant. This blocks replacing scalars by arbitrary
graded automorphisms while retaining this polynomial-profile, sparse-fiber
mechanism. It does not cover noninvertible actions, noncommutative or
nilpotent Ext algebras, fibers without the stated projection, or unrelated
constructions of FT2.

## 4. The apparent H=0 repair loses the required tensor exactness

The formal scalar rows (0,1) and (1,1) are independent over F_2. An
attempt to realize them takes h_0:T=C lt DC -> T, (a,phi)->(a,0).
This is a unital algebra endomorphism, and sigma_0=h_0 tensor h_0 is
an endomorphism of E=T tensor T. The regular left module with right
action twisted by sigma_0 is U_0. It is NOT projective on the right.

Here is a direct proof valid for any of the displayed nonzero q tables.
Let K=DC tensor DC inside E. It is annihilated by sigma_0, hence U_0 K=0.
For each of the four primitive vertex idempotents p=p_1 tensor p_2,

                 pK=(p_1 DC) tensor (p_2 DC)!=0.

For any nonzero idempotent c of C, c DC!=0: with the dual action
(c phi)(b)=phi(bc), choose phi with phi(c)!=0 and evaluate at b=1.
The vertex idempotents of E are primitive because E/rad E=k^4.
Every nonzero finite projective right E-module is a sum of the modules
pE, and (pE)K=pK!=0. No such projective is annihilated by K. This proves
the claim about U_0.

Since E is symmetric, it is self-injective. A finite projective
resolution of U_0 on the right would split backwards from its last
projective syzygy (projectives are injective), making U_0 projective.
Thus no finite such resolution exists. The ordinary U_0 tensor functor
cannot be used as the exact, projective-preserving functor in the pinned
conversion. A bounded projective replacement quasi-isomorphic to U_0
cannot repair the missing right projectivity. A different side-projective
functor with a noninvertible cohomology action has not been excluded or
constructed. Its existence with all needed profiles would be a genuine
additional operation, still unpaid here.
