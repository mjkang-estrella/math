# Actual restriction bimodules and their all-degree conversion

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0. Third-party rights retained privately.

This is a complete calculation of a FAILED proposed mechanism for the unchanged
FT2 target. It is neither a witness nor a subclass substituted for that target.
All algebras and tensor products in this checkpoint are over k=F_2.
No computer calculation enters the proof.

## 1. An unbounded-syzygy starting object with no scalar parameter

Put E=k[x,y]/(x^2,y^2), B=k[u]/(u^2), X=E/(x,y), T=B/(u).
Coefficient of xy on E and coefficient of u on B are symmetrizing functionals:
their monomial bases pair with complementary monomials. Hence E and B are
symmetric. Both X and T are nonprojective, since a finite projective module
over either local algebra is free and its dimension is a multiple of 4 or 2.

The nonnegative complex of free k[x]/(x^2)-modules with every differential
multiplication by x resolves k: kernel and image of multiplication by x are
both kx. Tensor this resolution with its y analogue and totalize. In degree
n it has E^{n+1}, with the differential on the summand labelled (r,s), r+s=n,
given by x toward (r-1,s) and y toward (r,s-1), omitting negative indices.
Tensoring exact complexes of vector spaces computes tensor products of their
homologies (split each complex into homology and contractible pairs). Thus
this total complex resolves X. Every entry is in the radical, so it is minimal.
The dimension recursion dim Omega^{n+1}X=4(n+1)-dim Omega^n X, starting at 1,
gives dim Omega^n X=2n+1. This is genuine unbounded growth over F_2.

Applying Hom_E(-,X) makes the differentials zero. The product structure is

    H_E^{>=0}=Ext_E^*(X,X)=k[alpha,beta], |alpha|=|beta|=1.

Indeed, for one variable the identity comparison from a shifted rank-one
resolution to itself shows that all powers of its degree-one class are
nonzero and span. External tensor comparisons commute in characteristic two
and give the independent monomials alpha^r beta^s on the indicated summands.
Likewise Ext_B^*(T,T)=k[t], |t|=1. The B-resolution is one-periodic even
stably: multiplication by u identifies Omega T with T. Consequently its
complete stable algebra is k[t,t^{-1}], in all integer degrees.

Use [1]=Omega^{-1}, and write H_E^a=stable Hom_E(X,X[a]) and H_B^a analogously.
Symmetric duality gives H_E^{-n-1}=D H_E^n. Therefore

    dim H_E^a = a+1 (a>=0), and -a (a<=-1);
    dim H_B^a = 1 for every integer a.

This invocation uses the exact perfect composition pairing in pinned
h:duality (and Linckelmann Section 2), not an assertion that a tensor functor
itself preserves the symmetrizing trace.

## 2. Both-side projectivity and actual cohomology projections

Let j_x,j_y:B->E send u to x,y respectively. Set

    L_x={}_B E_E via j_x, L_y={}_B E_E via j_y, F=L_x direct-sum L_y.

Each L is free of rank one on the RIGHT E-side and rank two on the LEFT
B-side. For L_x a left B-basis is (1,y); for L_y it is (1,x).
The functors L_i tensor_E - are exactly restriction along j_i, through the
balanced map a tensor v -> av. They are exact and preserve projectives.
Moreover L_i X=T as actual modules. No derived replacement is required.

Their induced maps r_x,r_y:H_E^a->H_B^a are ordinary Yoneda restriction in
positive degrees, with

    r_x(alpha)=t, r_x(beta)=0;
    r_y(alpha)=0, r_y(beta)=t.

For example alpha is represented by 0->X->E/(y)->X->0. Its x restriction is
the nonsplit B-extension, while its y restriction is split; beta is the
other extension. Preservation of products proves, for homogeneous p of
positive degree a,

    r_x(p)=p(1,0)t^a, r_y(p)=p(0,1)t^a.

These are noninvertible, genuinely realized cohomology actions, between
DIFFERENT symmetric algebras. They are not endomorphisms of H_E and cannot
be entered as square matrices on H_E. That distinction is the missing
condition in a purely formal zero/identity proposal.

## 3. Negative restriction is zero, proved rather than assumed

The map eta_E:X->Omega X=rad E, 1->xy, spans H_E^{-1}. It is nonzero
stably: a map X->E has image in kxy; a map E->rad E sends 1 into rad E;
the composite is zero since xy rad E=0. The same applies to sums and
summands of E, so eta_E does not factor through a projective. Duality
makes H_E^{-1} one-dimensional.

Restrict along j_x. As a B-module rad E=kx direct-sum B y. The displayed
map factors as T->B, 1->u, followed by B->rad E, 1->y. It therefore becomes
zero stably. Interchanging x and y proves r_y(eta_E)=0 as well.

For z in H_E^{-n-1}, the product alpha^n z lies in H_E^{-1} (with the
appropriate shifted composition). Its x restriction is zero. Multiplicativity
gives t^n r_x(z)=0. Since t is invertible in complete B cohomology,
r_x(z)=0. Use beta^n for r_y. Thus BOTH restrictions are zero in EVERY
negative degree. No transfer theorem from ordinary positive cohomology was
silently applied across the degree-zero seam.

## 4. A finite triangular algebra, map, and complete resolution

Put R=[[E,0],[F,B]], with usual triangular multiplication. It is unital,
associative and has dimension 4+8+2=14. Write its left modules as
(V,W,F tensor_E V->W), and define

    D_0(V)=(V,FV,1), D_1(W)=(0,W,0).

They are exact and preserve projectives by the two projectivities already
proved. Their Hom spaces are

    Hom_R(D_0 V,D_0 V')=Hom_E(V,V'),
    Hom_R(D_1 W,D_1 W')=Hom_B(W,W'),
    Hom_R(D_0 V,D_1 W)=0,
    Hom_R(D_1 W,D_0 V)=Hom_B(W,FV).

Choose complete resolutions P of X over E and Q of T over B. Symmetry
supplies these with finite terms. The complex FP is exact and B-projective.
Take Q_{-1}=B and the embedding T->B, 1->u. The actual map

    v:T->FX=T direct-sum T, 1->(1,1)

lifts to a full chain map Q->FP: lift upward using projectivity and exactness;
extend downward using exactness of Hom_B(Q,J) for projective J. This is
precisely the independently applicable interface h:comparison. It is not
an unevaluated element of a Hom space or a conjectural bimodule lift.
Under the cross Hom identification let V:D_1 Q->D_0 P be this chain map,
and put C=Cone(V), Z=c_0 C.

The column complexes and their cone are totally acyclic. To check the
extra Hom condition, R=D_0(E) direct-sum D_1(B), and the four blocks into
R reduce to Hom_E(P,E), Hom_B(Q,B), Hom_B(Q,F), and zero. The first two
are exact by symmetry; the third is exact since F is left B-projective.
Thus every step needed for complete-resolution comparison is paid.

The module has the explicit description

    Z=(X,N,i),
    N=(k^2 direct-sum B)/k(1,1,u),
    i:k^2=FX -> N, (a,b)->[(a,b,0)].

The one-dimensional relation is a B-submodule, since u kills it. This
formula follows by taking the degree-zero cokernel of the cone: first
quotient the D_0(P) boundaries, then use Q_0->T to impose the graph of
(v,T->B). It makes dim Z=1+(2+2-1)=4. The top-component functor sends
R-projectives to E-projectives; its value on Z is the nonprojective X.
Hence Z is nonprojective.

## 5. The complete comparison in every integer degree

Write K^a=H^a Hom_R(C,Z). The full End complex of C has two diagonal
blocks and one cross block. Projection to the diagonal gives a short
exact sequence of complexes, with cross block
Hom_B^{bullet-1}(Q,FP). Only a finite block decomposition is used; full
Hom continues to mean the product over all resolution indices.
Complete comparison therefore gives the exact sequence

    0 -> coker Delta^{a-1} -> K^a -> ker Delta^a -> 0,
    Delta^a:H_E^a direct-sum H_B^a -> (H_B^a)^2,
    Delta^a(g,h)=(r_x(g)+h,r_y(g)+h).

To verify the connecting map, lift the two diagonal cocycles and take
their cochain differential. Its cross component is F(g)v+v[a]h.
Projection to either restriction summand of F gives the displayed formula.
This proves the mixed-base version of pinned t:end-cohomology; no claim
that its same-base statement applies verbatim is needed.

For a>=1, the source dimension is a+2 and Delta has rank 2: alpha^a and
beta^a give the two coordinate vectors. Thus dim ker Delta^a=a and its
cokernel is zero. In degree zero Delta(c,d)=(c+d,c+d), so kernel and
cokernel are both lines. For a<=-1 both restrictions vanish by Section 3;
Delta(g,h)=(h,h), of rank one, so its kernel has dimension -a and its
cokernel has dimension one. Hence the ACTUAL groups of Z are

    dim K^a = a                  for a>=2;
              2                  for a=1 or a=0;
              1-a                for a<=-1.

In particular Ext_R^a(Z,Z) is nonzero for EVERY a>0. Also K^a is nonzero
for EVERY a<=-2, exactly the negative range needed by the symmetric
transfer. These are proved infinite formulas, not conditional specialized
Ext or finite numerical evidence.

## 6. The symmetric transfer can still be performed, and still fails

For clarity the source transfer argument, without its vanishing conclusion,
gives a useful unconditional identity here. Set A=R lt DR and M=A tensor_R Z.
Then A is symmetric of dimension 28, and M is finite and nonprojective.
For i>0,

    Ext_A^i(M,M) = K^i direct-sum D K^{-i-1}.

Here is why no unproved flatness is involved. Put I=DR tensor_R C.
For each finite projective C_j, its term is D Hom_R(C_j,R), so total
acyclicity makes I exact. The restriction of A tensor_R C is C direct-sum I,
an exact complex of induced A-projectives. Its nonnegative tail resolves M.
Put N'=DR tensor_R Z=c_0 I. The exact tail
0->N'->I_{-1}->I_{-2}->... is injective. Finite projective evaluation
Hom_R(Z,I_j)=D Hom_R(C_j,Z) identifies its degree-i cohomology, i>0,
with D K^{-i-1}. Adjunction on the already proved induced resolution now
splits self-Ext as stated, since Res M=Z direct-sum N'. If M were A-projective,
tensor its splitting with A->R to make Z R-projective, a contradiction.
These are the exactness, duality and nonprojectivity operations in tr:transfer,
spelled out for the modified input.

One may also compute dim M=10 without a program. Finite dual adjunction gives
dim N'=dim Hom_R(Z,R). A map Z->D_0(E) has top component 1->c xy. On the two
k-summands of N its lower component is then forced to (c xy,0) and (0,c xy).
Its value w=(w_x,w_y) on 1 in B must satisfy

    x w_x=c xy, y w_y=c xy.

For each c each equation has a two-dimensional solution space. Thus this
Hom space has dimension 1+2+2=5. Maps Z->D_1(B) factor through N/k^2=T,
so their space has dimension one. Therefore dim N'=6 and dim M=4+6=10.
Finally the exact self-Ext dimensions are

    dim Ext_A^1(M,M)=5;
    dim Ext_A^i(M,M)=2i+2 for EVERY i>=2.

The construction is fully finite-field and fully realized. It fails FT2.
It is a diagnostic on the suggested noninvertible-functor mechanism, not
a new construction of interest nominated for a count.

## 7. Why a sparse fiber cannot repair these very branches

Suppose one inserts an actual short exact sequence of side-projective
B-E-bimodules 0->G->F direct-sum Q'->Y'->0, with Q' projective over
B tensor E^{op}, and assumes stable Hom_B(T,Y'X[a])=0 outside a bounded
range. Evaluation is exact by right projectivity of Y'. The long exact
sequence identifies stable Hom_B(T,GX[a]) with (H_B^a)^2 for all sufficiently
large |a|; Q'X is projective. Any cone still using diagonal objects X,T
therefore has a comparison from a space of dimension a+2 into dimension 2
for large positive a. Its kernel has dimension at least a. Negative
kernels likewise survive for sufficiently negative a. This argument does
not require an unproved evaluated lift; even granting such a lift cannot
remove the dimension mismatch for these branches. It excludes ONLY this
finite collection of rank-one restrictions with bounded-Hom fiber correction.
It does not exclude other side-projective functors, non-sparse fibers,
other diagonal objects or cohomology algebras, nor all FT2 witnesses.
