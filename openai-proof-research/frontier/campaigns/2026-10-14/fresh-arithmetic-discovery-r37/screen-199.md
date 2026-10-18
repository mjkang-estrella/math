# Family 199: the direct stable-spherical configuration route closes

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. 2026-10-18.
Status: NO NOMINEE. No new full target was frozen. Count remains 13/20.

The provisional operation was to extract several interacting negative-spherical
objects from the stipulated symmetric self-orthogonal module, then construct
categorical twist dynamics. It was not a continuation or weakening of the
unresolved FT2 finite-field target. The actual source calculations and primary
hypotheses below close the direct version of this operation before any theorem
nomination. They do not rule out other categorical constructions.

## 1. Exact stipulated source interface

Write k=F_2(q,H_1,H_2). In the Tachikawa paper, use the actual objects E,X,F,
Lambda and Z of `triangular.tex`. Let P be the complete Lambda-resolution P_Z,
and put C^a=Hom_Lambda(P_a,Z). The source's `t:neighboring-degrees` proves

    H^a(C)=k if a=-1 or a=0, and 0 otherwise.                 (1)

This is more information than positive self-orthogonality. Its degree -1 is
nonzero, not an endpoint that may be discarded. The symmetric transfer is

    A=Lambda lt D Lambda,  M=A tensor_Lambda Z.

It supplies a complete A-resolution A tensor P, not a general flatness assertion
about A over Lambda. The source `t:fiber-hom` gives V^0=stable Hom_E(X,FX)=k v_0.
The two column objects U=D_0(X), V=D_1(X) have graded diagonal Hom equal to the
source H^*(X,X), with degree-three dimension two, and degree-zero cross Hom
Hom(V,U)=k v_0. All these are stipulated source contracts.

## 2. The transferred module is not a stable brick

Here is a finite-term argument for the missing degree-zero transfer calculation.
It avoids dualizing any infinite product of Hom spaces. The argument applies to
any totally acyclic finite-projective P over a finite algebra R. Put Z=c_0 P,
I=DR tensor_R P, N=c_0 I. Total acyclicity makes I exact, and every I_j is
injective. Hence N embeds into I_{-1}, with image ker(I_{-1}->I_{-2}).
Finite-projective duality gives Hom_R(Z,I_j)=D Hom_R(P_j,Z)=D C^j.
Consequently

    Hom_R(Z,N) = ker(D C^{-1} -> D C^{-2}).

Inside this kernel, maps Z->N that factor through projectives are exactly the
image of Hom_R(Z,I_0). To prove both inclusions, identify Z with its embedded
copy in P_{-1}. Every map Z->Q to a finite projective extends to P_{-1}, by total
acyclicity. Thus a projective factorization can be written through P_{-1}.
Every map P_{-1}->N lifts along I_0->>N because P_{-1} is projective. Conversely,
every map Z->I_0 extends across Z->P_{-1} because I_0 is injective. Composing
with I_0->>N proves the claimed equality of images. Under finite duality this
image is im(D C^0 -> D C^{-1}). Therefore

    H^0 Hom_R(P,N) = D H^{-1} Hom_R(P,Z).                   (2)

Induction-restriction on the COMPLETE induced resolution gives a direct sum of
cochain complexes

    Hom_A(A tensor P,M) = Hom_R(P,Z) direct-sum Hom_R(P,N).

For the source (1), equations (1)-(2) imply dim_k stable End_A(M)=2. More
precisely its ring is k[epsilon]/(epsilon^2). Indeed the adjunction description
of an A-endomorphism is an R-map Z->Z direct-sum N. The maps into N form a
square-zero ideal: their A-linear extensions have image in (DR)M and kill
(DR)M, because (DR)^2=0. This ideal survives in stable degree zero with dimension
one by (2); the quotient has dimension one by (1). Scalars split the quotient,
so the asserted dual-number ring follows. Projective factorizations respect
this split cochain decomposition; equivalently the first component is induced
by the quotient tensor functor R tensor_A -, which preserves projectives.

In particular M has no nontrivial stable direct-sum decomposition and is not a
stable brick. Symmetric stable duality further gives dimension two in degree
-1, with all other degrees zero. This is not the one-dimensional degree-zero
and degree-minus-one profile required for a (-1)-spherical object. Merely
reading the pre-transfer Z profile as the profile of M would give the wrong
conclusion.

## 3. Rectangular degree-zero cone variations supply no interacting pair

Keep the source algebra Lambda, column objects U,V, and map v_0 fixed. Consider
EVERY morphism V^b -> U^a in the homotopy category of their complete resolutions,
for arbitrary finite a,b>=0. Since Hom(V,U)=k v_0, the morphism is a rectangular
scalar matrix B times v_0. If its rank is r, invertible changes of bases in the
source and target put B into diag(I_r,0). Homotopic chain representatives have
isomorphic cones. It follows that the cone is stably isomorphic to

    Z^r direct-sum U^(a-r) direct-sum V[1]^(b-r).            (3)

This is an exhaustive statement about these degree-zero rectangular maps,
including arbitrary representatives; it is not an assertion about arbitrary
iterated cones, shifted entries, bimodules, or objects of the whole category.

If a-r or b-r is positive, the corresponding diagonal direct summand of the
cone's degree-three self-Hom is H^3(X,X), of dimension two. Thus the cone is not
self-orthogonal. The same conclusion persists after induction to A: for every
Gorenstein-projective cone object W, A tensor its complete resolution is exact
and projective by the source transfer argument, while positive Ext_A(A tensor
W,A tensor W) contains Ext_Lambda(W,W) as a DIRECT summand of the adjunction
complex. No claimed general flatness is used. When a=b=r, (3) is Z^r, and its
induction is M^r, which is self-orthogonal. Hence the only nonzero
self-orthogonal outputs of this entire degree-zero construction are sums of M.
In particular changing a scalar, or replacing it by a rectangular matrix,
does not produce the desired mixed configuration.

## 4. Exact primary obstruction and remaining limits

[Seidel--Thomas, arXiv:math/0001043](https://arxiv.org/abs/math/0001043), Definition
2.14, requires finite TOTAL graded Hom to and from every ambient object and a
specified scalar self-Hom profile. That printed definition is for n>0; it is
not cited as a negative-degree autoequivalence theorem.

[Dugas, arXiv:1404.0060v2](https://arxiv.org/abs/1404.0060), Remark 5.3, already
explains why the total-Hom requirement fails for every nonzero object of a
self-injective stable module category. In a minimal projective resolution of
a nonprojective finite module, every term is nonzero; applying Hom(-,A/rad A)
kills differentials and gives nonzero Ext in every positive degree. Dugas's
Definition 5.1 and Theorem 5.4 use a different relative-induction construction,
with an appropriate truncated-polynomial subalgebra and two-periodic induced
module. A dual-number stable endomorphism ring alone is not that contract.
Our M cannot be periodic: a positive stable period would identify a positive
self-Hom group with its nonzero stable endomorphism ring, contradicting the
stipulated positive vanishing. The obstruction to ordinary twists and the
periodic alternative belong to Dugas; they are not new results here.

Restricting to a smaller thick category may remove the ambient total-Hom
obstruction, but does not change stable End(M). We have not proved that every
object of thick(M) fails to be spherical. Nor have we excluded generalized
spherical functors or new side-projective bimodules. Producing a different
finite-Hom configuration, an appropriate exact adjunction and a nonroutine
autoequivalence mechanism remains unpaid. We have no credible completed
construction of that kind in this screen. Neither (2), (3), a one-object
formal-model observation, nor a restricted categorical statement is nominated
as a substantial campaign result. FT2 remains unchanged and unresolved.
