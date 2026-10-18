# Exact nucleus splitting: a noncascading rank bound

Author supporting structure for the SAME frozen global target. This note uses the actual kernel of the associator density, not a spectral threshold. It supplies no estimate replacing rank by trace. The algebraic operations are classical nucleus/Peirce decomposition and simultaneous diagonalization; this is not an independent novelty claim or a narrower nominee.

Let T be a fully symmetric real cubic on V, with product xy and selfadjoint multiplication operators L_x. Put

  D_xy=(1/2)sum_j<[L_ej,L_x],[L_ej,L_y]>,
  N=ker D, R=N^perp, r=dim R=rank D.

The definition makes sense without B=I. Then T splits orthogonally as a weighted orthodeco tensor on a subspace and a remaining tensor on dimension at most2r. All weights in the first summand are nonnegative after choosing orientations. In particular:

* if B=I, dist(T,O)²<=4r;
* if B<=2I, dist(T,O)²<=||B−I||F²+6r.

These estimates are not the desired trace-C theorem: arbitrarily small positive eigenvalues of D still count toward r.

## 1. The kernel is an associative metric subalgebra

A vector u lies in N exactly when L_u commutes with every L_x. Since the product is commutative, this is equivalent to every associator containing u vanishing. For example

  (ux)y−u(xy)=L_y L_u x−L_u L_y x=0.

The other positions follow by commutativity and reversing the associator. Hence, for u,v in N,

  L_(uv)=L_u L_v.

This product commutes with every L_x, so uv lies in N. Thus N is a commutative associative algebra with the inherited positive definite invariant inner product. Its multiplication operators on N commute and are selfadjoint. Simultaneously diagonalize them. Full cubic symmetry then gives an orthonormal basis e_i of N with

  e_i e_j=0 for i!=j,  e_i²=lambda_i e_i.

Orient each vector so lambda_i>=0. The simultaneous diagonalization includes the zero-product summand; no unit is assumed or introduced.

## 2. Its action on the orthogonal complement

For u in N, L_u preserves N and therefore also R by selfadjointness. Let A_i=L_ei restricted to R. Associativity with a nuclear argument gives

  A_i²=lambda_i A_i,  A_i A_j=0 for i!=j.              (1)

If lambda_i=0, selfadjointness and A_i²=0 imply A_i=0. If lambda_i>0, (1) gives

  A_i=lambda_i P_i,

where P_i is an orthogonal projection on R. Distinct P_i have orthogonal ranges. Consequently

  sum_i rank P_i<=r,

so at most r nuclear basis directions act nontrivially on R.

If P_i=0 (including lambda_i=0), e_i is an isolated cubic factor: its only nonzero coefficient involving e_i is T_iii=lambda_i. Indeed its action on R vanishes, and all products with the other nuclear basis vectors vanish. Remove all these isolated factors at once. The remaining space consists of R together with at most r active nuclear directions, and therefore has dimension at most2r. This is an exact orthogonal splitting, with no repeated projection and no accumulating leakage.

Under B=I there is also the exact relation

  1=||L_ei||F²=lambda_i²(1+rank P_i).                 (2)

In particular zero multipliers cannot occur, and every isolated factor has lambda_i=1. Formula(2) records how an active nuclear factor can be smaller than1 because it acts on a bad module. This compatibility is lost if one simply discards that module and assumes the remaining nuclear coefficients remain normalized.

## 3. Distance accounting

At B=I, let the remaining dimension be s<=2r. Its squared tensor norm is s. Choose any orthonormal basis of that space and orient each vector so its diagonal cubic coefficient is nonnegative. Its inner product with the corresponding unit orthodeco tensor is nonnegative, and hence the squared distance is at most2s<=4r. All removed factors already match exactly.

If B<=2I, the remaining tensor has squared norm at most2s and the same sign choice bounds its squared distance by3s<=6r. Each isolated factor costs (lambda_i−1)², which is at most (lambda_i²−1)² for lambda_i>=0. The isolated factors are orthogonal blocks of B, so their total cost is at most ||B−I||F². This proves the stated general rank bound.

## 4. Exact missing quantitative interface

For P=1_(D<=d0), one has only small associators on P, not zero associators. In particular L_(uv)=L_u L_v is no longer exact, P need not be a subalgebra, and its actions on the complementary space need not be orthogonal projections satisfying (1). The exact argument cannot be applied by replacing the word kernel with low spectrum.

A quantitative version would have to produce approximate nuclear factors and their complementary modules, with a trace-paid repair of the representation relations. The old-old-new blocks are present in this architecture and are not forbidden: they are part of the active modules. Thus this splitting identifies a genuinely broader compatibility structure than the pairwise completion, but it does not yet provide its robust realization.

The frozen all-error trace-residual target remains open. No use of the small-total or exact-B/small-D supporting theorem is made to fill the missing quantitative interface.
