# Density of the explicit extension, larger blocks, and a precise obstruction

Author continuation of the SAME full T101G69 target. No reduction from arbitrary density is claimed. This note examines extensions preserving the old cubic and initially setting all old-old-new coefficients to zero, as the preceding Gram completion does. Allowing those coefficients is a genuinely additional compatibility operation; the obstruction below does not cover it.

## 1. Full density blocks for the two-axis construction

Use the deficit eigenbasis, epsilon_i, l_i=sqrt(epsilon_i/2), c_i=sqrt(1−epsilon_i) from isometric-extension-and-cancellation.md. Let

  D_S,ij=(1/2)sum_r<[S_r,S_i],[S_r,S_j]>,
  (G_F)_ij=sum_k epsilon_k <S_i e_k,S_j e_k>.

Here D_S is the commutator-density matrix of S even though its Gram need not equal I. For the extended exact-isotropic tensor, D=(1/2)sum_r commutator Gram. Its old-old block is exactly

  D_old=D_S+G_F+diag(epsilon_i−epsilon_i²/2).            (1)

Indeed X_i=diag(S_i,L_i), with L_i=l_i times the off-diagonal swap on its pair. Distinct L_i commute. A new slice alpha has block form [[0,R_alpha],[R_alpha*,C_alpha]]. Its commutator with X_i has off-diagonal block S_i R_alpha−R_alpha L_i and new-new block [L_i,C_alpha]. Summing their Gram contributions gives G_F, diag(2l_i^4), and diag(2l_i² c_i²), respectively. The cross terms vanish since the relevant diagonal and off-diagonal positions are orthogonal. This proves(1).

For completeness the other blocks, with a_i=(S_i)_ii, are

  D_(j,u_i)=D_(j,w_i)
       =−c_i l_i² (S_j)_ii−2c_i l_i³ delta_ij;        (2)

  D_(u_i,u_i)=D_(w_i,w_i)=2epsilon_i−(3/2)epsilon_i²,
  D_(u_i,w_i)=−2l_i³ a_i−c_i² l_i².                  (3)

Different new pairs have zero cross entries. One direct verification of(2),(3) uses D_ab=delta_ab−<X_a,K(X_b)> and the triple-trace contraction. The required traces are

  tr(X_(u_i) X_j²) with its old contraction,
  tr(X_(u_i) X_i X_(w_i))=l_i³,
  tr(X_(u_i)^3)=c_i³,
  tr(X_(w_i)^2 X_i)=l_i² a_i,
  tr(X_(w_i) X_(u_i)^2)=c_i l_i².

For (2), contraction with the old slice gives c_i l_i²(S_j)_ii+2c_i l_i³ delta_ij. These formulas include all cross Grams; none is discarded by claiming that the original Gram is diagonal.

In particular (1) implies D_old>=F/2. The current completion concentrates an operator-sized density on any old direction with an operator-sized Gram deficit. Orthogonal rotation of the new coordinates does not change this old principal block.

## 2. Larger trace-free blocks remove one concentration term

There is a concrete improvement, but not a full repair. For each deficit epsilon_i choose d>=2 and add two d-dimensional spaces W_i^+,W_i^−. Set

  L_i=sqrt(epsilon_i/(2d)) diag(I_d,−I_d)

on this pair of spaces. Let H_d be the exact normalized harmonic-simplex cubic on dimension d from simplex-obstruction.md: B(H_d)=I and every slice has trace zero. Define the cubic on the two new blocks to be

  C_i=sqrt(1−epsilon_i/d)(H_d direct_sum H_d).

Use L_i for the old-new-new coefficients, keep old-old-new zero, and retain S on the old space. Then the old Gram gains ||L_i||F²=epsilon_i, while the new Gram is

  2L_i²+B(C_i)=(epsilon_i/d)I+(1−epsilon_i/d)I=I.

Cross old-new Grams vanish because the slices of H_d have trace zero. Different blocks have disjoint supports. Thus this is another exact symmetric B=I completion.

Now [L_i,C_alpha]=0 and tr L_i³=0. The same calculation as in section1 gives

  D_old=D_S+G_F+diag(epsilon_i²/(2d)).                 (4)

Thus the intrinsic diagonal term can be made small by increasing d. For S=0 and a single deficit1, this recovers the balanced harmonic-simplex mechanism with small density. The improvement is real; dimension alone does not force the old density to remain large.

However the construction still retains G_F, as well as D_S. Its new blocks are close to unit orthodeco at a bounded cost per deficit block, not automatically at cost proportional to a very small epsilon_i. Consequently it cannot be applied indiscriminately to a high-rank small trace deficit. This cost and the surviving G_F both require additional work.

## 3. No-old-old-new obstruction, independent of added dimension

Consider just one old dimension with S=t e^tensor3, 1/2<t²<1. Let ANY fully symmetric extension have B=I, preserve this old cubic, and have T(e,e,w)=0 for every new vector w. There is no restriction on the dimension or the cubic C on the new space. Its slices have the form

  X_e=diag(t,L),
  X_alpha=[[0,row_alpha(L)],[column_alpha(L),C_alpha]],

where L is a real symmetric matrix on the new space. Exact old Gram forces

  ||L||F²=epsilon=1−t².

The exact old density is

  D_ee=tr[L²(tI−L)²]
          +(1/2)sum_alpha||[L,C_alpha]||F².            (5)

This follows directly from the off-diagonal and new-new blocks of [X_e,X_alpha]. Since ||L||op<=sqrt(epsilon), equation(5) gives

  D_ee >=epsilon (|t|−sqrt(epsilon))²>0.              (6)

For t²=3/4 the lower bound is (2−sqrt(3))/8, approximately0.03349, regardless of the number of new axes, their rotation, the choice of C, or closeness to an added orthodeco block. Thus no construction in this entire no-old-old-new class can uniformly force arbitrarily small density for all Gram deficits.

This is NOT an obstruction to arbitrary symmetric extensions preserving only the old cubic. Once old-old-new coefficients are allowed, even the scalar example admits an exact orthodeco extension: on a two-dimensional space choose an orthonormal basis whose old-coordinate cubic sum is cos³(theta)−sin³(theta)=t, possible for every t in [−1,1]. Such an extension generally has a nonzero old-old-new coefficient. That additional coefficient is exactly what the restricted construction disallowed.

## 4. Remaining compatibility and status

A successful larger-block replacement must therefore solve for old-old-new coefficients as well as old-new-new and new-new-new coefficients. Those first coefficients also modify the old Gram and the old restricted associator, so they cannot be inserted without satisfying their joint Gram and cross-Gram equations. The original-density deletion problem is not resolved by rotating or enlarging the existing two-axis construction.

This is a precise method obstruction and a partial larger-block improvement. It does not refute or weaken the full frozen theorem. The all-error exact-isotropy problem, arbitrary-B preprocessing at the strong residual cost, and a noncascading replacement remain unresolved.
