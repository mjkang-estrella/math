# Well-conditioned Gram matrices do not guarantee global congruence normalization

Author continuation of the SAME frozen T101G69 target. This is a rigorous obstruction to one proposed reduction, not a counterexample to the target distance estimate. It does not alter any earlier completed note.

For every k>=1 there is a fully symmetric real cubic T on m=6k+1 coordinates such that

  (1−1/(4k+1))I <= B(T)<=I,
  ||B(T)−I||F²=1/(4k+1),

but no invertible real linear change in all three modes makes its Gram matrix a positive scalar multiple of I. In particular the r67 local normalizer cannot be extended globally using small Gram error alone, even when that error tends to zero in unnormalized Frobenius norm and the Gram condition number tends to1. The commutator error in this example is extensive, so the full target can still pay for replacement of the tensor.

## 1. Explicit cubic

Put a=4k+1 and b=2k, and split V=A direct_sum E with dimensions a,b. Index the A basis by j=0,...,a−1. For l=1,...,k define two vectors on A,

  v_(l,c)(j)=sqrt(2/a)cos(2pi l j/a),
  v_(l,s)(j)=sqrt(2/a)sin(2pi l j/a).

The finite geometric-series identity gives an orthonormal family of b vectors. At every j their squared entries sum to b/a. Denote their entries by v_r(j), r=1,...,b, and put v(j)=(v_r(j))_r. Define T by full symmetry from

  T_(A_i,A_j,E_r)=delta_ij v_r(i),

and set all other index types to zero. Thus, up to the conventional factor3, its cubic polynomial is sum_ir v_r(i) x_i² y_r. Let M_r=diag(v_r(i)). The slice matrices, in the A/E block decomposition, are

  X_(E_r)=[[M_r,0],[0,0]],
  X_(A_i)=[[0,e_i v(i)^t],[v(i)e_i^t,0]].

Their squares sum to

  B_A=2 sum_r M_r²=(2b/a)I_A=(1−1/a)I_A,
  B_E=sum_i v(i)v(i)^t=I_E.

Hence the claimed Gram bounds and beta²=a*(1/a)²=1/a follow exactly.

## 2. No exact isotropization anywhere in the congruence orbit

Define P_t=diag(e^(bt)I_A,e^(−at)I_E). It has determinant1. Every nonzero tensor coefficient has two A indices and one E index, so

  T_(P_t)=e^((2b−a)t)T=e^(−t)T ->0.                   (1)

We need no invariant-theory theorem to use this degeneration. The following elementary fact suffices: if a nonzero fully symmetric tensor U has B(U)=cI, c>0, then ||U_G||HS>=||U||HS for every determinant-one G.

First take G=exp H, H symmetric with tr H=0, and diagonalize H orthogonally with eigenvalues h_i. The squared norm along exp(tH) is

  f(t)=sum_ijk U_ijk² exp(2t(h_i+h_j+h_k)).

It is convex and f'(0)=6tr(HB(U))=0, hence f(1)>=f(0). For a general determinant-one G, use its polar decomposition G=Q exp H. The orthogonal change Q preserves the norm and the scalar Gram property, so the preceding argument applies. The same reasoning permits determinant minus1 after an orthogonal factor.

Suppose U=T_G had B(U)=cI for some invertible G. The determinant-one maps H_t=G^(-1)P_t G satisfy

  U_(H_t)=T_(P_t G)=e^(−t)T_G=e^(−t)U,

contradicting the norm-minimizing fact above. Thus no such G exists. This rules out arbitrary invertible congruence, not only diagonal scaling or a specific iterative solver.

## 3. Exact commutator accounting and the limit of the obstruction

Let Gamma_ij=<v(i),v(j)>. Gamma is an orthogonal projection of rank b with constant diagonal b/a. The E slices commute. For i!=j,

  ||[X_(A_i),X_(A_j)]||F²=2 Gamma_ij².

The mixed A/E commutator has squared norm

  ||[X_(A_i),X_(E_r)]||F²=2v_r(i)²||v(i)||².

Summing once over unordered slice pairs gives

  C=(b−b²/a)+2b²/a=b+b²/a.                            (2)

Thus C is a fixed positive fraction of m asymptotically. There is no conflict with the restricted correction or the frozen target: the elementary estimate

  dist(T,O_m)²<=2||T||HS²+2m<=4m

already bounds this family by a constant times C. Here ||T||HS²=tr B=3b and m=3b+1. Consequently these examples do not obstruct a reduction that is allowed to replace/delete O(C) tensor energy or dimensions.

What they do establish is that a trace-paid arbitrary-B reduction must include an actual replacement, deletion, or extension operation. Small beta alone cannot license the existence of an exact Gram normalizer, and uniform conditioning of B does not fix this. The successful local normalizer uses small associator density in an essential way.

## 4. Status of the full target

T101G69 remains unresolved. The exact-B/small-D supporting result remains available, but arbitrary-B preprocessing and arbitrary-D reduction have not been completed. This example is not a narrower substitute theorem or a nomination. Its use is to exclude a false global normalization premise before that premise enters a proof.
