# Ambient low-density products: a coefficient-space estimate

Author continuation of the unchanged full T101G69 target. This estimate avoids aligning actual nuclear factors with the spectral subspace of D. It does not prove global rounding. All arguments below are direct finite-dimensional calculations; no new external theorem is invoked.

Assume B=I. Let P=1_(D<=d), choose an orthonormal basis e_i of PV, and put X_i=L_ei. Thus sum_i X_i^2<=I and

    sum_r ||[X_r,L_v]||F^2=2<v,Dv><=2d||v||^2  (v in PV).

The index r always runs over the ENTIRE original space. Let Z=(z_ij) be any real coefficient matrix on PV, not necessarily symmetric. Regard it as a matrix on V by zero extension. Full cubic symmetry gives

    M(Z):=sum_ij z_ij X_i X_j=K(Z),
    K(Z)_ab=sum_ijc z_ij T_iac T_jcb.

The last equality follows from T_iac=T_cai and T_jcb=T_cbj.

## 1. A dimension-free bound on all coefficient combinations

Set V_j=sum_i z_ij X_i and U_i=sum_j z_ij X_j. Leibniz gives

    [X_r,M(Z)] = sum_j [X_r,V_j]X_j + sum_i X_i[X_r,U_i].

For each r, the first sum is the product of the block row ([X_r,V_j])_j with the block column (X_j)_j. The latter has operator norm at most1 since its squared Gram is sum_j X_j^2<=I. Therefore its squared Frobenius norm is at most sum_j ||[X_r,V_j]||F^2. The second sum is handled by the block row (X_i)_i, whose operator norm is also at most1, and the column ([X_r,U_i])_i. Summing r and using ||a+b||^2<=2||a||^2+2||b||^2 gives

    sum_r ||[X_r,K(Z)]||F^2 <= 8d ||Z||F^2.           (1)

No summation over coefficient basis vectors has been substituted for an operator estimate. Equation(1) holds for every Z with the same constant, and thus controls the entire coefficient map.

For arbitrary real Y, exact B=I gives

    sum_r ||[X_r,Y]||F^2=2<Y,(I-K)Y>F.

The identity follows by expanding both squared terms and using selfadjointness of each X_r; it does not require Y symmetric. K is selfadjoint on matrix Hilbert space and I-K is positive semidefinite.

Let Pi_g=1_[1-g,1](K), with 0<g<1. Spectral calculus and(1) yield

    ||(I-Pi_g)K(Z)||F^2 <= (4d/g)||Z||F^2.           (2)

Thus multiplication of low-density slices lies close to a high-channel ambient space in coefficient-operator norm. Keeping g fixed makes this error small with d; no gap larger than the actual cutoff g has been inserted.

## 2. Exactly what is still missing

The slice corresponding to the actual product vector is

    L_(sum_ij z_ij e_i e_j)=S(Z),  S=JJ*,

where J(v)=L_v. It is NOT K(Z). The difference is the pair-flattened associator, and small D operator norm does not make ||S-K||op small. The simplex family in simplex-obstruction.md has B=I and D_op tending to zero, but K(I)=I and S(I)=0. This is an actual latent matrix mode, not an error in the coefficient estimate.

Consequently(2) supplies an ambient approximate commutative representation, but does not show that the original low-vector subspace is an approximate subalgebra. Replacing K(Z) by S(Z) would reinstate precisely the unpaid pair-flattening step. Nor does(2) imply that the entire high-channel space is closed under matrix multiplication: its elements need not be in the image of these low-input products.

A robust repair could retain the needed ambient matrix modes and then correct their algebra and metric. The existing exact-B/small-D construction accomplishes that when ALL input directions have small density. In the present setting the original bad directions remain, and no trace-paid construction of a complete ambient algebra with small operator associator has been obtained. This note does not apply the restricted result to that unproved object.

The spectral Peirce counterexample shows why a direct gap for K(Q) is unavailable. Equation(2) is compatible with it and does not assert such a gap. The full all-error, all-dimensional target remains open; this is supporting author work only.
