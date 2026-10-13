> Corrected reader version of Q315, 2026-10-13. I316 found that the strict comparison in the original line 96 is false at epsilon=0. This copy changes only that mathematical comparison to a non-strict one; this notice is editorial. The original frozen file is retained unchanged at SHA256 53020ac5aa0e859cf48c3746c92adf2ab832f51dc9bdc7ddaf145bc3d400c41d. I316 independently verifies the weak estimate and the theorem with all constants and hypotheses unchanged. No contribution or acceptance decision follows.

# I315 — explicit uniform gaps below an amplification threshold

2026-10-13. **New parent proof proposal; neither independent gate has run.** Fourteen findings are accepted. This quantitatively strengthens the same hierarchy research direction as I312, and would be counted only once with that direction. Existing reviews of I312 keep their frozen qualitative target.

## Proposed theorem

For every integer r>=2 there is an explicit unitarily irreducible nilpotent complex matrix A_r of dimension

    n_r=(r³+3r)/2,       A_r^(r²+1)=0,       w(A_r)<=1,

such that the supremum C_d(A_r) of ||Q[A_r]|| over all d by d matrix polynomials Q with disk supremum norm at most one satisfies

    C_r(A_r)=2,
    C_d(A_r)<=2-(1-d/r)/22       (1<=d<r).          (Q315)

The same upper bound holds for every open-disk matrix Schur function, without a degree or boundary-continuity assumption. In particular, keeping only any fixed fraction of the r coefficient channels leaves a positive gap from two independent of r. No optimal constant or minimal base dimension is claimed.

## 1. Polynomial unitary averaging

Let U be the r by r unitary Fourier matrix, indexed by i,j=0,...,r-1. Set

    D_M(z)=diag(z^(ri)),      D_N(z)=diag(z^j),
    Phi(z)=z D_M(z) U D_N(z),      Theta(z)=z Phi(z).

Both are polynomial inner matrices. Phi(0)=0. For every r by r matrix B, normalized circle integration gives the exact identity

    integral Phi(z) B Phi(z)* dz = (tr B/r) I.     (T315)

Indeed its ij entry is a sum over k,l with exponent r(i-j)+k-l. Since |k-l|<=r-1, the exponent vanishes only if i=j and k=l. The surviving coefficient is sum_k |U_ik|² B_kk=tr B/r. This is an explicit unitary averaging identity, not an approximate equidistribution statement. Multiplication by the scalar z cancels in the conjugation.

## 2. Finite model and numerical radius

Use the construction of I312, now with this Phi: H=H²(C^r) orthogonal to Theta H²(C^r), C=P_H M_z|H, E=constant vectors, F=Phi C^r, G=(E+F)-perp in H, and

    X=2^(-1/2)P_E+2^(1/2)P_F+P_G,      A=X C X^(-1).

The proof below includes all needed elementary model identities; I312's unfinalized proof review is not a premise. Constants and F lie in H and are orthogonal because Phi(0)=0. We have ker C*=E. Also Cf=0 implies zf=Theta h, so f=Phi h and f perpendicular to Theta H² forces h constant. Thus ker C=F. If f is perpendicular to F in H, testing zf against Theta h and splitting h into its constant and zH² parts shows zf in H. Hence C is isometric on F-perp and

    C*C=I-P_F,       CC*=I-P_E.

Put B=C X^(-1)/sqrt(2). Then B*B equals zero on F, one on E, and one-half on G. As range C is perpendicular to E, direct multiplication gives A=2 sqrt(I-B*B)B. For every unit v,

    |<Av,v>|<=2||Bv|| sqrt(1-||Bv||²)<=1.

Thus w(A)<=1. Also ||X|| ||X^(-1)||=2. Compression of the contractive multiplier Q on H²(C^r tensor C^d) gives ||Q[C]||<=1, so ||Q[A]||<=2 at every level without needing a new sharp upper-bound theorem.

Here L=2+max M_i+max N_j=r²+1. The entries of z^L Theta(z)^(-1) are polynomials, so z^L H² is contained in Theta H². Thus H consists of vector polynomials of degree below L and C^L=0. Inner factorization and K_AB=K_A orthogonal-sum A K_B yield dim H=2r+sum_i ri+sum_j j=(r³+3r)/2. This also makes the matrix explicit by finite algebraic Gram orthogonalization, as in I312.

The polynomial P=Phi^T is disk bounded by one. With

    x=r^(-1/2)sum_j e_j tensor e_j,
    y=r^(-1/2)sum_j (Phi e_j) tensor e_j,

one has P[C]x=y, X^(-1)x=sqrt(2)x and Xy=sqrt(2)y. Thus P[A]x=2y, proving C_r(A)=2 by a finite polynomial witness. Transposition is necessary for the base-first evaluation convention.

## 3. Quantitative equality losses

Fix d<=r and a matrix Schur function Q of size d. Write S=Q[C], a contraction. Finite nilpotence defines its evaluation from the first L Taylor coefficients; it agrees with the multiplier compression by radial approximation. Let x be a unit top singular input for Q[A], and write

    gamma=||Q[A]||,    epsilon=4-gamma²>=0,
    u=(X^(-1) tensor I_d)x,     z=S u.

Tensor identities on the base factor are suppressed below. The exact loss decomposition is

    epsilon=2(2-||u||²)+2(||u||²-||z||²)
                + <(2I-X²)z,z>.

Every term is nonnegative. On E-perp, 2I-X^(-2)>=I; on F-perp, 2I-X²>=I. Therefore

    ||x_(E-perp)||²<=epsilon/2,
    ||z_(F-perp)||²<=epsilon,
    ||u||²-||Su||²<=epsilon/2.

Set v=P_E u, a constant vector represented by an r by d matrix V. Then

    ||u-v||²<=epsilon/2,       ||v||²>=2-epsilon,

because X^(-1) has norm at most one on E-perp and ||v||²=2||P_E x||². The positive defect operator D=(I-S*S)^(1/2) is a contraction. Hence

    ||Dv||<=||Du||+||u-v||<=sqrt(2 epsilon),
    ||v||²-||Sv||²<=2 epsilon.

This controls a quadratic defect directly; a triangle inequality on norms alone would unnecessarily lose a square root.

Put w=Sv and f=P_F w=Phi W, where W is another constant r by d matrix. Let h(z)=V Q(z)^T be the uncompressed Hardy-space product. Then P_H h=w. The multiplier is contractive, so

    ||h-w||²=||h||²-||w||²<=||v||²-||Sv||²<=2 epsilon.

Also

    ||w_(F-perp)||<=||z_(F-perp)||+||S(v-u)||
                   <=(1+1/sqrt(2))sqrt(epsilon).

As h-w is perpendicular to H and w-f lies in H, Pythagoras gives

    ||h-f||²<= [2+(1+1/sqrt(2))²]epsilon<=5epsilon,
    ||W||_HS²=||f||²>=2-[3+(1+1/sqrt(2))²]epsilon>=2-6epsilon.

These statements remain valid when the last lower bound is negative. All norms of functions here are Hardy/L2 Hilbert–Schmidt norms. Their constants are independent of r and d.

## 4. Rank loss paid by unitary averaging

Let Pi be the orthogonal projection onto the orthogonal complement of range V. Its rank is at least r-d. The uncompressed product h(z)=VQ(z)^T has Pi h(z)=0. Consequently

    integral ||Pi Phi(z)W||_HS² <= ||f-h||² <=5epsilon.

By (T315), the left side is exactly (rank Pi/r)||W||_HS². Put t=1-d/r>=0. Using nonnegativity of ||W||² and the preceding lower bound yields

    t(2-6epsilon)<=5epsilon,
    epsilon>=2t/(5+6t)>=2t/11.

Since 2-gamma=epsilon/(2+gamma)>=epsilon/4, this proves gamma<=2-t/22. Taking the supremum proves (Q315). There is no appeal to compactness for this quantitative gap and no hidden dependence on polynomial degree, matrix dimension or ancillary dimension. For d=r, t=0 and the already given witness attains two.

For open-disk Schur Q the multiplier statements follow from radial Parseval and finite-jet evaluation. The function h is in H² with ||h||<=||V||, and its orthogonal projections are well-defined. The averaging identity is applied only to the polynomial Phi and constant W. No boundary continuity of Q is needed.

## 5. Irreducibility

Let R be an orthogonal projection commuting with A and A*. It preserves F=ker A and E=ker A*, so commutes with X and hence with C,C*. Let V0 and W0 be the induced projections on E and F. Pairing R C^k e=C^k V0 e against Phi a gives the coefficient identities V0 Phi=Phi W0. On the circle V0=Phi W0 Phi*. Averaging with (T315) gives V0=(tr W0/r)I. Because it is a projection, V0 is zero or identity; the same follows for W0. The constants are jointly cyclic for C since C^k e=P_H z^k e and polynomials are dense. Hence R is zero or identity on H.

## Contribution and validation boundary

The weighted compressed-shift construction is credited to the scalar Gau–Wu antecedent and its standard vector-model extension. The one-parameter exact unitary averaging is also a standard type of finite Fourier operation. The proposed increment to assess is their use with the positive similarity-loss decomposition and a rank-deficient input projection to give an explicit uniform channel-fraction gap, with polynomial base dimension. This is stronger than generic irreducibility plus compactness yielding unspecified gaps for each fixed r, but its substantiality is not yet established.

No new independent proof or contribution verdict is claimed. The qualitative I312/I314 reviews retain their original frozen input. Any review of Q315 must be a new delegated round with those finalized objections supplied when available. The whole hierarchy direction is one potential finding; these improvements do not create extra acceptance slots. The current total remains fourteen.
