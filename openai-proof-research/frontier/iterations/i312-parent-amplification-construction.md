# I312 — proposed strict hierarchy of amplification levels

2026-10-13. **Complete parent proof proposal, not independently accepted.** This replaces the open construction lead in the prepared I312 brief. For every r>=2 it proposes one explicit irreducible nilpotent numerical contraction A_r such that

    C_d(A_r)<2 for every 1<=d<r,       C_r(A_r)=2,

where C_d(A) is the supremum of ||sum A^k tensor P_k|| over all d by d matrix polynomials P bounded by one on the closed unit disk. No degree bound is imposed in this supremum. It is a genuine level hierarchy, not merely a compression obstruction for one P. All r are one potential finding, not separate acceptance slots. Thirteen findings remain accepted.

## 1. Explicit finite construction

Index rows and columns by j=0,...,r-1. Put M_j=j and N_j=2^j-1. Let U be the unitary Fourier matrix, U_jk=r^(-1/2) exp(2 pi i jk/r). Set

    D_M(z)=diag(z^M_j),   D_N(z)=diag(z^N_j),
    Phi(z)=z D_M(z) U D_N(z),    Theta(z)=z Phi(z).

Both are polynomial inner matrices, and Phi(0)=0. In the vector Hardy space H²(C^r), let H=H²(C^r) minus Theta H²(C^r), with orthogonal complement intended. Let C=P_H M_z|H be the compressed shift. Write E for the subspace of constant vectors, and F={Phi(z)v:v in C^r}. These are orthogonal r-dimensional subspaces of H. Put G=H minus (E+F), and

    X=(1/sqrt(2))P_E + sqrt(2)P_F + P_G,
    A_r=X C X^(-1),       P_r(z)=Phi(z)^T.

This specifies a finite matrix in any orthonormal basis of H. For a concrete algebraic basis algorithm, work in the polynomial space of degrees below L=r+2^(r-1), and impose the finitely many orthogonality equations against Theta(z)z^k e_j. All coefficients belong to a cyclotomic number field with sqrt(r), and Gram orthogonalization gives exact algebraic entries. No numerical optimization is part of the definition.

Indeed z^L Theta(z)^(-1) is polynomial: its entries have exponents L-2-N_j-M_i>=0. Therefore z^L H² is contained in Theta H², H consists of polynomials of degree below L, and C^L=0. The identity K_AB=K_A orthogonal-sum A K_B for inner A,B gives

    dim H=2r+sum M_j+sum N_j=r(r+1)/2+2^r-1.

Thus r=3 gives dimension 13 and nilpotence bound seven. The value r=2 has dimension six. No minimal-dimension claim is made.

## 2. Numerical radius and the attained level-r witness

The compressed shift has ker C*=E and ker C=F. To check the latter, Cf=0 means zf=Theta h and f=Phi h; orthogonality to Theta H² forces h to be constant. Moreover for f orthogonal to F, zf is already orthogonal to Theta H²: test Theta h by writing h=h(0)+z h1. Hence C is isometric on F-perp. Thus

    C*C=I-P_F,     CC*=I-P_E.

Put B=C X^(-1)/sqrt(2). Then B*B is zero on F, one on E, and one-half on G. Since range C is orthogonal to E, direct multiplication gives

    A_r=2 sqrt(I-B*B) B.

Consequently for every unit v,

    |<A_r v,v>|<=2||Bv|| sqrt(1-||Bv||²)<=1.

Thus w(A_r)<=1 without importing a new equality theorem. The stipulated complete disk bound yields C_d(A_r)<=2 for every d. Alternatively the displayed similarity to the contraction C gives the same bound from the contractive multiplier compression and ||X|| ||X^(-1)||=2.

Let e_j denote constant coordinate vectors in E and the standard coefficient vectors in C^r, distinguished by tensor position. Define

    x=r^(-1/2) sum_j e_j tensor e_j,
    y=r^(-1/2) sum_j (Phi e_j) tensor e_j.

Both are unit vectors. Polynomial multiplication and compression give P_r[C]x=y: the transpose is required because the jth output component is sum_i Phi_ij(z)e_i. Since X^(-1)x=sqrt(2)x and Xy=sqrt(2)y, P_r[A_r]x=2y. On the circle Phi and Phi^T are unitary, so ||P_r||_disk=1. Therefore C_r(A_r)=2, attained by this explicit finite polynomial.

## 3. Rigidity of constant positive matrices

Suppose B0>=0 and A0 are constant r by r matrices with

    Phi(z) B0 Phi(z)*=A0  for every |z|=1.          (R)

Consider the ith diagonal entry. The factor D_M cancels there and it is

    sum_(k,l) U_ik conjugate(U_il) (B0)_kl z^(N_k-N_l).

All nonzero ordered differences N_k-N_l=2^k-2^l are distinct. For positive differences, their two-adic valuations identify l and then k; negative differences follow by sign. Every U entry is nonzero. Since the diagonal entry is constant, every off-diagonal (B0)_kl vanishes. Write B0=diag(b_j).

Then (R) is D_M U diag(b_j) U* D_M*=A0. The M_j are distinct, so U diag(b_j) U* must be diagonal. For Fourier U its off-diagonal entries are all nonzero discrete Fourier modes of the vector b. Their vanishing forces b to be constant. Thus B0=cI and A0=cI. In particular every nonzero B0 in (R) has rank r.

This rigidity statement is finite Fourier algebra. It concerns conjugation of constant matrices by an entire inner function; it is not an assertion that one fixed unitary has only scalar commutant.

## 4. Excluding every smaller coefficient size

Suppose Q is a d by d polynomial with ||Q||_disk<=1 and ||Q[A_r]||=2. Similarity gives

    Q[A_r]=(X tensor I_d) Q[C] (X^(-1) tensor I_d).

The multiplier-compression representation gives ||Q[C]||<=1. Equality in the two positive X norm bounds forces a unit norming vector x to lie in E tensor C^d, and Q[C]x to be a unit vector in F tensor C^d. Represent these by constant r by d matrices V,W, with Hilbert–Schmidt norms one. Before compression the product is V Q(z)^T; afterwards it is Phi(z)W. Since multiplication by the contractive Q has norm at most one and compression is an orthogonal contraction, norm equality forces the uncompressed product itself to equal the output:

    V Q(z)^T=Phi(z)W.

On the circle Q^T is contractive, so

    Phi W W* Phi*=V Q^T conjugate(Q) V*<=V V*.

The trace of each side is one. The nonnegative difference therefore vanishes pointwise, and (R) holds with B0=WW* and A0=VV*. Section 3 gives WW*=cI with c>0. Hence r=rank W<=d. This contradicts d<r. The argument excludes all smaller-size polynomial equality witnesses, not only compressions of P_r.

To exclude a supremum of two without attainment, allow matrix Schur functions Q on the open disk. For fixed d their Taylor coefficient matrices have norm at most one. Diagonal subsequences converge coefficientwise and locally uniformly to a Schur function. Since A_r^L=0, evaluation uses only the first L coefficients, so the evaluation image is compact. Radial Parseval gives the norm-one Hardy multiplier compression also for these Q. Equality again forces the analytic identity VQ(z)^T=Phi(z)W throughout the disk. For |z|<1 this gives Phi(z)WW*Phi(z)*<=VV*; letting z approach each point of the circle uses only continuity of the polynomial Phi, so no boundary continuity of Q is assumed. The trace argument and (R) then apply. Thus no Schur function of size d<r attains two, and its compact evaluation image has maximum strictly below two. Polynomial and Schur suprema agree by radial dilation and normalized uniform Taylor approximation. Therefore C_d(A_r)<2.

## 5. Unitary irreducibility

Let R be an orthogonal projection commuting with A_r and A_r*. It preserves ker A_r=F and ker A_r*=E. Hence it commutes with X, and therefore with C and C*. Its restrictions to E and F identify orthogonal projections V0,W0 on C^r.

For every k>=0, commutation gives R C^k e=C^k V0 e for constants e. Pairing with Phi v and using R Phi v=Phi W0 v shows coefficientwise

    V0 Phi(z)=Phi(z)W0.

On the circle, V0=Phi W0 Phi*. Section 3 forces W0=cI with c either zero or one, and V0=cI. The constants are jointly cyclic for C: the vectors C^k e=P_H z^k e span H because polynomials are dense in H². Thus R=cI on H. This proves irreducibility.

## 6. Prior operations and independent gates

The scalar construction X S(zf) X^(-1), its numerical-radius factorization, and its equality structure are old: Gau–Wu, *Inner functions of numerical contractions*, LAA 430 (2009), Theorems 5 and 8. The parent read the actual publisher PDF via NYCU, web lines 0–357 including those statements, the scalar construction proof and the beginning of the necessity proof. The remaining necessity proof was not read here. No raw PDF hash or page-image inspection is claimed. The scalar result already implies the qualitative E307 theorem, so that result cannot support novelty for this hierarchy.

The proposed new part is the matrix-valued construction together with constant-positive-matrix rigidity forcing full coefficient rank for every extremizer, then compactness at each smaller level. Whether this is already in the literature or a routine instance of a known matrix model theorem remains a separate contribution question. The parent has not certified it. The exact target and full proof require independent review before any acceptance.

Source: https://ir.lib.nycu.edu.tw/server/api/core/bitstreams/761cc49b-4b82-4fd4-8748-960e6473e874/content . No new full external body is retained.
