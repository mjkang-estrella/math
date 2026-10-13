# I316 — independent audit of the entire frozen Q315 proposal

**Frozen-proof verdict: FAIL, for the strict endpoint comparison in section 3, line 96. Q315 itself is independently verified with all stated constants and scope.** The exact input is the complete 124-line `frontier/iterations/i315-quantitative-amplification-gap.md`, SHA256 `53020ac5aa0e859cf48c3746c92adf2ab832f51dc9bdc7ddaf145bc3d400c41d`. Every deduction below is rederived for its new exponents. Completed I312 evidence is context only. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true; no upstream truth audit is attempted. In fact the mathematical proof below does not require a complete Crouzeix theorem or an imported scalar equality classification.

## 1. Exact target and convention

For each integer r>=2, use U_ij=r^(-1/2)exp(2 pi i ij/r), with indices 0,...,r-1, M_i=ri, N_j=j, and

    Phi(z)=z D_M(z) U D_N(z),    Theta(z)=z Phi(z),
    H=H²(C^r) orthogonal-minus Theta H²(C^r),
    C=P_H M_z|H,
    E=C^r (constants),    F=Phi C^r,
    G=H orthogonal-minus (E+F),
    X=2^(-1/2)P_E+2^(1/2)P_F+P_G,
    A_r=X C X^(-1).

The target includes the exact dimension (r³+3r)/2, A_r^(r²+1)=0, numerical radius at most one, unitary irreducibility, C_r(A_r)=2, and C_d(A_r)<=2-(1-d/r)/22 for all integers 1<=d<r. C_d ranges over every disk-bounded matrix polynomial, with no degree bound. For a size-d Schur function Q(z)=sum Q_k z^k, define Q[A]=sum_(k=0)^(L-1) A^k tensor Q_k, where L=r²+1. The base space is the first tensor factor. The same upper bound is proved for every such Q, rather than only for polynomial equality witnesses.

## 2. New exponent arithmetic and T315

On the circle D_M,D_N,U and the scalar z are unitary. Thus Phi and Theta are polynomial inner matrices, and their Hardy multipliers are isometries. Phi(0)=0. Explicitly Phi_ik(z)=U_ik z^(1+ri+k).

For an arbitrary constant B in M_r(C), the (i,j) entry of Phi B Phi* is

    sum_(k,l) U_ik conjugate(U_jl) B_kl z^(r(i-j)+k-l).

If its exponent vanishes, r(i-j)=l-k. Since |l-k|<=r-1, the only possible multiple of r is zero. Therefore i=j and k=l. Conversely these equalities give exponent zero. Normalized circle integration retains only those terms, and |U_ik|²=1/r gives

    integral Phi B Phi* d sigma=(tr B/r)I_r.       (T315)

This works for every complex B, with no positivity or Hermitian assumption. It is not the old Sidon-difference rigidity argument. The scalar leading z cancels pointwise. Applying this identity later to WW* is exact.

## 3. Finite algebraic model, dimension, and nilpotence

The subspace Theta H² is closed and invariant under multiplication by z, so H is invariant under M_z*. Consequently C*=M_z*|H. Invariance of the discarded subspace also proves C^k=P_H M_z^k|H for every k>=0: after each compression the discarded part stays in Theta H² under subsequent multiplication by z.

For z!=0,

    Theta^-1=z^-2 D_N^-1 U* D_M^-1.

With L=2+r(r-1)+(r-1)=r²+1, the (j,i) entry of z^L Theta^-1 is conjugate(U_ij) z^(L-2-j-ri). Every exponent is nonnegative. Thus K=z^L Theta^-1 is a polynomial matrix and Theta K=z^L I. Multiplication by K preserves H², giving z^L H² contained in Theta H². Orthogonality implies H is contained in the vector polynomials of degrees below L. Hence C^L=P_H M_z^L|H=0, and similarity gives A_r^L=0. No exact-minimal-index assertion is necessary.

For inner matrices A,B, write H²=K_A orthogonal-sum A H² and decompose the latter as A K_B orthogonal-sum AB H². This proves K_AB=K_A orthogonal-sum A K_B. Using Theta=z² I D_M U D_N yields

    dim H=2r+sum_i ri+sum_j j
         =2r+(r²(r-1)+r(r-1))/2
         =(r³+3r)/2.

An explicit orthonormal basis, expanding the proposal's finite Gram algorithm, is

    z^a e_i,                       0<=a<2, 0<=i<r;
    z^(2+a) e_i,                   0<=a<ri, 0<=i<r;
    z² D_M(z) U z^b e_j,           0<=b<j, 0<=j<r.

Zero-length index ranges contribute no vectors. The inner decompositions prove orthogonality and completeness, and multiplication by D_M U proves orthonormality of the last family. Every vector has degree below L. Entries of C and the endpoint projections are finite coefficient inner products in algebraic Fourier coefficients. This produces the same explicit matrix as the proposed basis-independent prescription, up to choice of orthonormal coordinates. It introduces no numerical scan or replacement model.

## 4. Both kernels and the partial isometry

Constants belong to H because Theta(0)=0. For a constant a and any g in H²,

    <Phi a,Theta g>=<Phi a,Phi z g>=<a,z g>=0.

Thus F is contained in H; multiplication by Phi is isometric, so dim F=r. Phi(0)=0 gives E perpendicular to F. Since C*=M_z*|H, its kernel is exactly E.

If Cf=0 for f in H, then zf=Theta h for h in H² and f=Phi h. Orthogonality to Theta H² says <h,zg>=0 for every g, so h is constant and f belongs to F. Conversely C Phi a=P_H Theta a=0. Hence ker C=F.

For f in H perpendicular to F, split h=h(0)+z h_1. Then

    <zf,Theta h>=<f,Phi h>
                 =<f,Phi h(0)>+<f,Theta h_1>=0.

Therefore zf belongs to H and Cf=zf, preserving norm. C vanishes on F and is isometric on F-perp, so C*C=I-P_F. Its range is E-perp because ker C*=E and the model is finite-dimensional; as a partial isometry it follows that CC*=I-P_E. Kernel dimensions alone would not prove these identities, but the displayed isometry calculation does.

## 5. Numerical radius and the full disk upper bound

Put B=C X^-1/sqrt(2). As X commutes with the endpoint projections,

    B*B=(1/2)X^-1(I-P_F)X^-1=P_E+(1/2)P_G,
    T=sqrt(I-B*B)=P_F+(1/sqrt(2))P_G.

The range of B lies in E-perp. On this range sqrt(2)T=X, hence

    2TB=X C X^-1=A_r.

For a unit vector a, Cauchy–Schwarz and self-adjointness of T give

    |<A_r a,a>|<=2||Ba|| ||Ta||
                =2s sqrt(1-s²)<=1,    s=||Ba|| in [0,1].

Thus w(A_r)<=1, directly. The weighted scalar compressed-shift model and this type of factorization are credited to Gau–Wu (2009); they are not asserted new. Also ker A_r=XF=F and ker A_r*=X^-1 E=E.

Under the base-first identification of H tensor C^d with r by d matrix-valued polynomials, the coefficient action I tensor Q_k takes a column matrix g to g Q_k^T. Therefore Q[C] is columnwise projection onto H of the multiplier g(z)Q(z)^T. Complex transpose preserves operator norm: Q^T is antiunitarily conjugate to Q*. A disk Schur Q thus gives a contractive Hardy multiplier by radial Parseval, since ||g(rho z)Q(rho z)^T||_HS<=||g(rho z)||_HS on each circle radius rho<1.

For full detail on the compression identity with no boundary hypothesis, set Q_s(z)=Q(sz), 0<s<1. Its Taylor series converges uniformly on the closed disk, so compression is sum C^k tensor s^k Q_k. All terms k>=L vanish. As s increases to one, the finite sum converges to Q[C]. Each entry of Q is in H² and its radial dilates converge in H² by square summability of coefficients. Since every g in H is polynomial, g Q_s^T converges to g Q^T in H². Passing through the bounded orthogonal projection proves the asserted multiplier-compression identity and ||Q[C]||<=1. The same applies to all disk-bounded polynomials regardless of their degrees.

Similarity gives Q[A_r]=(X tensor I_d)Q[C](X^-1 tensor I_d), and ||X||=||X^-1||=sqrt(2). Thus ||Q[A_r]||<=2 at every coefficient size, without an imported complete spectral-set theorem.

## 6. Base-first transpose and the level-r witness

Let P=Phi^T. Circle unitarity and the scalar maximum principle applied to matrix elements imply its disk norm is at most one, and its supremum is one. Under column vectorization,

    x=(1/sqrt(r))sum_j e_j tensor e_j   corresponds to I_r/sqrt(r),
    y=(1/sqrt(r))sum_j Phi e_j tensor e_j corresponds to Phi/sqrt(r).

Both have norm one, and y lies in F tensor C^r. Right multiplication of I_r/sqrt(r) by P^T=Phi gives y before compression, so P[C]x=y. Since X^-1 x=sqrt(2)x and Xy=sqrt(2)y, P[A_r]x=2y. This finite polynomial witness and the upper bound prove C_r(A_r)=2. The transpose is exactly the one required by the base-first convention; no tensor factors are silently reversed.

## 7. Three nonnegative losses and projected-input defect

Fix 1<=d<=r and any size-d open-disk Schur Q. The finite matrix Q[A_r] has a unit top singular input x. Suppress tensor identities and write

    S=Q[C],    gamma=||Q[A_r]||=||X S X^-1 x||,
    epsilon=4-gamma² in [0,4],    u=X^-1 x,    z=Su.

Direct cancellation gives the exact loss decomposition

    epsilon=2(2-||u||²)+2(||u||²-||z||²)
              +<(2I-X²)z,z>.

Indeed the right side is 4-||Xz||². Its first term is nonnegative since ||X^-1||²=2; its second is nonnegative since S is contractive; its third is nonnegative since X²<=2I. More explicitly,

    2I-X^-2=(3/2)P_F+P_G,
    2I-X²=(3/2)P_E+P_G.

The former dominates P_(E-perp), and the latter dominates P_(F-perp). Each nonnegative loss is bounded by the sum epsilon. Consequently

    ||x_(E-perp)||²<=epsilon/2,
    ||z_(F-perp)||²<=epsilon,
    ||u||²-||Su||²<=epsilon/2.

Put v=P_E u. X^-1 has norm at most one on E-perp, so

    ||u-v||²<=epsilon/2,
    ||v||²=2||P_E x||²>=2-epsilon.

The positive operator D=(I-S*S)^(1/2) exists and has norm at most one. Crucially, ||Du||²=||u||²-||Su||²<=epsilon/2. Hence

    ||Dv||<=||Du||+||D(v-u)||
           <=sqrt(epsilon/2)+sqrt(epsilon/2)=sqrt(2epsilon),
    ||v||²-||Sv||²=||Dv||²<=2epsilon.

This is a quadratic defect estimate with the stated constant. It does not infer a squared estimate from a triangle inequality between ||v|| and ||Sv||, which would lose a square root. It also holds for epsilon=0.

## 8. Uncompressed product, Pythagoras, and constants 5 and 6

Represent the constant v by V in M_(r,d), put w=Sv, and project f=P_F w. Since Phi maps constants isometrically onto F, f=Phi W for a unique constant W in M_(r,d). The uncompressed Hardy product is

    h(z)=V Q(z)^T,    P_H h=w.

Its norm is at most ||v|| by multiplier contractivity. Orthogonality of h-w to H gives

    ||h-w||²=||h||²-||w||²
             <=||v||²-||Sv||²<=2epsilon.

Also w-z=S(v-u), so

    ||w_(F-perp)||<=||z_(F-perp)||+||S(v-u)||
                   <=(1+1/sqrt(2))sqrt(epsilon).

Let c=(1+1/sqrt(2))²=3/2+sqrt(2). Since h-w is perpendicular to H and w-f belongs to H, they are orthogonal. Thus

    ||h-f||²=||h-w||²+||w-f||²
             <=(2+c)epsilon=(7/2+sqrt(2))epsilon<=5epsilon.

Separately,

    ||w||²>=||v||²-2epsilon>=2-3epsilon,
    ||W||_HS²=||f||²=||w||²-||w-f||²
                >=2-(3+c)epsilon
                =2-(9/2+sqrt(2))epsilon>=2-6epsilon.

The exact inequalities sqrt(2)<3/2 certify both roundings. These are Hardy/L² Hilbert–Schmidt norms for functions and Hilbert–Schmidt norms for constants. The function h need not be polynomial or boundary continuous. The lower bound on ||W||² is still a valid inequality if its right side is negative; W is never rescaled or assumed nonzero in this estimate. The requested weak <=5epsilon estimate is valid at epsilon=0. However, the frozen parent actually writes the strict final comparison <5epsilon at line 96; that stronger assertion is false at epsilon=0. This is the exact repair discussed in section 11 below, not an unchanged-parent claim.

## 9. Rank loss, sign-safe twirl comparison, and inversion

Let Pi project onto (range V)-perp in C^r. Then q=rank Pi/r>=1-d/r=t>=0, and Pi V=0 gives Pi h(z)=0 at every point of the disk. As left multiplication by Pi is a contraction in Hardy Hilbert–Schmidt norm,

    integral ||Pi Phi W||_HS² d sigma
       =||Pi(f-h)||²<=||f-h||²<=5epsilon.

Only Phi W, a polynomial, is integrated on the circle. There is no assumption on boundary values or continuity of Q. Since Pi is an orthogonal projection, cyclicity of trace and T315 give

    integral ||Pi Phi W||_HS² d sigma
       =tr(Pi integral Phi WW* Phi* d sigma)
       =(rank Pi/r)tr(WW*)=q||W||_HS².

Nonnegativity of ||W||² is used before the lower estimate:

    t(2-6epsilon)<=t||W||²<=q||W||²<=5epsilon.

This order is valid even when 2-6epsilon<0, including rank V<d. It never multiplies a negative lower bound by q>=t in the wrong direction. Rearranging gives

    2t<=(5+6t)epsilon,
    epsilon>=2t/(5+6t)>=2t/11,

because 0<=t<=1 and the denominator is positive. With 0<=gamma<=2,

    2-gamma=(4-gamma²)/(2+gamma)
             =epsilon/(2+gamma)>=epsilon/4>=t/22.

Therefore every size-d Schur evaluation satisfies gamma<=2-(1-d/r)/22 for 1<=d<r. Taking the supremum over all admissible polynomials proves the claimed C_d bound. At d=r this argument gives the upper bound two and the preceding witness attains it. The original theorem makes no smaller-channel gap claim for d>r; the similarity still bounds those levels by two. No compactness or equality-attainment argument is used to obtain the quantitative gap.

## 10. Irreducibility for the new Phi

Let R be an orthogonal projection commuting with A_r and A_r*. It preserves ker A_r=F and ker A_r*=E. Self-adjointness of R makes the orthogonal complements invariant, so R commutes with P_E,P_F,P_G and X. Therefore R commutes with C=X^-1 A_r X and C*. Its restrictions give orthogonal projections V0,W0 on C^r by

    Re=V0 e,    R(Phi a)=Phi W0 a.

For constants e,a and k>=0, commutation and self-adjointness imply

    <C^k V0 e,Phi a>=<C^k e,Phi W0 a>.

Because Phi a belongs to H, projection can be removed from the first argument. Writing Phi=sum_k Phi_k z^k and using the convention conjugate-linear in the first argument gives e* V0 Phi_k a=e* Phi_k W0 a. Thus V0 Phi_k=Phi_k W0 for every k, and

    V0 Phi=Phi W0.

Circle unitarity gives V0=Phi W0 Phi*. Applying the new twirl, rather than old Sidon rigidity, yields V0=(tr W0/r)I. Since V0 is a projection, this scalar is zero or one. From the circle identity W0=Phi* V0 Phi, W0 is the same scalar projection. Finally the vectors C^k e=P_H z^k e span H by polynomial density and finite dimension. Commutation gives R C^k e=C^k V0 e, so R is zero or identity on H. This proves unitary irreducibility with no scalar cyclicity assumption on an individual constant vector.

## 11. Whole-proposal disposition and boundaries

The proposed theorem and all needed weak inequalities are independently verified. All deductions other than the strict endpoint comparison at section 3, line 96, are valid as stated. The final contribution/validation boundary contains no additional mathematical assertion needed for Q315. The scalar Gau–Wu antecedent is correctly credited. Its Theorem 5 construction and proof and Theorem 8 statement were directly inspected, but its necessity theorem is not a premise here. The two pinned Crouzeix companion statements were read as corpus/convention context and are stipulated true, not used to infer this quantitative hierarchy.

The completed I312 report and full analysis match their dispatch hashes. Its original exponents M_i=i,N_j=2^j-1 differ from the present M_i=ri,N_j=j. Its qualitative PASS supplies neither T315, the present polynomial dimension, nor any quantitative constant. The original graded rank-defect warning is also context only: its obstruction to an unrelated block ansatz is not an assumption in this proof. I313 and I314 live bodies were not read.

### Exact failed step and necessary repair

The frozen section 3 fixes d<=r and asserts at line 96

    ||h-f||²<= [2+(1+1/sqrt(2))²]epsilon<5epsilon.

The coefficient 2+(1+1/sqrt(2))² is strictly below five, but multiplying this strict coefficient inequality by epsilon preserves strictness only if epsilon>0. The proof explicitly includes d=r, and the supplied witness gives epsilon=0.

For every integer r>=2, take d=r, Q=P=Phi^T, and x=(1/sqrt(r))sum_j e_j tensor e_j. The already verified witness gives gamma=2 and epsilon=0. In section 3's normalization,

    u=v=sqrt(2)x,    V=sqrt(2/r)I_r,
    h(z)=V Q(z)^T=sqrt(2/r)Phi(z),
    w=Sv=sqrt(2)y,    f=P_F w=w=h,
    W=sqrt(2/r)I_r.

Thus ||h-f||²=0 and the final strict comparison is 0<0. This is an exact counterexample to an intermediate assertion, with no numerical scan. It does not refute Q315 or any needed constant. In particular ||W||²=2 satisfies its lower bound, and t=0 satisfies the final rank inequality.

The necessary manuscript repair is the single comparison change `<5epsilon` to `<=5epsilon`; equivalently the parent could qualify the strict comparison by epsilon>0 and retain the weak bound at zero. This preserves every theorem hypothesis, model condition, exponent, dimension, scope, and constant. It is nevertheless an actual correction to a false frozen assertion, so this review returns FAIL rather than PASS unchanged. The corrected weak bound was derived directly in section 8; the conclusion then follows exactly as in section 9. The parent file remains frozen and unedited.

Explanatory expansions, distinct from that repair: the finite orthonormal basis, compression by radial dilates, explicit spectral loss operators, exact constants before rounding, the sign-safe comparison using nonnegative ||W||², and coefficient orientation in irreducibility. These expand valid operations already justified by the definitions and claims. The explicitly identified comparison repair is separate. No weakened theorem hypothesis, exponent, scope, or constant is substituted; no other missing mathematical operation remains for Q315.

This review issues no contribution or acceptance verdict and changes no count. Only the five assigned outputs are authored. No child agent, numerical scan, git operation, publication, or shared-index mutation was used. Raw identities and read extents are separately authenticated; detached output hashes are computed after finalization.
