# I312 — complete independent mathematical audit

**Proof verdict: PASS unchanged**, for ALL sections of the authenticated parent proposal and its exact assertion C_d(A_r)<2=C_r(A_r) for all integers r>=2 and 1<=d<r. The target input is the 102-line `frontier/iterations/i312-parent-amplification-construction.md`, SHA256 `da83fdf48779e56c2c8c694973282ecf61ea14c1134e86b9f48bfed12cc89070`. This review does not edit that proposal. No necessary fix or extra hypothesis is introduced below. The expansions make its compressed arguments independently checkable.

All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The hierarchy itself admits the direct proof below, including its complete upper bound. It needs no imported scalar equality classification and no assumption that level two determines a completely bounded norm. This is proof review, not acceptance or a completed independent contribution gate.

## 1. Construction, finite space, and nilpotence

Fix r>=2. Let M_j=j, N_j=2^j-1 for j=0,...,r-1; U_ij=r^(-1/2)exp(2 pi i ij/r). Set

    Phi=z D_M U D_N,    Theta=z Phi=z^2 D_M U D_N,
    H=H^2(C^r) orthogonal-minus Theta H^2(C^r),
    C=P_H M_z|H.

Each diagonal delay and U is unitary on the circle. Phi and Theta are therefore polynomial inner functions; multiplication by either is an isometry of vector Hardy space. Phi(0)=0. The closed subspace Theta H^2 is invariant under M_z, so H is invariant under M_z*, and

    C^k=P_H M_z^k|H  (k>=0).

For example, this power identity follows by quotienting by the invariant subspace: the discarded part of M_z h belongs to Theta H^2 and stays there after every subsequent multiplication by z.

Let L=r+2^(r-1). Since

    Theta^-1=z^-2 D_N^-1 U* D_M^-1,

the (j,i) entry of z^L Theta^-1 has exponent L-2-N_j-M_i. Its minimum is zero, achieved at the largest indices. This is a polynomial matrix K with Theta K=z^L I. Hence z^L H^2(C^r) is contained in Theta H^2(C^r), H consists of polynomials of degree below L, and C^L=0. Similarity gives A_r^L=0. No commutation between U and a diagonal delay is used in the inverse calculation.

For inner matrices A,B, decompose H^2=K_A orthogonal-sum A H^2 and then A H^2=A K_B orthogonal-sum AB H^2. Thus K_AB=K_A orthogonal-sum A K_B. Applying this to Theta gives the following optional explicit orthonormal basis (an audit expansion of the supplied basis algorithm):

    z^a e_i,                       0<=a<2, 0<=i<r;
    z^(2+a) e_i,                   0<=a<M_i;
    z^2 D_M(z) U z^b e_j,          0<=b<N_j.

The families are mutually orthogonal by the decomposition, and the last family is orthonormal because multiplication by D_M U is isometric. Their count is

    n_r=2r+sum_j M_j+sum_j N_j
       =r(r+1)/2+2^r-1.

This independently verifies n_2=6, L_2=4 and n_3=13, L_3=7. It is an explicit exact algebraic matrix prescription: compute the finite coefficient inner products of C in this basis and the projections defining X. Gram orthogonalization in the parent prescription also gives algebraic entries; no optimization is hidden in the definition. Neither minimal dimension nor exact nilpotence index L is claimed.

## 2. The two defects and direct numerical-radius factorization

Let E be all constant vectors and F={Phi v:v in C^r}. Constants belong to H because Theta(0)=0. For constant v and h in H^2,

    <Phi v,Theta h>=<Phi v,Phi z h>=<v,z h>=0,

so F is contained in H and has dimension r. E and F are orthogonal since Phi(0)=0. Put G=H orthogonal-minus (E+F).

Because C*=M_z*|H, its kernel is exactly E. If Cf=0, then zf=Theta h for some h in H^2 and f=Phi h. Membership in H says

    0=<Phi h,Phi z g>=<h,z g>  for every g in H^2.

Thus h is constant, so f belongs to F. The reverse inclusion follows from z Phi v=Theta v. Therefore ker C=F.

The stronger partial-isometry assertion also holds. If f in H is orthogonal to F, write h=h(0)+z h_1. Then

    <zf,Theta h>=<f,Phi h>
                  =<f,Phi h(0)>+<f,Theta h_1>=0.

Consequently zf lies in H and Cf=zf, with equal norm. C vanishes on F, so C*C=I-P_F. Its range is E-perp because ker C*=E; hence CC*=I-P_E. This does not infer partial isometry from kernel dimensions alone.

Define X=2^(-1/2)P_E+2^(1/2)P_F+P_G and A=X C X^-1. For B=C X^-1/sqrt(2),

    B*B=P_E+(1/2)P_G,
    sqrt(I-B*B)=P_F+(1/sqrt(2))P_G.

The range of B is in E-perp. On that range, sqrt(2)sqrt(I-B*B) agrees with X. Therefore

    2 sqrt(I-B*B) B=X C X^-1=A.

For a unit v, self-adjointness of the square root and Cauchy–Schwarz give

    |<Av,v>|<=2||Bv|| ||sqrt(I-B*B)v||
              =2 t sqrt(1-t^2)<=1,    t=||Bv||.

This proves w(A)<=1 directly in all r. It agrees with the credited Ando construction, without using that theorem as an unexplained implication. Also ker A=XF=F and ker A*=X^-1 E=E, facts needed later.

## 3. Multiplier calculus, transpose, and the attained level

Identify sum_a h_a tensor f_a in H tensor C^d with an r by d polynomial matrix H_x(z) whose columns are h_a. Its tensor norm equals its Hardy Hilbert–Schmidt norm. A coefficient matrix Q_j acting on the second factor changes H_x to H_x Q_j^T. Therefore the analytic multiplier corresponding to base-first Q[C] is right multiplication by Q(z)^T, followed by projection of each column onto H. This fixes the transpose convention explicitly.

Transpose preserves Euclidean operator norm over complex matrices: Q^T is antiunitarily conjugate to Q*. Thus disk contractivity of Q implies multiplier contractivity. For a general open-disk matrix Schur function, radial Parseval applied to the squared Hilbert–Schmidt norm gives

    ||H_x Q^T||_(H^2(HS))<=||H_x||_(H^2(HS)).

No boundary continuity is needed. The compressed multiplier equals sum_(j=0)^(L-1) C^j tensor Q_j. To justify this for Schur functions, first use Q(tz), whose Taylor series converges uniformly on the closed disk, and then pass to t upward to one. For polynomial H_x the coefficient tails converge in H^2 by square summability of the entries of Q; the compressed Taylor calculus is finite. Equivalently, all terms of degree at least L project to zero. Thus ||Q[C]||<=1 for every such Q.

The similarity gives

    Q[A]=(X tensor I_d)Q[C](X^-1 tensor I_d),
    ||Q[A]||<=||X|| ||X^-1||=2.

This provides the complete disk upper bound without a new use of the pinned complete theorem.

Take d=r, P=Phi^T, and x=r^(-1/2)sum_j e_j tensor e_j. Under the column identification x is the constant matrix I_r/sqrt(r). Right multiplication by P^T=Phi produces Phi/sqrt(r), already in F tensor C^r. Therefore P[C]x=y, with y=r^(-1/2)sum_j Phi e_j tensor e_j. Both are unit vectors. X^-1 x=sqrt(2)x and Xy=sqrt(2)y, so P[A]x=2y. P is unitary on the circle, hence has disk norm one by the matrix-element maximum principle. This proves C_r(A)=2 with a finite polynomial witness.

For the exact requested r=3 instance, with omega=exp(2 pi i/3),

    P_3(z)=(1/sqrt(3)) [ z     z^2           z^3        ]
                       [ z^2   omega z^3     omega^2 z^4 ]
                       [ z^4   omega^2 z^5   omega z^6   ].

Its degree is six and coefficient size is three. A_3 is the 13-dimensional matrix above, with A_3^7=0. This is the parent model specialized exactly, not a substitute construction.

## 4. All-r constant-positive-conjugacy rigidity

Suppose B0>=0 and A0 are constant r by r matrices and Phi(z)B0 Phi(z)*=A0 for every point of the circle. The scalar leading factor z disappears there. In diagonal entry i the D_M factors also disappear, giving

    sum_(k,l) U_ik conjugate(U_il)(B0)_kl z^(N_k-N_l).

For k>l, N_k-N_l=2^l(2^(k-l)-1). Its two-adic valuation is l and its odd part determines k-l. Thus all positive ordered differences are distinct, and all negative ordered differences are distinct by sign. Positive and negative differences cannot coincide. Each U_ik conjugate(U_il) is nonzero. Every nonconstant Laurent coefficient of that diagonal entry therefore isolates one off-diagonal entry of B0 and makes it zero. No cancellation between different ordered pairs is possible. B0 is diagonal, say diag(b_j).

Now put T=U diag(b_j) U*. The (i,h) entry of D_M T D_M* is T_ih z^(i-h). Distinct M_i force T_ih=0 for i!=h. Fourier conjugation gives

    T_ih=(1/r)sum_j b_j exp(2 pi i(i-h)j/r).

Every nonzero residue i-h modulo r occurs among such pairs. All nonzero Fourier modes of b vanish, so b is constant. It follows that B0=A0=cI. Positivity implies c>=0; any nonzero B0 has rank r. The algebra in fact works without positivity, but that strengthening is unnecessary. It is simultaneous conjugacy by the entire function Phi, not the commutant of a single unitary U.

## 5. Every matrix Schur equality witness, not just the displayed P

Fix any d and any d by d Schur function Q. Suppose ||Q[A]||=2. The finite evaluation matrix has a unit norming vector x. Write X_d=X tensor I_d and Z=Q[C]. The exact chain is

    2=||X_d Z X_d^-1 x||
      <=sqrt(2)||Z X_d^-1 x||
      <=sqrt(2)||X_d^-1 x||<=2.

Every inequality is equality. Since the top eigenspace of the positive X^-1 is E, x belongs to E tensor C^d, and X_d^-1 x=sqrt(2)x. The middle equality gives ||Zx||=1. The first equality puts Zx in the top eigenspace F tensor C^d of X. Hence x is represented by a constant V in M_(r,d), and Zx by Phi W for constant W in M_(r,d), with ||V||_HS=||W||_HS=1.

Before compression the product is g(z)=VQ(z)^T. Its norm is at most one, while its orthogonal projection onto H tensor C^d is Phi W of norm one. Pythagoras gives

    ||g-P_H g||^2=||g||^2-||P_H g||^2=0.

Thus g=Phi W in Hardy space. Equality of Taylor coefficients gives the analytic identity

    VQ(z)^T=Phi(z)W  throughout the open disk.

This is a full identity, not just equality of the first L jets or the retained compression. It holds for arbitrary Schur functions and arbitrary norming vectors.

Because Q^T is contractive, for every |z|<1,

    Phi(z) WW* Phi(z)*
       =VQ(z)^T (Q(z)^T)* V*<=VV*.

Let z tend radially to any prescribed circle point. The left side converges by polynomial continuity of Phi. The resulting boundary inequality requires no radial limit of Q. Circle unitarity gives trace(Phi WW* Phi*)=trace(WW*)=1; trace(VV*)=1 as well. The positive semidefinite difference consequently has trace zero and is the zero matrix. Section 4 applies and gives

    WW*=VV*=I_r/r.

In particular rank W=rank V=r, so d>=r. This is the required universal exclusion for all size-two Schur jets when r=3, and for all d<r in general. The argument does not assume uniqueness of any chosen top vector, minimality of the displayed coefficient level, or compressibility to the displayed P. Direct sums and tensor identity repetitions play no role.

## 6. Compactness, strict supremum, and polynomial agreement

For fixed d, every Taylor coefficient of a d by d Schur function has operator norm at most one by Cauchy's integral formula and passage to circle radius one. Given a sequence, successively extract subsequences for coefficient 0,1,... in their finite-dimensional closed unit balls, then take the diagonal subsequence. On every |z|<=R<1, the geometric coefficient tail is bounded uniformly by R^n/(1-R). Thus coefficient convergence gives locally uniform convergence to a Schur function.

Since A^L=0, Q[A] depends continuously on only Q_0,...,Q_(L-1). Every sequence in the evaluation image has a subsequence converging to another point of the image. The image is compact in finite-dimensional matrix space. Its norm maximum is at most two by Section 3, and cannot be two when d<r by Section 5. Therefore this maximum is strictly below two. The gap is for each fixed (r,d); no numerical value or uniform bound over r is claimed.

Every disk-bounded polynomial is Schur. Conversely, for any Schur Q and 0<t<1, the dilated function Q(tz) is analytic past the closed disk and has disk norm at most one. Its Taylor polynomials T_n converge uniformly there. Normalize them by max(1,||T_n||_disk), which tends to one, to obtain admissible matrix polynomials. Their evaluations converge to Q(tA), and the first L coefficients tend to those of Q as t increases to one. Hence polynomial and Schur evaluation suprema agree. This establishes C_d(A)<2 for every d<r despite the unrestricted polynomial degree in the definition.

The old scalar compactness operation is supporting methodology. It is the matrix Schur nonattainment in Section 5 that makes the present strict inequality possible; separate exclusion of polynomial equality alone would be inadequate.

## 7. Irreducibility and the orientation of the recovered relation

Let R be an orthogonal projection commuting with A and A*. Since ker A=F and ker A*=E, R leaves F and E invariant. Self-adjointness makes their orthogonal complements invariant as well, so R commutes with P_E,P_F,P_G and X. Consequently it commutes with C=X^-1 A X and with C*. Its restrictions are constant orthogonal projections V0 on E=C^r and W0 on F=Phi C^r:

    Re=V0 e,     R(Phi v)=Phi W0 v.

Write Phi(z)=sum_k Phi_k z^k. For e,v in C^r and k>=0,

    <C^k e,Phi v>=<z^k e,Phi v>,

because Phi v belongs to H. Using commutation with C and self-adjointness of R gives

    <C^k V0 e,Phi v>=<C^k e,Phi W0 v>.

In coefficient form this says e* V0 Phi_k v=e* Phi_k W0 v (or their conjugates if the opposite inner-product convention is used). Therefore V0 Phi_k=Phi_k W0 for every k, with no transpose reversal. Summing gives the exact proposed relation V0 Phi=Phi W0. On the circle, multiplication on the right by Phi* yields V0=Phi W0 Phi*. Section 4 makes W0=V0=cI. Since these are projections, c is zero or one.

Finally {C^k e:k>=0,e in E} spans H. Indeed C^k e=P_H z^k e and the polynomials are dense in H^2; their projections span finite-dimensional H. Commutation gives R C^k e=c C^k e, so R=cI. There are no nontrivial orthogonal reducing projections. A_r is unitarily irreducible for every r>=2.

## 8. Section 6 of the proposal, repairs, and the remaining gate

The scalar antecedent and the amplification-literature comparisons are credited in the separate [literature record](../../sources/i312_amplification_hierarchy/literature.md), with direct primary-source reading. No mathematical equality assertion above is inferred from a search snippet or from I309/I311. The r=3 conclusion is stronger than R019's obstruction for one specified size-two polynomial and stronger than the scalar/complete separation already covered by I306/I307.

Necessary fixes: **none**. Optional expansions: the orthonormal basis, explicit P_3, the norm chain with its normalization, the radial boundary argument, and the coefficient pairing for reducing projections. Each is already justified by the unchanged parent's definitions and claims. No silent repair was made. No unpaid operation remains for the theorem's stated hypotheses and conclusion.

The independent contribution/priority operation is still outstanding. This review found no inspected same-scope theorem supplying the hierarchy, but has not certified novelty against all matrix-valued model constructions. Its proof verdict must not be represented as SUBSTANTIAL acceptance. All r constitute one potential finding. No acceptance, count change, publication, numerical sweep, optimization, git operation, shared-index edit, or child-agent work is authorized or performed.
