# Conditional recovery after nondegenerate response deletion

Author support, jointly developed with parent. This is a sufficient reduction of the unchanged all-deficit entropy target to the still-unproved global cubic rounding statement. Parent supplied the low/middle N-spectrum deletion and the unweighted covariance recovery observation. It is not an independent proof review.

Use the notation of bounded-response-construction.md: C_r=N X_r+E_r, 0<N<=I, sum C_r²<=I, e=sum||E_r||F²=O(delta), and ||C-sym C||²=O(delta). For a fixed c>0, rank 1_{N<c}=O(delta). The source supplies ||Y||² and Omega(B)=O(delta). All constants below are absolute and may depend on this fixed c.

## 1. Delete only paid coefficient mass

Symmetry of C_r,X_r implies sum||[N,X_r]||F²<=4e. Let P=1_{N>=c}, Q=I-P, Qlo=1_{N<c/2}, Qmid=Q-Qlo. The spectral gap gives

 sum_r||P X_r Qlo||F² <=4c^(-2) sum_r||[N,X_r]||F².

On Qmid the inverse of N is bounded by2/c, so

 sum_r||Qmid X_r||F² <=8c^(-2)(rank Qmid+e).

Indeed Qmid N X_r=Qmid(C_r-E_r) and sum||Qmid C_r||F²<=rank Qmid. Hence a_P=sum_r||P X_r Q||F²=O(delta).

In an N eigenbasis write T_rij=(X_r)_ij. For r in Q and i,j in P,

 n_i T_rij=n_r T_irj+(C_rij-C_irj)-E_rij+E_irj.

The first term on the right belongs to mixed output energy and n_r<=1. Divide by n_i>=c and sum squares. Thus b_P=sum_{r in Q}||P X_r P||F²=O(delta).

The analogous three-index identity on P proves full symmetry there. Namely

 n_j(T_rij-T_irj)=(n_j-n_i)T_rij
                   +(n_iT_rij-n_rT_irj)+(n_r-n_j)T_irj.

The first and last terms are entries of [N,X_r] and [N,X_i]; the middle is the symmetry defect of C minus the corresponding E entries. Since n_j>=c, the fully symmetric projection of P tensor P tensor P applied to T differs from it in squared Frobenius norm O(delta).

For bounded Gram, set Erow=sum E_r E_r*. Congruence of NBN<=2(I+Erow) gives

 PBP<=2c^(-2)I_P+2H,
 H=N_P^(-1)(P Erow P)N_P^(-1), trH<=c^(-2)e.

This is the correct congruence; N_P need not commute with Erow. Delete V=1_{H>1} inside P, and let R=P-V. Then rank V<=trH=O(delta), RBR<=K I_R with K=2c^(-2)+2, and

 sum_r||V X_r||F²=tr(VBV)<=2c^(-2)rank V+2trH=O(delta).

Full near-symmetry on P pays the new input-V coefficients by swapping the input index with an output index. Therefore, with Q'=I-R,

 k=rank Q'=O(delta),
 a=sum_r||R X_r Q'||F²=O(delta),
 b=sum_{r in Q'}||R X_r R||F²=O(delta).              (1)

The restriction T_R=R tensor R tensor R applied to T has full symmetry defect O(delta), since tensor restriction is a contraction. No assumption that R commutes with N or B is used after this construction.

## 2. Strong Gram defect on the retained pencil

Let B0 be B clipped spectrally to[1/2,2]. The explicit source omega gives ||B0-I||F²<=C Omega and rank(B-B0)<=C Omega: these are scalar bounds, including both tails. The compression R(B-B0)R has that rank and operator norm at most K+2, because 0<=RBR<=K and 0<=RB0R<=2. Hence

 ||RBR-I_R||F²<=C Omega.

For the retained slices A_r=R X_r R, r in R, their Gram B_g differs from RBR by a positive matrix D whose trace is exactly a+b. Moreover 0<=D<=RBR<=K I. Thus

 ||B_g-I_R||F²<=C Omega+2K(a+b)=O(delta).             (2)

This argument never bounds the deleted eigenvalues of the original B.

## 3. Recover an actual good-output law

Use Gaussian coordinates x=(v,u) in R plus Q'. Write L_g(v)=sum_{r in R}v_r A_r and bar F(v)=E_u[R F(v,u)], where F is the actual centered source transport. Its derivative is the symmetric positive matrix E_u[R J R]. Thus the averaged map remains a gradient; no assertion that its output law is log-concave is required.

Frobenius contraction for q, followed by block-diagonal comparison, gives

 E||R J R-q(L_g)||F² <=3||Y||²+6a+3b.               (3)

Precisely, compare J=q(A) to q(L), then q(L) to q(RLR) on R by replacing L with its block diagonal part (total squared off-block coefficient norm2a), then remove the bad-input part of RLR (squared norm b). Jensen gives the same bound for D bar F-q(L_g).

Conditional Gaussian Poincare gives

 E|R F-bar F|² <=E||R J Q'||F² <=2||Y||²+4a.         (4)

For the last inequality compare J with q(L) and then q(L) with the block-diagonal comparison, whose R,Q' block is zero. Consequently this operation fixes the correct conditional Gaussian measure and pays the entire lost output fluctuation.

Symmetrize T_R and clip all three mode singular values at sqrt(K)+1, as in response-normalization.md. The resulting fully symmetric cubic S has bounded Gram, |S-T_R|²=O(delta), and ||B_S-I||F²=O(delta). The last assertion follows from the two bounded flattening norms and(2). The new pencil q(L_S) still differs from D bar F in L2 squared by O(delta).

The actual symmetric-curl-test.md argument applies with any fixed Gram bound K': choose R0²>=18K' in its Gaussian Wick estimate and use the positive minimum of q's second divided difference on[-R0,R0]. It therefore gives c(S)=O(delta). This is a constant change in that proved analytic interface, not use of an unproved point-evaluation bound.

## 4. Exact reduction to the frozen B<=2 algebraic target

Read in full: r67/global-preprocessing.md and r69/scope.md. Write beta=||B_S-I||F and a0=sqrt(c(S)). For fully symmetric cubics a0 is exactly the total associator Hilbert-Schmidt norm, not merely a comparable proxy. The r67 preprocessing projects onto the B_S spectrum in[1/2,3/2]. Its retained cubic S1 satisfies B_S1<=1.5I, beta(S1)<=6beta, and sqrt(c(S1))<=a0+6beta. It deletes at most4beta² axes and loses at most18beta² tensor squared norm. The commutator bound follows from the exact two internal-Q corrections: each is a permutation of ZZ*, with Z*Z<=QB_SQ, whose Frobenius norm is at most3beta. Thus there is no beta^4 error. Appending arbitrary unit odeco axes on the deleted space costs at most44beta² in the original tensor distance. These are exactly the inequalities proved in the actual r67 note, applicable without any smallness assumption.

Apply the frozen r69 statement to S1, whose Gram is <=1.5I<=2I; its r<s commutator convention is half c(S1). The resulting O on the entire retained R space would satisfy |S-O|²<=C(beta²+c(S)). If S1 has dimension zero, use the empty tensor and the same44beta² completion bound without invoking r69. No rescaling or extension of the frozen r69 quantifiers is used.

## 5. Conditional completion and the exact remaining theorem

If the exact frozen r69 statement, through Section4, supplies a unit-weight orthogonally decomposable tensor O with |S-O|²<=C(||B_S-I||F²+c(S)), then q's Frobenius Lipschitz bound and Gaussian Poincare imply

 W2²(law(bar F), rotated centered product exponential)<=C delta.

Indeed for O=sum_i u_i tensor u_i tensor u_i, the centered gradient primitive of q(L_O) is sum_i u_i[-log Phi(-<u_i,v>)-1]. Its law is the required product exponential. Means of both maps vanish. Combine this with(4) to obtain the same cost for R F.

Let Cg=Cov(R F)>0. Whitening R F gives an orthogonal projection of the original isotropic target, because Cg^(-1/2)R Cov(F)^(1/2) is a coisometry (with the source's initial orthogonal orientation included). The covariance-normalization coupling lemma converts the preceding product-exponential approximation to cost at most four times that cost after whitening and an orthogonal change of product coordinates. Complete the discarded k-dimensional orthogonal complement with independent centered exponentials, at cost2k. This would prove the full original target.

The global bounded-Gram cubic rounding theorem is NOT proved here and is not imported from the absolute-small-residual theorem. Thus the displayed completion is conditional. These estimates neither change the target nor justify a nomination. They isolate a sufficient remaining algebraic theorem, rather than merely another necessary compatibility estimate.

If R has dimension zero, stop before forming Cg or its inverse. Then m=k<=C delta, and coupling the isotropic X independently to a centered product exponential costs exactly2m<=C delta. Thus every inverse and every positive-dimensional lemma above is used only in its actual domain.

## 6. Smooth applicability and passage to every isotropic log-concave density

The source lemma geo:approximation (approximation.tex, read in full) supplies smooth strongly convex potentials with bounded Hessians, density convergence, entropy convergence, and convergent means and covariance matrices. Its common exponential tail also supplies weighted L1 convergence with weight1+|x|². Center and covariance-normalize these approximants. For a fixed isotropic target the covariance matrices tend to I, so the resulting isotropic laws X_j converge to X in W2 and h(X_j) tends to h(X). Linear changes preserve positive upper and lower Hessian bounds for each j. Thus the smooth source transport hypotheses apply separately to every approximant.

All constants in Sections1–5 depend only on the fixed scalar q-response constants and the hypothetical universal r69 constant, not on the upper/lower Hessian bounds, dimension, or j. Therefore, conditional on r69, their conclusion passes to the target: distance in W2 to any fixed set of measures is1-Lipschitz, so inf_U W2(X_j,U(E-1)) converges to the corresponding infimum for X. Pass to the limit in its squared bound. This also covers bounded supports and nonsmooth potentials. No convergence of the deleted subspaces or normalized source transports is required. The approximation lemma is paid source input, not newly proved upstream truth.
