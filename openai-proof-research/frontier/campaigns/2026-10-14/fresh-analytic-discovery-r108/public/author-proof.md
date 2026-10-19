# T273NC108: author deduction at the frozen scope

Status: full author argument, conditional only on the stipulated source operations identified below. No independent correctness or contribution gate has been run. No acceptance, priority, or publication claim is made. The frozen statement in `frozen-target.md` is unchanged.

Original research prose, CC BY 4.0. Third-party evidence is stored separately under `private/` and is not covered by this notice.

## Statement and notation

There are two input modes and two retained modes. Let (K\) be invertible with \(\|K\|<1\), let \(L=(I-KK^*)^{1/2}\), and let the independent environment be the centered gauge-invariant Gaussian state \(\Gamma_E\), with \(E>0\). The retained annihilation column is \(c=Ka+Lb\). Write \(B=LEL^*>0\) and \(\Phi=\Phi_{K,E}\). The occupation convention is \(R_{ij}=\operatorname{Tr}\rho a_j^*a_i\). Thus \(\Phi(\Gamma_R)=\Gamma_{KRK^*+B}\).

For \(g(t)=(t+1)\log(t+1)-t\log t\), \(g(0)=0\), the claim is, for every finite \(s\ge0\),

\[
\inf_{\rho:\ \operatorname{Tr}\rho N<\infty,\ S(\rho)=s}S(\Phi\rho)
=\min_{R\ge0:\ \operatorname{tr}g(R)=s}\operatorname{tr}g(KRK^*+B). \tag{T}
\]

Here \(N=a_1^*a_1+a_2^*a_2\), and no restriction on correlations, squeezing, or non-Gaussianity is imposed on \(\rho\). There is no energy cap. The claim concerns precisely these strict positive-noise, invertible, strictly contractive two-mode channels. Singular or noiseless boundary channels are not additional claims.

We use capital \(\operatorname{Tr}\) for Fock-space trace and lowercase \(\operatorname{tr}\) for the physical two-dimensional matrix trace. Let \(h(t)=g'(t)=\log(1+1/t)\) for \(t>0\). For a positive reference covariance \(A\), put \(H_A=h(A)\); then
\(-\log\Gamma_A=d\Gamma(H_A)+\operatorname{tr}\log(I+A)\), where \(d\Gamma(H)=a^*Ha\). Physical matrix products act on the annihilation-column index, not on the Fock eigenvector indices.

## 1. Precisely credited source operations

Source273 means the complete manuscript **The entropy photon-number inequality**, at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The private retrieval ledger gives exact raw URLs, Git blobs and SHA256s. Its `thm:epni` and `cor:thermal-attenuator` have a single scalar transmissivity and a common temperature per input port. They do not state (T).

The following are paid operations, not contributions of this argument:

1. `lem:energy-compactness` and `lem:gibbs-variational` in Section 1: energy-bounded trace compactness and entropy continuity on finite-mode Fock space, and the Gibbs variational identity.
2. `thm:interpolation` in Section 2: for arbitrary linear maps between diagonal coordinate Hilbert spaces, four comparisons with weights \(mf(x)e^{\pm x},mf(y)e^{\pm y}\), \(f(x)=x/\sinh x\), imply comparison for \(mf(x)f(y)/f(x+y)\). No intertwining of those maps with the parameter multipliers is assumed. The output test space must be invariant under functions of the parameter tuple and have finite parameter support.
3. `lem:gibbs-regularity` and the proof of `prop:regularized-minimum` in Section 3: the fourth-moment regularization, positive cross-entropy majorant, Gibbs identification, seventh moments, and logarithm bounds. The lemma itself applies to any positive form \(kW^4+W^{1/2}DW^{1/2}\), with \(k>0\), \(D\) bounded positive and \(W=1+N\).
4. The finite-eigenblock Hessian duality proof of `prop:hessian`, its density argument, and identification of the completed map on bounded observables.
5. Section 4's scalar thermal multiplier, weak trace method, and mixture-error interpolation; Section 5's weighted trace justification and scalar entropy-production expansion, followed by number-basis recurrence and compactness. Their scalar algebra will be used component by component, with the different temperatures explicitly retained.

The source's interpolation proof and its Stieltjes/parallel-sum construction are stipulated. We do not re-prove or audit them. The new calculations to be checked here are the matrix normalization, simultaneous four-weight comparisons, matrix defect transport, and matrix cancellation. Calling these new calculations does not assign a significance rating to them.

## 2. An interior Gaussian minimizer and the normalization

Fix \(s>0\). The set \(\{R\ge0:\operatorname{tr}g(R)=s\}\) is nonempty and compact: every eigenvalue lies in \([0,g^{-1}(s)]\). The objective is continuous, so choose a minimizer \(R\) and put \(Q=KRK^*+B\).

In fact \(R>0\). Otherwise, in dimension two its eigenvalues are \((r,0)\), where \(r=g^{-1}(s)>0\). Let \(P\) be the positive-eigenvalue projection and \(P^\perp\) its complement. For sufficiently small \(t>0\), choose \(d(t)>0\) uniquely by
\(g(r-d(t))+g(t)=g(r)\). Then \(d(t)\to0\) and \(d(t)/t\to\infty\), because \(g(t)/t\to\infty\) and \(g'(r)>0\). Along \(R_t=(r-d(t))P+tP^\perp\), differentiability of \(\operatorname{tr}g\) on matrices bounded below by \(B\) gives

\[
\operatorname{tr}g(KR_tK^*+B)-\operatorname{tr}g(Q)
=-d(t)\operatorname{tr}(K^*h(Q)KP)+O(t)+o(d(t))<0.
\]

The coefficient of \(-d(t)\) is strictly positive. This contradicts minimality.

Set \(H_1=h(R)\) and \(H_0=h(Q)\). The Lagrange multiplier rule on the real vector space of Hermitian matrices applies, since the entropy derivative \(H_1\) is nonzero. It gives

\[
K^*H_0K=\lambda H_1,\qquad \lambda>0. \tag{1}
\]

Define

\[
U=\lambda^{-1/2}H_0^{1/2}KH_1^{-1/2}. \tag{2}
\]

Equation (1) gives \(U^*U=I\), hence \(U\) is unitary. We do not diagonalize \(K\) and \(B\) simultaneously. The relevant identities are

\[
\lambda U H_1R U^*=H_0^{1/2}KRK^*H_0^{1/2},\qquad
\lambda U H_1(R+I)U^*=H_0^{1/2}K(R+I)K^*H_0^{1/2}. \tag{3}
\]

The two gaps \(Q-KRK^*=B\) and \(Q+I-K(R+I)K^*=B+I-KK^*\) are positive definite. Consequently one can choose a fixed \(\varepsilon>0\), as small as desired, such that

\[
(1+\varepsilon)\lambda U H_1R U^*\le H_0Q,\qquad
(1+\varepsilon)\lambda U H_1(R+I)U^*\le H_0(Q+I). \tag{4}
\]

For example any positive \(\varepsilon\) below both
\(\lambda_{\min}(B)/\|KRK^*\|\) and
\(\lambda_{\min}(B+I-KK^*)/\|K(R+I)K^*\|\) suffices. These are auxiliary constants for a fixed reference, not extra hypotheses of (T).

## 3. Regularization of a hypothetical violation

Suppose a finite-energy \(\rho^{\rm w}\) with entropy \(s\) has output entropy strictly below \(S(\Gamma_Q)\). The affine expression
\(S(\Phi\rho)-S(\Gamma_Q)-\lambda(S(\rho)-S(\Gamma_R))\)
is negative at this witness. Normalized number cutoffs preserve this strict negativity for some fixed finite-number-supported witness. The cut-off witness need not have exactly entropy \(s\); the reference and the frozen claim have not changed.

Choose \(\varepsilon>0\) satisfying (4) and small enough that adding \(\varepsilon\lambda D(\rho\Vert\Gamma_R)\) preserves negativity at that witness. Next choose \(0<\kappa<1\), write \(\alpha=1-\kappa\), and define
\(\rho_0=\alpha\Phi\rho+\kappa\Gamma_Q\). We will also require (16) below; it only depends on references already fixed. For sufficiently small \(\kappa\), entropy continuity retains negativity. For \(\zeta>0\), minimize

\[
J_\zeta(\rho)=S(\rho_0)-S(\Gamma_Q)
-\alpha\lambda[S(\rho)-S(\Gamma_R)]
+\varepsilon\alpha\lambda D(\rho\Vert\Gamma_R)
+\zeta\operatorname{Tr}\rho W^4. \tag{5}
\]

There are fixed \(c>0,\zeta_0>0\) such that its infimum is at most \(-c\) for \(0<\zeta\le\zeta_0\).

Here are the regularity details needed to use the paid source machinery. Expanding relative entropy rewrites (5), up to a constant, as
\(S(\rho_0)-(1+\varepsilon)\alpha\lambda S(\rho)+\varepsilon\alpha\lambda\operatorname{Tr}\rho d\Gamma(H_1)+\zeta\operatorname{Tr}\rho W^4\).
Since \(H_1\ge h_{\min}I>0\) and \(S(\rho)\le2g(\operatorname{Tr}\rho N/2)\), upper sublevels have bounded energy uniformly in \(\zeta\); for each fixed \(\zeta\) they also have bounded fourth moment. The source energy compactness and entropy continuity, together with lower semicontinuity of the positive penalties, therefore give a minimizer.

Let \(T=\Phi^*\) be the raw unital completely positive observable map. Write \(\mathcal H_s=-\log\rho_s\), where \(\rho_1=\rho\). Replacement implies \(0\le\mathcal H_0\le-\log(\kappa\Gamma_Q)\le CW\). Passive total-number preservation and the environment's finite energy give \(0\le T\mathcal H_0\le C'W\), where the slice of a positive unbounded form is defined by monotone bounded spectral truncations.

Replace output entropy in (5) by its cross entropy against this fixed \(\rho_0\). The resulting majorant agrees at the minimum and is a Gibbs free-energy functional with positive Hamiltonian

\[
\mathcal K=\frac{\alpha T\mathcal H_0+\varepsilon\alpha\lambda d\Gamma(H_1)+\zeta W^4}{(1+\varepsilon)\alpha\lambda}.
\]

Its part other than \(kW^4\) is between zero and \(C''W\), so `lem:gibbs-regularity` applies verbatim. It identifies \(\rho=e^{-\mathcal K}/\operatorname{Tr}e^{-\mathcal K}\), gives faithfulness and finite seventh moment, and yields

\[
(1+\varepsilon)\alpha\lambda\mathcal H_1
=\alpha T\mathcal H_0+\varepsilon\alpha\lambda d\Gamma(H_1)+\zeta W^4+c_\zeta I. \tag{6}
\]

The input logarithm is bounded above by \(C_\zeta W^4\). The environment has all number moments. The passive dilation and replacement imply finite seventh moment of the output as well. Uniformity of these higher-moment and logarithm bounds in \(\zeta\) is not needed.

Subtracting (6) from the objective difference gives, for another input of finite fourth moment,

\[
J_\zeta(\widetilde\rho)-J_\zeta(\rho)
=(1+\varepsilon)\alpha\lambda D(\widetilde\rho\Vert\rho)
-D(\widetilde\rho_0\Vert\rho_0)\ge0. \tag{7}
\]

For a faithful state \(\sigma=\operatorname{diag}(p_l)\), write
\(\|Z\|_{\ell,\sigma}^2=\sum_{l,r}\ell(p_l,p_r)|Z_{lr}|^2\), with \(\ell\) the logarithmic mean. Applying the source's finite-eigenblock perturbation and Gibbs-variational duality proof to (7) gives

\[
\|TZ-\operatorname{Tr}(\rho TZ)I\|_{\ell,\rho}^2
\le\frac{(1+\varepsilon)\lambda}{\alpha}\|Z\|_{\ell,\rho_0}^2 \tag{8}
\]

for centered output tests. In particular the factor is \(\lambda/\alpha\), not its reciprocal. The proof optimizes over trace-zero finite input eigenblocks, which are dense in the trace-zero inverse-logmean norm; (7) supplies the coefficient \((1+\varepsilon)\alpha\lambda\), while the output variation is \(\alpha\Phi(A)\). It extends to complex tests by their Hermitian parts. Bounded spectral compressions and CP Schwarz identify the extension with the actual centered slice on every bounded observable.

## 4. Four comparisons with incompatible physical eigenspaces

Choose a physical mode basis diagonalizing \(R\) on the input, and separately one diagonalizing \(Q\) on the output. Transform \(K,U\) accordingly; (1)–(4) remain valid. These physical bases are unrelated to the Fock eigenbases of \(\rho\) and \(\rho_0\). Let \(r_{1j}\) be the eigenvalues of \(R\), \(r_{0j}\) those of \(Q\), and \(h_{sj}=h(r_{sj})\).

The observable space at side \(s\) consists of two-component columns \(Z=(Z_j)\), each centered in \(\rho_s\), with base norm

\[
\|Z\|_s^2=\sum_{j,l,r}h_{sj}\ell(p_{sl},p_{sr})|(Z_j)_{lr}|^2.
\]

Put \(v_{sjlr}=\log(p_{sl}/p_{sr})/h_{sj}\) and
\[
\mathscr LZ=\sqrt\alpha\,U^*\big(TZ-\operatorname{Tr}(\rho TZ)I\big), \tag{9}
\]
where slicing and centering act componentwise. This map mixes physical coordinates. No commutation with \(H_0,H_1\), or their multipliers, is asserted.

For each coordinate define \(b(v)=\frac v2\coth(hv/2)\) and weights \(b(v)+v/2,b(v)-v/2,r,r+1\). The first two weighted norms are respectively \(\sum_j\operatorname{Tr}\rho_s Z_jZ_j^*\) and \(\sum_j\operatorname{Tr}\rho_s Z_j^*Z_j\). CP Schwarz bounds the input centered slice variances by the raw output variances. Mixture variance bounds \(\alpha\) times either raw variance by the replaced output variance. Unitarity of \(U\) preserves the sum over physical components. This proves both arithmetic-weight comparisons for (9).

For the constant weight \(r\), the input squared norm is the logmean norm with physical matrix \(H_1R\). Applying (8) to the components after multiplying by a square root of \(UH_1RU^*\) gives

\[
\begin{aligned}
\|\mathscr LZ\|_{r,1}^2
&=\alpha\|TZ-\langle TZ\rangle_\rho I\|_{\ell,\rho;UH_1RU^*}^2\\
&\le(1+\varepsilon)\lambda\|Z\|_{\ell,\rho_0;UH_1RU^*}^2
\le\|Z\|_{\ell,\rho_0;H_0Q}^2
=\|Z\|_{r,0}^2.
\end{aligned} \tag{10}
\]

Here the semicolon means contraction of the physical-index Gram matrix with the stated positive matrix. Thus its order is preserved by a positive matrix inequality. The last step is exactly (4). The other inequality in (4) proves (10) for \(r+1\).

Apply source `thm:interpolation` with one map, weight one, and tuple
\(m=1/h_{sj}\), \(x=\log(p_{sl}/p_{sr})/2\), \(y=-h_{sj}/2\).
The base measures are \(h_{sj}\ell(p_{sl},p_{sr})\). The output test space is two columns of centered finite eigenblock matrices. Each test has finitely many tuples, including its identity tails. A tuple multiplier acts by a constant on the diagonal entries of each physical component, preserving that component's centering. It therefore satisfies every test-space hypothesis of the theorem, despite the mixing in (9).

We obtain

\[
\|\mathscr LZ\|_{F_1}\le\|Z\|_{F_0},\qquad
F_{sj}(v)=\frac1{h_{sj}}\frac{f(h_{sj}v/2)f(-h_{sj}/2)}{f(h_{sj}(v-1)/2)}. \tag{11}
\]

Each \(F_{sj}\) has positive lower and finite upper bounds depending only on the fixed reference eigenvalue. This follows from the source identity
\(F(v)=[b(v)-(r+1/2)v]/(1-v)\), its positive continuous extension, and limits \(r,r+1\). Density extends (11) to completed centered spaces. For bounded tests it remains the actual map (9), by the arithmetic approximation argument following (8).

## 5. Transport of the weighted thermal defect

For a state \(\sigma\), let \(\mu=\operatorname{Tr}\sigma a\), and define the trace-class operator column

\[
D_A(\sigma)=(I+A)(a-\mu)\sigma-A\sigma(a-\mu),\qquad V_A(\sigma)=H_A^{1/2}D_A(\sigma). \tag{12}
\]

These columns represent linear functionals on observable columns by the pairing \(\sum_j\operatorname{Tr}(V_j^*Z_j)\). Their dual norms below refer to the metric (11). Finite energy makes \(a_j\sigma,\sigma a_j,a_j^*\sigma,\sigma a_j^*\) trace class by Hilbert–Schmidt factorization. Thus (12) does not require a bounded test to preserve the domain of an annihilator.

Let \(\gamma=\Phi\rho\), \(\mu_\gamma=K\mu\). A direct weak identity is

\[
D_Q(\gamma)=K\,\Phi(D_R(\rho)),\qquad
V_Q(\gamma)=\sqrt\lambda\,U\,\Phi(V_R(\rho)), \tag{13}
\]
where \(\Phi\) acts on each trace-class component. To verify the first identity, temporarily omit centering and write \(D_A=a\sigma+A[a,\sigma]\). In the dilation, inverse mode rotation gives the retained part of \(a\) as \(K^*c\) and of \(b\) as \(L^*c\). Partial trace of a discarded commutator vanishes. Therefore the partial traces of the input commutator columns are \(K^*[c,\gamma]\) and \(L^*[c,\gamma]\). Combining the columns with \(K,L\) produces
\(c\gamma+(KRK^*+LEL^*)[c,\gamma]\).
The environment defect is zero because \(\Gamma_E\) is thermal in its own passive eigenbasis. Centering subtracts precisely \(K\mu\,\gamma\). All discarded commutators can first be cut off in the discarded number basis; cyclicity then holds for bounded operators, and the trace-class products converge by the preceding factorization. This proves the weak identity for every bounded retained test. The second equality in (13) follows from (2).

Replacement and centering yield

\[
D_Q(\rho_0)=\alpha D_Q(\gamma)+\kappa\alpha\mu_\gamma(\gamma-\Gamma_Q). \tag{14}
\]

As a functional, the first term in the weighted version of (14) equals
\(\sqrt{\alpha\lambda}\,V_R(\rho)\circ\mathscr L\); the centering in \(\mathscr L\) does not contribute since the defect vanishes on identity. Define
\[
A_*^2=\alpha\lambda\|V_R(\rho)\|_{F_1,*}^2,
\qquad M_*^2=\alpha\lambda\mu^*H_1\mu
=\alpha\mu_\gamma^*H_0\mu_\gamma.
\]
Equation (11) bounds the leading functional by \(A_*\).

For the error use \(J(Z)=\sqrt{\kappa\alpha}\operatorname{Tr}[(\gamma-\Gamma_Q)Z]\). Mixture variance bounds \(|J(Z)|^2\) by each output arithmetic variance on centered tests. The two-weight logarithmic-mean operation in source Section 2 consequently gives
\(|J(Z)|^2\le\|Z\|_{\ell,\rho_0}^2\).
Let \(C^2=\max_j(h_{0j}\inf_v F_{0j}(v))^{-1}<\infty\). Then \(J\)'s norm on the \(j\)-th \(F\)-space is at most \(C\). Applying Cauchy–Schwarz to the two-component error in (14) gives

\[
\|V_Q(\rho_0)\|_{F_0,*}\le A_*+\sqrt\kappa C M_* . \tag{15}
\]

For clarity, its squared error bound is \(\kappa\alpha C^2\|H_0^{1/2}\mu_\gamma\|^2=\kappa C^2 M_*^2\). There is no assumption that the two output temperatures are equal. Choose

\[
0<\kappa\le\frac{\varepsilon^2}{2(\varepsilon+2)C^2}. \tag{16}
\]

Young's inequality applied to (15) yields

\[
\|V_Q(\rho_0)\|_{F_0,*}^2
\le(1+\varepsilon/2)A_*^2+(\varepsilon/2)M_*^2. \tag{17}
\]

The dual norms used here are finite at the regularized minima. Indeed in a reference eigenmode, with \(\rho_s=\operatorname{diag}(p_l)\), the unweighted defect entries are \([(r+1)p_r-rp_l](a_j-\mu_j)_{lr}\). The source's dual norm calculation and logarithmic-sum bounds apply for this particular \(r\). Finite seventh moment and \(\mathcal H_s\le C_sW^4\) bound all crossed logarithmic sums by a constant times the fifth moment. There are only two reference modes and all their \(h\)'s are finite and positive. Multiplying each component by \(\sqrt h\) preserves finiteness.

## 6. Common-rate covariance and exact cancellation

For a positive covariance \(A\), diagonalize it by a passive mode rotation and define
\[
\mathcal L_A\sigma=\sum_{j=1}^2[(a_j^{(A)}+1)\mathcal D[d_j]\sigma+a_j^{(A)}\mathcal D[d_j^*]\sigma],
\quad\mathcal D[d]\sigma=d\sigma d^*-\tfrac12\{d^*d,\sigma\},
\]
where \(a_j^{(A)}\) denotes an eigenvalue of \(A\), not an annihilator. All modes have decay rate one; only bath occupancies vary. Its Gaussian semigroup has characteristic function
\[
\chi_{\mathcal T_{A,t}\sigma}(z)=\chi_\sigma(e^{-t/2}z)
\exp[-(1-e^{-t})z^*(A+I/2)z].
\]
The channel itself acts by
\(\chi_{\Phi\sigma}(z)=\chi_\sigma(K^*z)\exp[-z^*(B+(I-KK^*)/2)z]\).
Substituting these two formulas and using \(Q=KRK^*+B\) proves

\[
\Phi\mathcal T_{R,t}=\mathcal T_{Q,t}\Phi. \tag{18}
\]

This uses scalar decay rate one, which commutes with \(K\). It does not require inverse-temperature-dependent drift or an input/output semigroup with the same covariance. Since \(\Gamma_Q\) is fixed, at a regularized minimum,
\(\delta_1=\mathcal L_R\rho\), \(\delta_0=\mathcal L_Q\rho_0=\alpha\Phi\delta_1\).

All these are weighted trace-class identities. In a reference eigenbasis the annihilators change total number by one; passive rotations preserve total number. With finite seventh moments, the source factorization around \(W^3\rho_sW^3\) shows \(W^2\delta_sW^2\) is trace class and number cutoffs converge in that norm. A passive dilation preserves total number and the fixed Gaussian environment has all moments, so slicing is continuous in the same weighted norm. This justifies (18) at the generator level and
\(\operatorname{Tr}\delta_0\mathcal H_0=\alpha\operatorname{Tr}\delta_1T\mathcal H_0\).
Traces against \(\mathcal H_s\) are defined by pairing with the bounded form \(W^{-2}\mathcal H_sW^{-2}\). Tracelessness follows by the cutoff limit. No two-sided positive perturbation by \(\delta_s\) is asserted.

Let \(C_s\) denote centered occupation matrices of \(\rho_s\), and let \(A_1=R,A_0=Q\). The componentwise entropy-production identity is

\[
\operatorname{Tr}(\mathcal L_{A_s}\rho_s)\mathcal H_s
=\|V_{A_s}(\rho_s)\|_{F_s,*}^2-\operatorname{tr}H_s(C_s-A_s). \tag{19}
\]

To check normalization, the source scalar calculation for mode \(j\) reads
\(\operatorname{Tr}\mathcal L_{r_j,j}\rho_s\mathcal H_s
=h_j\|D_j\|_{F_{sj},*}^2-h_j((C_s)_{jj}-r_j)\).
The first term is exactly the squared dual norm of \(\sqrt{h_j}D_j\). Summing gives (19). The absolute convergence checks in Section 5 justify the spectral expansion and anticommutator traces. Off-diagonal entries of \(C_s\) are retained in invariant notation; in a basis diagonalizing \(H_s\) their trace contribution is zero.

The corresponding drift identities are

\[
\operatorname{Tr}\delta_1d\Gamma(H_1)
=-\operatorname{tr}H_1(C_1-R)-\mu^*H_1\mu,
\quad
C_0-Q=\alpha K(C_1-R)K^*+\kappa\alpha\mu_\gamma\mu_\gamma^*. \tag{20}
\]

The first follows from \(\mathcal L_R^*(a_j^*a_j)=r_j-a_j^*a_j\) in a reference eigenbasis. The second follows from independent environment covariance, followed by the centered covariance of a two-branch mixture. Thus (1) matches the two energy terms exactly, including their matrix order.

Finally \(P_\zeta=\operatorname{Tr}\delta_1W^4\) has an upper bound independent of \(\zeta\) and the minimizing state. In the reference number basis its diagonal value at \((n_1,n_2)\) is
\[
\sum_j[(r_j+1)n_j((W-1)^4-W^4)+r_j(n_j+1)((W+1)^4-W^4)].
\]
The degree-four part is \(-4(n_1+n_2)^4\); the remaining terms are bounded in absolute value by a fixed constant times \(1+(n_1+n_2)^3\). Its supremum over nonnegative integers is finite. This also explains why different \(r_j\)'s cause no moment-bound problem.

Pair (6) with \(\delta_1\), using (18), and substitute (19)–(20). The result, before dropping any term, is

\[
0=\|V_Q(\rho_0)\|_{F_0,*}^2
-(1+\varepsilon)A_*^2-\varepsilon M_*^2
-\kappa\alpha\mu_\gamma^*H_0\mu_\gamma+\zeta P_\zeta. \tag{21}
\]

Equivalently the last mean term is \(-\kappa M_*^2\). Equation (17) implies
\[
0\le-\frac\varepsilon2(A_*^2+M_*^2)+C'\zeta. \tag{22}
\]
Thus the input mean and its weighted defect norm tend to zero as \(\zeta\downarrow0\).

## 7. Identification of the limit and endpoint

Uniform energy compactness supplies a trace-norm convergent subsequence of the minimizing inputs, with limit \(\widehat\rho\). In the fixed reference eigenmode number basis, every finite matrix test has a uniformly bounded centered \(F_1\)-norm, since \(F_1\) is bounded and the logarithmic mean is at most the arithmetic mean. Equations (22) and (12) therefore make its defect pairing tend to zero. The input means also tend to zero because \(H_1>0\). For each fixed number-basis test the annihilator-adjoint times the test, in either order, is bounded finite rank. Trace-norm convergence passes the uncentered identity to the limit:

\[
(r_{1j}+1)d_j\widehat\rho=r_{1j}\widehat\rho d_j,\qquad j=1,2. \tag{23}
\]

These identities determine the whole state. For matrix entries \((\mathbf p,\mathbf b)\) with \(p_j>0\), they give
\((r_{1j}+1)\sqrt{p_j}\widehat\rho_{\mathbf p,\mathbf b}
=r_{1j}\sqrt{b_j}\widehat\rho_{\mathbf p-e_j,\mathbf b-e_j}\).
If \(p_j>b_j\), iterate until the right side vanishes. The case \(p_j<b_j\) follows by self-adjointness. Every off-diagonal entry is zero; the diagonal ratio in coordinate \(j\) is \(r_{1j}/(1+r_{1j})\). Trace one gives \(\widehat\rho=\Gamma_R\), including the product structure in that eigenmode basis. No convergence of unbounded moments was used to pass (23).

The channel and replacement are trace-norm continuous; their outputs converge to \(\Gamma_Q\). Their energies remain bounded. Source entropy continuity makes the entropy part of (5) tend to zero. Its two penalties are nonnegative, so the limiting lower value of (5) is nonnegative, contradicting its uniform upper bound \(-c\). This proves the lower bound in (T) for every \(s>0\). The selected Gaussian input gives the reverse bound and attainment.

For \(s=0\), a state with zero entropy is pure. Given any finite-energy pure \(\rho\), let \(\rho_t=(1-t)\rho+t\Gamma_I\), \(0<t<1\). It is faithful, has positive finite entropy \(s_t\), and converges to \(\rho\) with uniformly bounded energy, so \(s_t\to0\). Apply the proved positive-entropy claim. For any \(R_t\) with \(\operatorname{tr}g(R_t)=s_t\), \(\|R_t\|\le g^{-1}(s_t)\to0\); hence the Gaussian minimum tends to \(\operatorname{tr}g(B)\). Output entropy continuity gives \(S(\Phi\rho)\ge\operatorname{tr}g(B)\). The vacuum attains equality. This proves the full endpoint and completes the author deduction at exactly the frozen scope.

## 8. What this does and does not establish

The argument supplies all steps at arbitrary finite energy through regularized minima and an actual compactness limit. The exact noncommuting identities (1)–(4), (10), (13), and (20) are the intended bridge. Scalar normalization by \(K/\sqrt\lambda\) generally fails the arithmetic comparisons; the test certificate records a rational example. The repaired map instead uses the unitary (2), and the weighted defect ensures the repair agrees with entropy production.

This is an author proof, not an independent review. The source already pays the difficult interpolation theorem and nearly all regularity/compactness operations. Its theorem explicitly permits arbitrary linear maps and coordinate-dependent parameters. It is therefore a serious contribution-gate risk that the complete extension is only a matrix packaging of paid operations plus standard Lagrange multipliers, polar normalization, and Gaussian covariance algebra. A strong theorem statement or a failure of the naive scalar map does not settle that gate. No count credit is requested by this file.

Primary comparisons, exact semantic reading extents, failed retrievals, developed-family exclusions, and integrity-only controls are recorded separately. No assertion of worldwide priority or exhaustive literature clearance follows from this bounded search. No mathematical conclusion is inferred from a checksum or a finite example.
