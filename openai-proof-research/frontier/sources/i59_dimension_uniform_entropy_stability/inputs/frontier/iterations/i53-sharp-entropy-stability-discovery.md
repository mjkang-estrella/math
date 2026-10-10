# I53: sharp entropy stability through quantitative Hessian compatibility

Date: 2026-10-09 \(America/Los_Angeles\). Status: **complete author-level fixed-dimensional candidate; independent proof and contribution reviews required**. No acceptance, priority, or finding-count decision is made here. All pinned theorem statements and proof operations are premises at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The candidate is a power estimate in quadratic Wasserstein distance to the **entire orthogonal orbit** of the centered exponential product. The additional construction is an error-controlled passage from weak compatibility of a nonlinear matrix field to a nearly associative cubic tensor, followed by a constructive orthogonal decomposition of that tensor. A second, distinct construction uses successive spectral partitions and gives a weaker exponent. Neither argument uses a finite-dimensional Łojasiewicz theorem or a compactness modulus. Dimension-uniform normalized stability and a Banach–Mazur simplex estimate remain open in this report.

## 1. Frozen scope and three early screens

The exact assignment is retained in `../sources/i53_sharp_entropy_stability_discovery/brief.txt`. `inputs.json` records the frozen instructions, front pages, complete tree, and selected prior reports. The four shared status files were mutable at capture time; their later drift is informational, not a reason to rewrite old seals. No shared files, prior verifiers, Git index, or commits are changed. In particular, I49's order-sensitive search failure is left untouched. Corpus searches here compare **sorted line multisets**.

Write
\[
 Z_m=(E_1-1,\ldots,E_m-1),\quad E_i\stackrel{\rm iid}{\sim}\operatorname{Exp}(1),\qquad
 \delta(f)=h(f)-m-\tfrac12\log\det\operatorname{Cov}(f).
\]
For a centered isotropic density, set
\[
 d_m(f)=\inf_{O\in O(m)}W_2(f,\mathcal L(OZ_m)).
\]
All three screens were checked against actual primary statements and the pinned source's operations before selecting the main construction.

1. **Gaussian transport / dimension-uniform Wasserstein target U.** Are there numerical constants \(C>0\) such that, for every dimension and centered isotropic log-concave density,
   \[
   d_m(f)^2/m\le C\sqrt{\delta(f)/m}?
   \tag{U}
   \]
   The sharp source's retained slack is genuinely relevant, but the normalized trace weight grows only like the square root of a large eigenvalue. Its exact equality argument does not prove \(U\). Filonov–Kachkovskiy's matrix-count dependence cannot be suppressed. We develop the unrestricted fixed-dimensional theorem below and isolate the remaining dimension losses in §9; \(U\) is neither proved nor refuted.

2. **Information / one-dimensional localization target K.** For fixed \(m\), can a finite bound \(\inf_O D(f\Vert\mathcal L(OZ_m))\le C_m\delta(f)^\alpha\), \(\alpha>0\), hold for all centered isotropic log-concave densities? **No**, already in dimension one. For \(a>0\), the asymmetric Laplace density
   \[
   g_a(x)=(1+a)^{-1}\begin{cases}e^{x/a},&x<0,\\ e^{-x},&x\ge0\end{cases}
   \]
   has mean \(1-a\), variance \(1+a^2\), entropy \(1+\log(1+a)\), and hence standardized gap
   \[
   \delta_a=\log(1+a)-\tfrac12\log(1+a^2)\longrightarrow0.
   \]
   Its standardized density is positive everywhere, whereas either one-dimensional equality density vanishes on a half-line. Both directed divergences from this density to the two equality laws are infinite. Products give the same obstruction in all dimensions and every orientation. This refutes K, not Wasserstein stability and not reverse-directed KL under extra support hypotheses. Melbourne–Nayar–Roberto's rearrangement/localization proof supplies the scalar sharp bound, but does not turn a small variance loss into this impossible support conclusion.

3. **Convex-body / cone-section target S.** With \(\varepsilon_K=\log(L_{\Delta_n}/L_K)\), seek \(d_{\rm BM}(K,\Delta_n)-1\le C_n\varepsilon_K^{\beta_n}\) for every convex body. Here \(d_{\rm BM}\) is the affine Banach–Mazur distance: the infimum of \(b/a\) over \(a,b>0\), a translate \(K-z\), and a linear image \(T\Delta_n\), with \(aT\Delta_n\subset K-z\subset bT\Delta_n\); the reference simplex contains zero in its interior. The source's cone law has entropy gap **exactly \(n\varepsilon_K\)**. Its equality proof uses exact equality of closed supports, the unique cone vertex, and a height-one section. These operations do not quantitatively follow from W2 proximity. Rademacher and Kipp study maximizer restrictions by variation, not a global distance-to-simplex estimate. A quantitative cone-section route is developed to the unpaid interface in §9. No simplex theorem is asserted.

We choose the Wasserstein mechanism. The following is the exact result proved here, not a restatement of \(U\).

## 2. Candidate H53 and dependencies

**H53.** For every integer \(m\ge2\), there is a finite constant \(C_m\), depending only on \(m\), such that every log-concave probability density \(f\) on \(\mathbb R^m\), with mean \(a\) and covariance \(C>0\), satisfies
\[
 \inf_{O\in O(m)}W_2\bigl(\mathcal L(C^{-1/2}(X-a)),\mathcal L(OZ_m)\bigr)
 \le C_m\delta(f)^{1/(m+6)}.
 \tag{H53}
\]
For \(m=1\), the same assertion holds with exponent \(1/2\). Constants are independent of the density, support, smoothness, and Hessian bounds. They are **not dimension-uniform**. A complete specification of how to choose finite dimensional constants is given in §§3–6; the exponent is explicit, while no optimized numerical value of \(C_m\) is claimed.

Dependencies from the main pinned family (all eleven cached manuscript/README files copied and Git-blob verified):

* `transport.tex`, `tr:normalization`: for each smooth uniformly log-concave target there is a symmetric positive definite \(P\) making \(\mathbb E q^{-1}(DF)=0\), where \(F\) is its Gaussian Brenier map after applying \(P\). This is not ordinary isotropic normalization.
* `matrix.tex`, `mat:strict-remainder` and `mat:rigidity-weight`: with \(A=q^{-1}(DF)=L+Y\), \(L(x)=\sum x_rX_r\), \(B=\sum X_r^2\),
  \[
  \|Y\|_{L^2(\gamma)}^2\le1000\delta,\qquad
  \sum_i\omega(\lambda_i(B))\le2000\delta.
  \tag{2.1}
  \]
* `rigidity.tex`, `lem:spectral-lipschitz`: \(\|q(M)-q(N)\|_F\le\|M-N\|_F\). The same file's exact Taylor compatibility and commutation calculation are inherited, not new discoveries.
* `approximation.tex`, `geo:approximation`: smooth approximation with entropy, first moments, covariance and weighted density convergence. Its exponential envelope is allowed to depend on the original density, never on the approximation index.

We read the full scalar, matrix, transport, rigidity, approximation, geometry and scalar-certificate operations. The coefficient-pair surplus in `transport.tex` is consumed in `matrix.tex`; it is not silently retained a second time as an extra commutator bound. The related general-Mahler manuscript was also inspected at its projection/linear-field/equality interfaces: its different deficit and layer measures are not asserted to be bounded by the present entropy deficit.

Classical ingredients used with proofs or elementary derivations below are mollification, Gaussian Poincaré, spectral calculus, polarization of a cubic form, and covariance comparison. No external conjecture or recent theorem is promoted to a premise. The external almost-commuting theorem is an audited comparison; Construction B below provides its own real-matrix proof.

## 3. Quantitative normalization and weak compatibility

First assume that \(f\) is smooth, centered, isotropic, and has potential with Hessian between positive finite multiples of the identity. Apply the pinned normalization. Center \(F\), so
\[
 F_\#\gamma_m=P_\#f,\quad DF=q(A),\quad \mathbb EA=0,
 \quad A=L+Y,\quad L(x)=\sum_rx_rX_r.
\]
All norms of matrix or tensor arrays below are **unnormalized** Euclidean/Frobenius norms, unless explicitly called operator norms.

The source weight is
\[
 \omega(\lambda)=\frac{3(\lambda-1)^2}{37+3\lambda}
 \left(\frac3{20}+\frac{49}{100}\frac{37}{37+3\lambda}\right)
 \min\left(\frac{13}{100},\frac{32}{25\sqrt\lambda}\right).
\]
It gives an explicit small-gap cutoff. For \(\lambda\le1/2\), use \(37+3\lambda\le40\), the second factor at least \(3/20\), and the minimum \(13/100\), to get \(\omega\ge117/320000>10^{-4}\). For \(\lambda\ge2\), use \((\lambda-1)^2\ge\lambda^2/4\), \(37+3\lambda\le(43/2)\lambda\), and
\(\min(13/100,32/(25\sqrt\lambda))\ge13/(100\sqrt\lambda)\), to get
\[
 \omega(\lambda)\ge\frac{117}{172000}\sqrt\lambda>10^{-4}.
\]
Thus \(\delta<5\cdot10^{-8}\) implies \(\operatorname{spec}B\subset[1/2,2]\). On that interval
\[
 \omega(\lambda)\ge \frac{117}{86000}(\lambda-1)^2>10^{-3}(\lambda-1)^2.
\]
Consequently
\[
 \|B-I\|_F\le\sqrt{2\cdot10^6\delta},\qquad
 \sum_r\|X_r\|_F^2=\operatorname{tr}B\le2m,
 \qquad \|DF-q(L)\|_{L^2(\gamma)}\le e:=\sqrt{1000\delta}.
 \tag{3.1}
\]
At equality these follow directly with zero errors; no limiting argument is needed in the smooth case.

Here is the quantitative analytic interface. Define column curls
\[
 K_{irs}(x)=\partial_r q(L(x))_{is}-\partial_s q(L(x))_{ir}.
\]
As a distribution this equals the curl of (q(L)-DF), since weak mixed derivatives of \(F_i\) commute. We do **not** infer that a small \(L^2\) error has small classical derivatives.

Fix once and for all a nonnegative smooth bump 
\(\rho(x)=c_m\exp[-1/(1-|x|^2)]\mathbf1_{|x|<1}\), normalized to integral one. Set \(R=(10\sqrt{2m})^{-1}\). On \(B_{2R}\), \(\|L(x)\|_{\rm op}\le1/5\). Real analyticity of \(q\) near zero, or smooth matrix functional calculus on this compact spectral interval, bounds \(K\) and its first two derivatives by finite constants depending only on \(m\). These bounds can be specified as suprema over the compact set \(\sum\|X_r\|_F^2\le2m, |x|\le2R\), of the indicated explicit derivatives of \(q(\sum x_rX_r)\). They involve neither \(q^{-1}\) nor \(f\).

For \(0<h\le R\), distributional integration by parts and the Gaussian density lower bound on \(B_R\) give, componentwise,
\[
 |(K*\rho_h)(0)|\le C_m e h^{-m/2-1},\quad
 |\nabla(K*\rho_h)(0)|\le C_m e h^{-m/2-2}.
\]
The mean-value theorem for \(K,\nabla K\) bounds their differences from these averages by \(C_mh\). All array norms cost only a finite, displayed dimension-dependent aggregation. Choosing \(h=e^{2/(m+6)}\le R\) proves
\[
 |K(0)|+|DK(0)|\le C_m e^{2/(m+6)}=:\nu.
 \tag{3.2}
\]
If \(e^{2/(m+6)}>R\), defer to the large-gap bound in §6. The constants in (3.2) can thus be chosen from the bump's first two derivative \(L^2\) norms, the lower Gaussian density, and the preceding compact derivative suprema. This specifies finite constants without an unproved quantitative compactness principle.

Put \(a=q'(0)=2/\pi>0\), \(b=q''(0)/2>0\). Taylor differentiation gives the **exact** jets
\[
 K_{\cdot rs}(0)=a(X_re_s-X_se_r),
\]
\[
 \partial_tK_{\cdot rs}(0)
 =b\{(X_rX_t+X_tX_r)e_s-(X_sX_t+X_tX_s)e_r\}.
 \tag{3.3}
\]
Set \(S_{rs}=X_re_s-X_se_r\). In the braces on the right,
\[
 X_rX_te_s-X_sX_te_r+X_tS_{rs}
 =[X_r,X_s]e_t+X_rS_{ts}-X_sS_{tr}+X_tS_{rs}.
\]
Using (3.1), (3.2), and \(a,b>0\), we conclude
\[
 \Big(\sum_{r,s}|S_{rs}|^2\Big)^{1/2}
 +\Big(\sum_{r,s}\|[X_r,X_s]\|_F^2\Big)^{1/2}\le C_m\nu.
 \tag{3.4}
\]
This is a quantitative version of the source's zero-jet calculation, with its weak-derivative loss fully paid.

View \(X\) as the tensor \(X_{ijr}=(X_r)_{ij}\), and let \(T\) be its full symmetrization in the three indices. Since \(X_{ijr}=X_{jir}\), (3.4) implies \(\|T-X\|_F\le C_m\nu\), by writing the symmetrization as the average of six permutations and pairing transpositions. Write \(T_r=(T_{ijr})_{ij}\). Matrix product expansion and Cauchy–Schwarz give
\[
 \eta(T):=\max\left\{
 \Big\|\sum_rT_r^2-I\Big\|_{\rm op},
 \Big(\sum_{r,s}\|[T_r,T_s]\|_F^2\Big)^{1/2}\right\}
 \le C_m(\nu+\sqrt\delta)\le C_m\delta^{1/(m+6)}.
 \tag{3.5}
\]
For example \(\|\sum T_r^2-\sum X_r^2\|_F\le(2\|X\|_F+\|T-X\|_F)\|T-X\|_F\); the commutator comparison follows by expanding the two products, with the same bounded-array factors. Choose the small-gap cutoff further so that \(\eta(T)\le10^{-6}m^{-4}\).

## 4. Construction A: cubic maximization and quadratic error accumulation

The next lemma is the principal constructive algebraic bridge. Its input is an **equation residual**, not a previously known distance to an orthogonally decomposable tensor.

**Lemma A.** Let \(T\) be a real fully symmetric cubic tensor on \(\mathbb R^m\), with symmetric slices \(T_r\), and let \(\eta=\eta(T)\le10^{-6}m^{-4}\), as in (3.5). There is an orthonormal basis \(u_1,\ldots,u_m\) such that
\[
 \left\|T-\sum_{j=1}^m u_j^{\otimes3}\right\|_F\le20m\eta.
 \tag{A}
\]
Signs are absorbed into the \(u_j\), since the tensor order is odd.

**Proof.** We give the recursion, including its errors. In a current \(d\)-dimensional subspace, let the current tensor have residual \(\eta_d\le2\eta\). Write its multiplication as \(x*y=T_x y\), where \(T_x=\sum x_rT_r\), and let \(p(x)=T(x,x,x)\). Choose a global maximizer \(v\) of \(p\) on the unit sphere and set \(c=p(v)\). This maximizer exists on the compact sphere. Because \(p\) is odd, \(c=\max|p|>0\).

Here is a quantitative lower bound before any deflation. The trace identity gives \(\|T\|_F^2=\operatorname{tr}\sum T_r^2\ge d(1-\eta_d)\). The real polarization identity
\[
 T(x,y,z)=\frac1{48}\sum_{\epsilon_i=\pm1}
 \epsilon_1\epsilon_2\epsilon_3p(\epsilon_1x+\epsilon_2y+\epsilon_3z)
\]
shows that every unit-coordinate entry of \(T\) has absolute value at most \(9c/2\). Thus \(c\ge\sqrt{1-\eta_d}/((9/2)d)\ge1/(10d)\).

The first- and second-order conditions on the sphere give
\[
 v*v=cv,\qquad T(v,w,w)\le c|w|^2/2\quad(w\perp v).
 \tag{4.1}
\]
Indeed the constrained Hessian is \(6T_v-3cI\) on \(v^\perp\). In the decomposition \(\mathbb Rv\oplus v^\perp\), \(T_v=\operatorname{diag}(c,H)\), where \(H\) is real symmetric and all its eigenvalues are at most (c/2).

Full tensor symmetry gives \(T_wv=T_vw\). Hence
\[
 (T_v^2-cT_v)w=[T_v,T_w]v.
\]
For unit (v,w), Cauchy–Schwarz in the coefficient indices bounds the operator norm of the commutator by \(\eta_d\). Thus \(\|H^2-cH\|_{\rm op}\le\eta_d\). If \(\lambda\le c/2\) is an eigenvalue of \(H\), then \(c-\lambda\ge c/2\), so \( |\lambda|\le2\eta_d/c\), including negative eigenvalues. Therefore
\[
 \|H\|_F^2\le4d\eta_d^2/c^2\le400d^3\eta_d^2.
\]
Since \(v^T(\sum T_r^2)v=\|T_v\|_F^2=c^2+\|H\|_F^2\), the threshold \(\eta_d\le2\cdot10^{-6}m^{-4}\) implies \(c\ge1/2\). Substituting this improved lower bound gives
\[
 \|H\|_F^2\le16d\eta_d^2,\qquad |c-1|\le\eta_d+16d\eta_d^2\le2\eta_d.
 \tag{4.2}
\]

Let (T') be the restriction of \(T\) to \(v^\perp\) in all three slots. For an orthonormal basis of the complement and columns \(h_a=He_a\), the original slices indexed by \(a>1\) have block form
\[
 T_a=\begin{pmatrix}0&h_a^T\\h_a&T'_a\end{pmatrix}.
\]
The restricted quadratic normalization and commutators obey exact identities
\[
 \Big(\sum_rT_r^2\Big)_{v^\perp}=\sum_a(T'_a)^2+2H^2,
\]
\[
 [T_a,T_b]_{v^\perp}=[T'_a,T'_b]+h_ah_b^T-h_bh_a^T.
 \tag{4.3}
\]
The array norm of the last outer-product errors is at most \(2\|H\|_F^2\): expand the squared norms, or use the triangle inequality on the two arrays, each of norm \(\|H\|_F^2\). Thus
\[
 \eta(T')\le\eta_d+32d\eta_d^2\le\eta_d+64m\eta_d^2.
 \tag{4.4}
\]
Rotating all tensor indices before each restriction preserves the full commutator-array norm, by orthogonality in the two coefficient indices and in matrix coordinates. No matrix-count factor is omitted.

Start with \(\eta_m=\eta\). Inductively the increase in each of at most \(m\) steps is at most \(256m\eta^2\), and the total is at most \(256m^2\eta^2\le\eta\). Hence \(\eta_d\le2\eta\) throughout, justifying all thresholds above. In dimension one the argument simply selects the sign of the single coefficient.

At a step, \(T\) differs from \(cv^{\otimes3}+T'\) by the three placements of \(v\otimes H\), whose total squared tensor norm is \(3\|H\|_F^2\). These discarded entries at different steps are orthogonal: classify an entry by its first removed basis direction. The diagonal coefficient errors are orthogonal to all of them. Therefore, after all steps,
\[
 \left\|T-\sum_ju_j^{\otimes3}\right\|_F^2
 \le\sum_{d=1}^m\{3\cdot16d(2\eta)^2+(4\eta)^2\}
 \le208m^2\eta^2<(20m\eta)^2.
\]
This proves \(A\). ∎

This construction differs from both exact simultaneous diagonalization and perturbation theory given an already nearby decomposable tensor. The spectral gap \(c-\lambda\ge c/2\) comes from the **maximizing cubic direction**, and the error added by restriction is quadratic, as (4.3) shows. Those are the two points that must survive independent review.

## 5. Construction B: successive spectral partitions

This second construction uses only approximate commutation and coefficient symmetry. It independently yields a full, weaker power law, without Lemma A or a cubic optimization argument.

**Spectral partition lemma.** For \(k\) real symmetric \(d\times d\) matrices \(H_1,\ldots,H_k\) with operator norms at most one and pairwise Frobenius commutators at most \(z\le1\), there are commuting real symmetric matrices \(D_i\) with
\[
 \max_i\|H_i-D_i\|_F\le C_{d,k}z^{1/2^{k-1}}.
 \tag{5.1}
\]
For \(k=1\) there is no error. To prove the induction, diagonalize \(H_1\); group consecutive eigenvalues into clusters by retaining a gap whenever it exceeds \(h\). A cluster has diameter at most (dh), and distinct clusters are separated by more than \(h\). Replace \(H_1\) by a scalar on each cluster, at cost at most \(d^{3/2}h\). For \(i>1\), erase entries across clusters, at cost at most (z/h), because \([H_1,H_i]_{ab}=(\lambda_a-\lambda_b)(H_i)_{ab}\). The resulting block restrictions remain contractions.

Their commutators within a block are bounded by (z+4z/h), using product expansion and contraction. Apply induction to (k-1) matrices separately within these common invariant blocks, and combine the errors with the Euclidean sum over at most \(d\) blocks. At \(h=\sqrt z\), the input for the next stage is at most \(5\sqrt z\); the constants absorb the factor five. If this exceeds one, zero approximants and larger constants supply the bound. The exponent is halved at each stage. All changes are real orthogonal changes or real block truncations, proving the real version directly. This construction deliberately allows constants depending on both \(d\) and \(k\).

Apply it to \(H_r=X_r/\sqrt2\). The norm bound follows from \(X_r^2\preceq B\preceq2I\); (3.4) supplies their commutators. Obtain commuting symmetric \(D_r\) with total array error
\(\zeta\le C_m\nu^{1/2^{m-1}}\). Diagonalize them by a common \(U\), and rotate the coefficient index as well:
\[
 \widetilde X_i=U^T\Big(\sum_rU_{ri}X_r\Big)U,\qquad
 \widetilde D_i=U^T\Big(\sum_rU_{ri}D_r\Big)U.
\]
The \(\widetilde D_i\) are diagonal. Coefficient symmetry of \(X\), with error (3.4), implies for \(i\ne j\)
\[
 |(\widetilde D_i)_{jj}|+|(\widetilde D_j)_{ii}|\le C_m(\nu+\zeta).
\]
This follows by looking at the \(e_j,e_i\) components of \(\widetilde D_ie_j-\widetilde D_je_i\), which are orthogonal. The quadratic normalization of \(D\) differs from identity by at most \(C_m(\sqrt\delta+\zeta)\). Hence the only surviving entry \((\widetilde D_i)_{ii}\) is within \(C_m(\sqrt\delta+\nu+\zeta)\) of a sign. Round it to that sign. Absorb signs into the corresponding basis vectors. We have constructed \(X^*_r\) with
\[
 \sum_r\|X_r-X^*_r\|_F^2\le C_m\nu^{2/2^{m-1}},
 \qquad L^*(x)=\sum_r x_rX^*_r
   =\sum_j\langle u_j,x\rangle u_ju_j^T.
\]
The analytic and normalization steps in §6 now give
\[
 d_m(f)\le C_m\delta^{1/((m+6)2^{m-1})}.
 \tag{B53}
\]
Filonov–Kachkovskiy, Theorems 2–3, supplies a stronger treatment of arbitrary fixed-count families in normalized Hilbert–Schmidt norm than many naive partitions, but its exponent degrades with the number of matrices. We do not call that dimension-free when the number of matrices is \(m\). Construction B also shows precisely what would already follow from a conventional almost-commuting-matrix bridge. H53 improves the exponent by using the symmetric tensor and its normalization in Construction A.

## 6. Reconstruction of the probability law; all normalization and approximation costs

For Construction A, (3.5) and Lemma A yield an orthonormal basis with
\[
 \|L-L^*\|_{L^2(\gamma)}\le C_m\delta^{1/(m+6)},\qquad
 L^*(x)=\sum_j\langle u_j,x\rangle u_ju_j^T.
\]
Define the centered map
\[
 H(x)=\sum_j u_j\{t(\langle u_j,x\rangle)-1\},\qquad
 t(s)=-\log\Phi(-s).
\]
Then \(DH=q(L^*)\), \(\mathbb EH=0\), and \(H_\#\gamma=\mathcal L(UZ_m)\), with covariance \(I\). The source's global **forward** Lipschitz bound gives
\[
 \|DF-DH\|_{L^2(\gamma)}\le\|Y\|_2+\|L-L^*\|_2
 \le C_m\delta^{1/(m+6)}.
\]
Both maps lie in Gaussian \(H^1\). Poincaré applied to their centered difference supplies
\[
 r:=\|F-H\|_{L^2(\gamma)}\le C_m\delta^{1/(m+6)}.
 \tag{6.1}
\]
There is no tail truncation or inverse-\(q\) Lipschitz claim here.

It remains to pay for the affine normalization, rather than leaving \(P^{-1}\) in the conclusion. The source's normalization proof contains the following useful operation. Convexity of scalar \(q\) and \(\mathbb EA=0\) give \(\mathbb E q(A)\succeq q(0)I\) by applying scalar Jensen to each expected spectral measure. Projection of \(F\) on first Gaussian chaos gives
\[
 P^2=\operatorname{Cov}F\succeq(\mathbb EDF)^2\succeq q(0)^2I,
 \qquad\|P^{-1}\|_{\rm op}\le q(0)^{-1}.
 \tag{6.2}
\]
The second matrix inequality uses the spectral theorem for the single matrix \(\mathbb EDF\), not an invalid general operator monotonicity of squaring.

Also
\[
 \|P-I\|_F\le r.
 \tag{6.3}
\]
For completeness, let \(M=\mathbb E[(P^{-1}F)H^T]\). Both vectors are centered isotropic, so Cauchy–Schwarz gives \(\|M\|_{\rm op}\le1\). Diagonalizing the positive matrix \(P\) gives \(\operatorname{tr}(PM)\le\operatorname{tr}P\). Thus
\[
 r^2=\operatorname{tr}P^2+m-2\mathbb E\langle F,H\rangle
 \ge\operatorname{tr}(P-I)^2.
\]
Using the coupling already on Gaussian space,
\[
 W_2(f,H_\#\gamma)
 \le\|P^{-1}F-H\|_2
 \le q(0)^{-1}\{r+\|(I-P)H\|_2\}
 \le2q(0)^{-1}r.
 \tag{6.4}
\]
Covariance \(I\) of \(H\) gives \(\|(I-P)H\|_2=\|I-P\|_F\). This removes the condition number without assuming it was controlled before the argument. The inherited lower bound (6.2) is uniform even when the smooth potential's Hessian constants degenerate.

To make \(C_m\) precise, select the finitely many derivative/bump constants in §3 and product-array constants in (3.4)–(3.5). Choose \(\delta_m>0\) so that \(i\) \(\delta_m<5\cdot10^{-8}\), (ii) \((1000\delta_m)^{1/(m+6)}\le R\), and (iii) the right side of (3.5) is at most \(10^{-6}m^{-4}\). Their finite minima define such a positive cutoff without reference to the input density. Let \(K_m\) be the constant in (6.4) on this interval. Set \(C_m=\max(K_m,\sqrt{2m}\delta_m^{-1/(m+6)})\). For \(\delta\ge\delta_m\), independent centered isotropic coupling gives \(d_m\le\sqrt{2m}\), proving H53 globally. This is a concrete finite-constant prescription, not an effective claim about an unexamined compactness modulus.

For a general density, take the source's approximants \(f_j\). Their weighted \(L^1\) convergence gives convergence of first and second moments and W2 convergence (one may couple the common density part identically and the residual parts independently; the residual second moment tends to zero). Whiten and center each approximant. Covariance matrices converge to \(C>0\), so the whitened approximants converge in W2 to the whitened \(f\), and their gaps converge to \(\delta(f)\). The distance to any fixed subset of a metric space is 1-Lipschitz, so H53 passes to the limit without a rate for the approximation or any selection of limiting orientations. Applying an affine change to a smooth approximant preserves its positive finite Hessian bounds. This completes H53 in every asserted scope.

For \(m=1\), (3.1) gives \(|X_1^2-1|\le C\sqrt\delta\), so \(X_1\) is within \(C\sqrt\delta\) of a sign. No curl, mollification or matrix rounding is needed. The same reconstruction proves the stated exponent \(1/2\). ∎

## 7. Actual primary-source and companion audit

Full retrieved bytes, UTC timestamps, HTTP outcomes, hashes and reproducible text extractions are in `literature/manifest.json`. Read ranges and pinned proof labels are separately retained in `passages.json`; the list is an audit record, not a claim to have proved external sources. Current arXiv pages were consulted rather than assuming the first version remained current.

* **Fradelizi–Marín Sola**, [arXiv:2406.07406v1](https://arxiv.org/abs/2406.07406v1), current accessible arXiv version: Conjecture 3(iii), Proposition 5.2 and Lemma 5.2 are the entropy/isotropic formulation and cone lift. Proposition 5.2\(i\) uses auxiliary dimensions tending to infinity. Their projective/log-Laplace variation proof concerns functional Mahler minimizers. These facts supply neither a uniform stability modulus nor a quantitative reverse passage from a near-product law to a simplex section. The pinned bibliography lists a 2026 journal publication; a current journal proof was not retrieved here. The direct author-PDF request failed TLS certificate verification, recorded as a failure. The version limitation is retained.
* **Melbourne–Nayar–Roberto**, [arXiv:2309.01840v2](https://arxiv.org/abs/2309.01840v2), and the [published article](https://link.springer.com/article/10.1007/s00440-025-01431-3), whose author-hosted PDF was also read: Theorem 1.1 is the scalar bound. The current article's §§3.1–3.3 use decreasing rearrangement, degrees of freedom, and localization to two-piece log-affine densities; §4 finishes a scalar inequality. This is not a law-distance estimate for arbitrary near minimizers. The source's all-dimensional equality theorem, not extrapolation of scalar localization, is our starting premise.
* **Filonov–Kachkovskiy**, [arXiv:1008.4002v2](https://arxiv.org/abs/1008.4002v2), Theorem 2 and all of its proof, and Theorem 3: the norm is normalized Hilbert–Schmidt; the two-matrix power is \(1/4\). The many-matrix construction iterates a fourth-root loss. It addresses fixed matrix count uniformly over matrix size, not this problem with both counts growing together. The actual block-truncation proof is real when the matrices are real, but we give Construction B explicitly rather than relying on an unstated field conversion.
* **Boralevi–Draisma–Horobeţ–Robeva**, [arXiv:1512.08031v1](https://arxiv.org/abs/1512.08031v1), §3.1, Lemma 11 and Proposition 12: exact associativity characterizes symmetric orthogonal decomposition. Its proof uses orthogonal simple ideals and a classification argument, and its quadratic equations are prior art. Lemma A does not claim that exact characterization as new; it gives a small-residual estimate with explicit threshold, linear error, and a quadratic deflation budget.
* **Auddy–Yuan**, [arXiv:2007.09024](https://arxiv.org/abs/2007.09024), current retrieved PDF version recorded in the file and manifest: Theorem 2.4 compares two already odeco tensors. Theorem 3.1 starts with a decomposition whose factor matrices are nearly isometric and rounds them by polar decomposition. The input distance or nearly orthogonal factorization is not the equation residual (3.5). Their singular-vector bounds should not be invoked here before constructing an odeco approximation.
* **Mu–Hsu–Goldfarb**, [arXiv:1705.10404](https://arxiv.org/abs/1705.10404), Theorem 2.2, Lemma 2.3, Theorem 3.1 and Lemma 3.2: successive best rank-one approximation and deflation with controlled accumulation are prior techniques. Their input is a known orthogonally decomposable tensor plus a small additive perturbation. The proposed distinction in Lemma A is deriving that proximity from small associativity and normalization residuals. Neither cubic maximization nor deflation itself is claimed as new.
* **Rademacher**, [arXiv:1404.5662v2](https://arxiv.org/abs/1404.5662v2), Theorems 1–2 and the facet-variation setup: necessary symmetry/local-extremum conditions for simplicial polytopes, then the simplex conclusion. **Kipp**, [arXiv:2411.08722v2](https://arxiv.org/abs/2411.08722v2) and [published article](https://link.springer.com/article/10.1007/s00454-026-00829-7), Theorem 1.5 and its proof: a bound on the dimension of decomposability of the polar of a local maximizer, obtained from a kernel of first-moment/covariance variations and a second variation. Kipp's [platonic-solids paper](https://arxiv.org/abs/2407.01353), Theorem 1.2, strengthens the simplicial hypothesis to a simplicial vertex. These are strong structural restrictions, but do not state H53 or quantitative global simplex stability.
* The separate pinned **general Mahler** proof, `06-linear-equality.tex`, obtains exact coefficient commutation from a spectral measure supported on the diagonal; its retained inequality contains a different matrix/layer defect. Its `09-consequences.tex` explicitly warns that an auxiliary-dimensional functional limit does not classify functional equality. Neither these operations nor the already-contained entropy equality/Mahler implication are new findings here.

The entire 749-manuscript path inventory and 9,340-file ignored corpus were used. The narrow entropy/isotropic/commutation search and the broader companion screen are frozen as line multisets, not a claim to have read every one of those files. Prior I05 already rejected a subgaussian/KLS transfer using the exponential equality law; this report makes no such claim. R013 is not used: none of the proofs here invokes a logBM moment-product estimate.

**Novelty boundary.** Construction B and source equality plus an unspecified compactness modulus are insufficient bases for a substantial nomination. The potentially new contribution in H53 is the explicit weak-Hessian-to-cubic reconstruction and especially Lemma A's equation-residual-to-product construction, with normalization and nonsmooth passage closed. Every ingredient that is merely classical or already in a source is identified above. Bounded searches found no exact H53 duplicate in the inspected primary statements, but do not establish worldwide priority. Whether this integrated bridge meets the project's substantial standard is for the separate contribution review.

The relevant named problems are sharp entropy minimization for log-concave densities and the strong isotropic constant/simplex problem; their inequalities and equality cases are already settled **under the pinned premises**. The remaining subject is quantitative near-extremizer structure. A direct MathDB request returned a general page without a verified matching problem entry in the retained text, and indexed searches did not establish a problem-specific significance score. No MathDB score or featured status is assigned.

## 8. Adversarial tests and limitations of the finite diagnostics

The reproducible standard-library diagnostics test identities and actual examples, not the universal theorem:

* exact rational tests of symmetrization, both jet identities, coefficient-error commutator expansion, tensor rotations, and both deflation identities (4.3);
* a two-dimensional cubic family with a known global maximizing direction, testing the sign of the constrained Hessian, the small complementary eigenvalue, and the quadratic restriction error;
* exact checks of the induction budget at the largest allowed residual for multiple dimensions;
* centered/variance-normalized truncated exponentials and asymmetric Laplace laws, with explicitly evaluated gaps and one-dimensional quantile W2 diagnostics at two quadrature resolutions;
* the example \(X_1=I_2,X_2=0\), which has exact commutation and \(B=I\) but fails coefficient symmetry and Jacobian compatibility: simultaneous diagonalization alone cannot finish the proof;
* the blowup of (1/q'(-R)), and abstract high-eigenvalue arrays showing why normalized source slack does not imply normalized \(\operatorname{tr}(B-I)^2\) control.

None of these examples is called a counterexample to \(U\). Numerical law distances are upper bounds to the whole-orbit distance, since they use a specified orientation, not an optimization over all orientations. In one dimension both signs are also evaluated. Neither a TV estimate nor a KL estimate is inferred from W2. No numerical step is used to certify the maximum in Lemma A's universal proof.

The independent proof review should attack: the weak-to-jet exponents and their Gaussian/Lebesgue conversion; the tensor-symmetrization error; the identity \(T_v^2-cT_v=[T_v,T_{(\cdot)}]v\); the use of a **global** cubic maximizer; the quadratic, rather than linear, restriction errors; simultaneous rotation of all tensor indices; the covariance comparison (6.3); and weighted approximation. The constant prescription uses explicit finite suprema of a known smooth matrix function, not hidden density-dependent constants. It does not give a practical numerical \(C_m\).

## 9. What remains unpaid beyond H53

**Dimension-uniform route.** Lemma A has polynomial dimensional costs and an explicit small-total-residual threshold, but (3.2) localizes at one point of an \(m\)-dimensional Gaussian space. The cost is \(h^{-m/2-2}\), and the exponent (1/(m+6)) degrades to zero. An averaged curl/chaos argument would have to recover the coefficient symmetry and almost-associativity without this small-ball loss. One cannot simply replace all norms by normalized traces: for diagonal \(B_m=\operatorname{diag}(m^{3/2},1,\ldots,1)\),
\[
 m^{-1}\operatorname{tr}\omega(B_m)\asymp m^{-1/4}\to0,
 \qquad m^{-1}\operatorname{tr}B_m\asymp m^{1/2}\to\infty.
\]
These are matrix arrays, not realized log-concave counterexamples. They establish the precise failure of the proposed scalar-slack-only moment upgrade. A viable uniform proof must exploit the actual Hessian compatibility and covariance normalization before discarding such directions. We did not prove that estimate.

**Cone route.** For \(K\) centered with covariance \(I_n\), let \(T\sim\Gamma(n+1,1)\), independent of uniform \(X\in K\). The source law ((TX,T)) has block covariance \(((n+1)(n+2)I_n,n+1)\), entropy gap \(n\log(L_{\Delta_n}/L_K)\), and explicit affine whitening. H53 therefore proves a W2 estimate for its whitened cone law in dimension (n+1), with the corresponding dimension-dependent exponent. This consequence alone is a routine transfer and not a separate result.

A direct section construction can be examined as follows. In physical cone coordinates, the map \((y,t)\mapsto y/t\) is Lipschitz on \(a\le t\le b, |y|\le R\), with constants at most \(1/a+R/a^2\). The gamma tail below \(a\) is at most \(a^{n+1}/(n+1)!\), and upper tails are explicit. But an orthogonal exponential approximant in whitened coordinates need not have its affine cone vertex at the physical origin or its generating rays uniformly transverse to the height direction. Its restriction to a height band does not automatically correspond to uniform measure on one compatible simplex. Controlling the apex and ray heights quantitatively from transport error, before using division by \(t\), is the unpaid geometric estimate. Exact support equality in the source cannot replace it. No condition-number-free or Hausdorff/Banach–Mazur transfer is asserted.

**Information route.** The explicit asymmetric Laplace example closes the proposed directed-KL screen. A revised target using a support-compatible reference family, smoothed extremizers, or a weaker information distance would require a new statement and new estimates. It is not smuggled into H53.

## 10. Reproduction

From the project root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i53_sharp_entropy_stability_discovery/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i53_sharp_entropy_stability_discovery/verify.py
```

The diagnostics contain 4,170 assertions. Both commands are read-only and print results. The stored deterministic diagnostic output is compared byte-for-byte by the verifier. The verifier also checks immutable pinned Git blobs against the frozen complete tree, selected frozen inputs, primary response hashes, source passage slices, the full corpus inventory and search line multisets, and the artifact seal. Live drift of the four shared ledgers is separately reported. The first local verification exposed a path-order comparison in the corpus inventory (the sets and all file hashes agreed); the verifier now sorts both path lists. Its failed output and original assembly seal are retained in `verification-initial.json` and `seal-initial.json`. The corpus search comparisons already used line multisets and were unchanged. The optional literature-fetch script is a provenance aid, not part of offline reproduction and not a promise that future network responses reproduce their captured bytes.
