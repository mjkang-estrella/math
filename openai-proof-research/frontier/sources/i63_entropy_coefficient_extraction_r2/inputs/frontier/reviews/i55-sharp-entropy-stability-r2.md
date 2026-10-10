# I55 independent original-proof audit of I53

Date: 2026-10-09. **H53: PASS ORIGINAL WITHOUT REPAIRS**, conditional on the stipulated pinned OpenAI statements **and proof operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. This is a fresh review of the frozen original [I53 report](../iterations/i53-sharp-entropy-stability-discovery.md), not an author continuation. The parent's earlier checks and the author's finite diagnostics are not premises of this verdict.

Separate verdicts: **Lemma A, B53, the one-dimensional exponent (1/2), and the directed-KL counterexample all PASS ORIGINAL WITHOUT REPAIRS.** The cone-law consequence and the explicitly limited matrix/compatibility diagnostics pass in their stated scopes. The dimension-uniform target U and Banach–Mazur simplex target S remain **unproved and unrefuted** here. I make no acceptance, finding-count, substantiality, or worldwide-priority decision.

No mathematical repair is needed. One **numerical-reporting qualification** is needed: I53 §8 calls its numerical law distances upper bounds to the orbit distance. Exact fixed-orientation distances are upper bounds, but its unvalidated Simpson values are approximations to those bounds, not certified bounds themselves. This does not enter either theorem's proof. The expansions below make the original estimates independently checkable; they do not change its hypotheses, exponent, constants in Lemma A, or proof mechanism. In particular, they do not replace the target by a smooth or bounded-support version.

## Frozen scope and source audit

The exact delegated brief, including the original author assignment and parent observations, is in [brief.txt](../sources/i55_sharp_entropy_stability_r2/brief.txt). Ten inputs are frozen in `inputs.json`, including AGENTS.md, all four current ledgers, the complete tree, the catalogue, and the original report. `author-files.json` records the SHA256 of all 83 existing author artifacts, including both seals and both verification records. The initial failure is preserved, not overwritten: `verification-initial.json` reports **FAIL: full corpus path inventory**. The recorded cause is Path-order versus string-order comparison, and the corrected verifier sorts both path lists. No mathematical proof correction is hidden in that history. I55 freezes those history records separately without recursively copying the old evidence archive.

I independently inventoried all **13,223 tree entries / 749 manuscript directories** and all **9,340 ignored corpus files**, using `rg --files --no-ignore`. Each corpus file is hashed. Two independent whole-corpus searches are frozen as **sorted line multisets**, retaining repetitions: compatibility (14 lines) and broader companions (1,193 lines). The broad word “isotropic” has many unrelated algebraic and Fourier-analysis hits; inventory/search coverage is not a claim to have read every manuscript. The authoritative complete tree, not the truncated root cache or historical 719 count, determines coverage.

I read the original report completely and the actual entropy manuscript's introduction, transport, matrix, scalar, certificate, approximation, rigidity, and geometry proofs. I also read the general-Mahler introduction, projection/normalization section, linear-field/equality section, and functional consequences. The 15 pinned blobs used by I53 are verified against the complete tree; source hashes, labels, ranges, and passage hashes are recorded in the evidence. Relevant inherited operations are:

* `transport.tex`, `tr:normalization`: a **symmetric positive definite** target normalization P, with (E q^{-1}(DF)=0). Its proof explicitly contains the spectral-measure Jensen and first-chaos lower bound.
* `matrix.tex`, `mat:strict-remainder`: (2\delta\ge \|Y\|_2^2/500+\sum_i\omega(\lambda_i(B))/1000). Thus the original constants 1000 and 2000 are correct.
* `matrix.tex`, the final proof: the two-eigenvalue bound consumes the transport separation surplus (\mathcal C). H53 does not reuse that surplus as an extra commutator estimate.
* `rigidity.tex`, `eq:coefficient-symmetry`, `eq:coefficients-commute`, and `lem:spectral-lipschitz`: the exact Taylor identities and global forward Frobenius Lipschitz estimate are already source operations. H53 pays for their approximate use.
* `approximation.tex`, `geo:common-tail` and its final dominated-convergence argument: convergence weighted by (1+|x|^2), and entropy convergence, follow from the proof even though the lemma statement lists unweighted (L^1), moments, and entropy separately.
* General Mahler `06-linear-equality.tex`: diagonal support of its spectral measure gives exact commutation. Its different defect and layer measures are not controlled by this entropy gap. `09-consequences.tex` explicitly distinguishes the auxiliary-dimensional functional limit from equality transfer.

These sources are stipulated premises. The review checks their scope and the new deductions, not their upstream truth.

## Exact theorem being passed

Let (Z_m=(E_1-1,\ldots,E_m-1)), with independent mean-one exponentials. For every fixed integer (m\ge2), there is a finite dimension-only (C_m) such that every log-concave probability density with mean a and positive covariance C obeys
\[
 \inf_{O\in O(m)}W_2\!\left(\mathcal L(C^{-1/2}(X-a)),\mathcal L(OZ_m)\right)
 \le C_m\left(h(f)-m-\tfrac12\log\det C\right)^{1/(m+6)}.
\]
For (m=1), the exponent is (1/2). Constants need not be sharp, practical, or uniform in dimension. No support, boundary, Hessian, or smoothness restriction survives in the conclusion. Whitening an affine exponential product gives an orthogonal exponential product since (C^{-1/2}M) is orthogonal when (C=MM^T); the reference class is exactly the whole equality orbit.

## 1. From retained slack to approximate cubic equations

Write (A=L+Y), (L(x)=\sum_r x_rX_r), (B=\sum_rX_r^2), as in I53. For (0\le\lambda\le1/2), the author's lower bound (117/320000) for (\omega) is valid. For (\lambda\ge2), the bound (117\sqrt\lambda/172000) follows from
\((\lambda-1)^2\ge\lambda^2/4\), (37+3\lambda\le43\lambda/2), and (\min(13/100,32/(25\sqrt\lambda))\ge13/(100\sqrt\lambda)). Both bounds exceed (10^{-4}). Since (2000\delta<10^{-4}) when (\delta<5\cdot10^{-8}), every eigenvalue lies in ([1/2,2]). There,
\[
 \omega(\lambda)\ge(117/86000)(\lambda-1)^2>10^{-3}(\lambda-1)^2.
\]
Consequently (\|B-I\|_F\le\sqrt{2\cdot10^6\delta}), (\|X\|_F^2=\operatorname{tr}B\le2m), and
\(\|q(L)-DF\|_{L^2(\gamma)}\le e=\sqrt{1000\delta}). No eigenvalue tail is discarded without payment.

For the curl calculation, put (E=q(L)-DF), and denote the standard Gaussian density by g. On (B_R),
\[
 \|E\|_{L^2(dx;B_R)}\le(2\pi)^{m/4}e^{R^2/4}\,e.
\]
This is the entire Gaussian-to-Lebesgue loss at the fixed origin. It depends only on m and the fixed R, not on a shrinking h or on the target density. For a component of (K=\operatorname{curl}q(L)=\operatorname{curl}E), distributional integration by parts transfers one derivative to (\rho_h), and two derivatives for (DK*\rho_h). The scaling identity
\(\|D^j\rho_h\|_{L^2(dx)}=h^{-m/2-j}\|D^j\rho\|_2\)
gives exactly
\[
 |K*\rho_h(0)|\le C_meh^{-m/2-1},\qquad
 |DK*\rho_h(0)|\le C_meh^{-m/2-2}.
\]
Commutation of weak derivatives of each (F_i) suffices; differentiability of the error E is never assumed.

On (B_{2R}), (\|L\|_{\rm op}\le\sqrt{2m}|x|\le1/5). Smooth spectral functional calculus bounds derivatives of (q(L)) through order three on the compact coefficient ball. Hence K and DK differ from their mollified values by at most (C_mh). There is no singularity from repeated eigenvalues, because the matrix function itself is smooth. Choosing
\[
 h=e^{2/(m+6)}
\]
balances (eh^{-m/2-2}=h); the zero-jet term is smaller for (e\le1). Thus the first two curl jets are (O_m(e^{2/(m+6)})=O_m(\delta^{1/(m+6)})). The condition (h\le R) is included in the eventual dimension-only cutoff. For (e=0), the smooth curl vanishes distributionally and hence identically, so no division by h is required.

The exact jets have the author's signs and factor (b=q''(0)/2):
\[
 K_{\cdot rs}(0)=q'(0)(X_re_s-X_se_r),
\]
\[
 \partial_tK_{\cdot rs}(0)=b\{(X_rX_t+X_tX_r)e_s-(X_sX_t+X_tX_s)e_r\}.
\]
Set (S_{rs}=X_re_s-X_se_r). Since (X_te_s=X_se_t+S_{ts}), the expression in braces is
\[
 [X_r,X_s]e_t+X_rS_{ts}-X_sS_{tr}+X_tS_{rs}.
\]
Both scalar jet coefficients are strictly positive by the source's explicit values. Summing all vector and matrix entries costs only a dimension-only constant and gives (3.4). Independent rational polynomial-coefficient checks test repeated and distinct differentiation indices; they corroborate this algebra but are not its proof.

For clarity, full symmetrization here is
\[
 T_{ijr}=\tfrac13\{(X_r)_{ij}+(X_i)_{jr}+(X_j)_{ri}\}.
\]
The two differences from ((X_r)_{ij}) are entries of S after permutations, so (\|T-X\|_F\le(2/3)\|S\|_F). If (D=T-X), K denotes (\|X\|_F\le\sqrt{2m}), and (\epsilon=\|D\|_F), direct product estimates give
\[
 \left\|\sum T_r^2-\sum X_r^2\right\|_F\le(2K+\epsilon)\epsilon,
\]
\[
 \|([T_r,T_s]-[X_r,X_s])_{rs}\|_F\le4K\epsilon+2\epsilon^2.
\]
This proves (3.5) in the specified unnormalized array norms. There is no unaccounted matrix-count limit or sign change.

## 2. Lemma A, including threshold and constant

Take a fully symmetric cubic tensor T in dimension m with
\[
 \eta=\max\{\|\sum T_r^2-I\|_{\rm op},\ \|([T_r,T_s])_{rs}\|_F\}
 \le10^{-6}m^{-4}.
\]
At a recursive step in dimension (1\le d\le m), assume (\eta_d\le2\eta). This is a bootstrap hypothesis verified below, not an unproved restriction on the intermediate tensors.

Let v be a **global** spherical maximizer of the odd cubic p and (c=p(v)=\max|p|>0). Nonzeroness follows from (\|T\|_F^2\ge d(1-\eta_d)>0). Polarization gives 
\(|T(e_i,e_j,e_k)|\le(8\cdot27/48)c=(9/2)c), hence
\[
 c\ge\frac{\sqrt{1-\eta_d}}{(9/2)d}\ge\frac1{10d}.
\]
The bound uses all (d^3) ordered entries, so the dimension power is correct.

The first variation gives (T_vv=cv). The second derivative of (p(\cos t\,v+\sin t\,w)) at zero, for unit (w\perp v), is (6T(v,w,w)-3c\le0). Thus (T_v=\operatorname{diag}(c,H)), with (H\preceq(c/2)I). Stationarity alone would not give this inequality; the negative control (p=x_1^3+x_2^3), (v=(1,1)/\sqrt2), has complementary eigenvalue c and violates it.

Full symmetry gives (T_wv=T_vw), and therefore
\[
 [T_v,T_w]v=T_v^2w-T_w(cv)=(T_v^2-cT_v)w.
\]
Cauchy–Schwarz over the two coefficient indices yields
\(\|[T_v,T_w]\|_F\le\eta_d|v||w|\).
Consequently (\|H^2-cH\|_{\rm op}\le\eta_d). For every eigenvalue (\lambda\le c/2), including negative ones,
\[
 |\lambda|\le2\eta_d/c,
 \quad \|H\|_F^2\le4d\eta_d^2/c^2\le400d^3\eta_d^2.
\]
Symmetry also gives
\[
 v^T\Big(\sum_rT_r^2\Big)v=\sum_r|T_rv|^2=\|T_v\|_F^2=c^2+\|H\|_F^2.
\]
At the largest allowed residual,
\[
 c^2\ge1-\eta_d-400d^3\eta_d^2
 \ge1-2\cdot10^{-6}-1.6\cdot10^{-9}>1/4.
\]
Thus (c\ge1/2), and substitution gives exactly the original bounds
\[
 \|H\|_F^2\le16d\eta_d^2,\qquad
 |c-1|\le\eta_d+16d\eta_d^2\le2\eta_d.
\]
The last inequality follows from (16d\eta_d\le32\cdot10^{-6}m^{-3}<1).

Now rotate **all three indices** so that v is the first coordinate and restrict to its orthogonal complement. The other slices have blocks
\(T_a=\left(\begin{smallmatrix}0&h_a^T\\h_a&T'_a\end{smallmatrix}\right)), with (h_a=He_a). Matrix multiplication gives
\[
 \Big(\sum_rT_r^2\Big)_{v^\perp}=\sum_a(T'_a)^2+2H^2,
\]
\[
 [T_a,T_b]_{v^\perp}=[T'_a,T'_b]+h_ah_b^T-h_bh_a^T.
\]
One H-squared term comes from (T_v^2), the other from summing (h_ah_a^T). The sign of the commutator correction agrees with the original. Its array norm is at most (2\|H\|_F^2), because each of the two outer-product arrays has norm (\|H\|_F^2). Compression contracts Frobenius norm. Orthogonal rotation preserves the full array norm: the two coefficient indices undergo an orthogonal tensor-product action, and each matrix undergoes orthogonal conjugation. Thus
\[
 \eta(T')\le\eta_d+32d\eta_d^2\le\eta_d+64m\eta_d^2.
\]
This is quadratic growth, not linear growth hidden in a constant.

If all previous residuals are at most (2\eta), each increase is at most (256m\eta^2). At most m increases give
\[
 \eta_d\le\eta+256m^2\eta^2\le2\eta,
 \qquad256m^2\eta\le256\cdot10^{-6}m^{-2}<1.
\]
This closes the bootstrap, including dimension one. If (\eta=0), every bound gives zero: (H=0,c=1), and the recursion constructs an exact normalized orthogonal decomposition.

The three placements of (v\otimes H) have disjoint index supports and squared norm (3\|H\|_F^2). Entries removed at different steps are disjoint when classified by their earliest removed direction. Diagonal coefficient errors are disjoint from all mixed entries. Therefore
\[
 \left\|T-\sum_ju_j^{\otimes3}\right\|_F^2
 \le\sum_{d=1}^m(192d+16)\eta^2
 =(96m^2+112m)\eta^2
 \le208m^2\eta^2<(20m\eta)^2.
\]
This verifies the **original threshold (10^{-6}m^{-4}) and constant (20m)**. No alteration of either is needed. Signs are absorbed in the odd-order basis tensors.

## 3. Construction B and its separate exponent

I independently checked the real spectral-partition induction. For (0<z\le1), put (h=\sqrt z). In the eigenbasis of the first contraction, maximal chains of adjacent gaps at most h have diameter at most dh; different clusters have separation greater than h. Choosing any cluster eigenvalue as its replacement scalar preserves contraction and incurs Frobenius error at most (d^{3/2}h).

For each other matrix, erase cross-cluster entries. The squared deleted norm is at most (z^2/h^2), by the entrywise commutator identity. Block compression preserves operator norm at most one. If (widehat H_i) are the block-truncated contractions and (E_i=H_i-widehat H_i), then
\[
 \|[\widehat H_i,\widehat H_j]-[H_i,H_j]\|_F
 \le2\|E_i\|_F+2\|E_j\|_F\le4z/h.
\]
One can expand with one original factor and one truncated factor, so no unbounded product term is omitted. Compression to any block only decreases this bound. The induction input is at most (z+4\sqrt z\le5\sqrt z).

Let (a_k=2^{1-k}). Constants can be chosen monotonically in d with (C_{d,1}=0), and, for (k\ge2), at least
\[
 d^{3/2}+1+\sqrt d\,5^{a_{k-1}}\max_{s\le d}C_{s,k-1},
 \quad\text{and}\quad\sqrt d\,25^{a_k}.
\]
For (5\sqrt z\le1), the first expression pays for truncation and the Euclidean sum over at most d blocks; ((\sqrt z)^{a_{k-1}}=z^{a_k}). For (5\sqrt z>1), all-zero approximants work using the second expression. For (z=0), exact simultaneous orthogonal diagonalization supplies zero error, the usual endpoint implicit in the original argument. This is an explicit validation of its constant absorption, not a repair.

Apply this to (X_r/\sqrt2), and rescale the approximants by (\sqrt2). After a common diagonalizing U, rotate the coefficient index as well. If (\widetilde D_i=\operatorname{diag}(d_{i1},\ldots,d_{im})), the symmetry error bounds the vector
\(d_{ij}e_j-d_{ji}e_i). For (i\ne j) its components are orthogonal, so both cross entries are small. The j-th diagonal entry of (\sum_i\widetilde D_i^2) is (\sum_id_{ij}^2), close to 1. Thus (d_{jj}^2) is close to 1 after accounting for all cross entries, and rounding to a sign has linear error, using (||d_{jj}|-1|\le|d_{jj}^2-1|). This leaves only the normalized coordinate cubic terms. The original error (O_m(\nu^{1/2^{m-1}})) follows, yielding
\[
 \boxed{d_m(f)\le C_m\delta^{1/((m+6)2^{m-1})}.}
\]
There is no dimension-free matrix-count assertion. B53 is independently complete even if Lemma A is removed.

## 4. Reconstruction, covariance orientation, and unrestricted densities

For the orthonormal basis returned by A, let
\[
 L^*(x)=\sum_j\langle u_j,x\rangle u_ju_j^T,
 \qquad H(x)=\sum_ju_j(t(\langle u_j,x\rangle)-1).
\]
The source transport identity gives (DH=q(L^*)), (EH=0), and (\operatorname{Cov}H=I). Orthogonal Gaussian coordinates are independent, so the law is exactly that of (OZ_m). Gaussian coefficient orthogonality identifies (\|L-L^*\|_2) with the tensor-array error.

The global **forward** Lipschitz bound yields
\[
 \|DF-DH\|_2\le\|Y\|_2+\|L-L^*\|_2.
\]
Both maps are in Gaussian (H^1): for F this follows from the individual smooth transport bounds; H has exponential second moments of the required order and (q(s)\le q(0)+|s|). Poincaré on their centered difference gives (r=\|F-H\|_2\le C_m\delta^{1/(m+6)}). The same step preserves B53's weaker exponent. No inverse-q bound appears.

For every unit v, the expected spectral measure of A at v is a probability measure with mean (v^TEAv=0). Convexity of q gives (E DF\succeq q(0)I). Projection of F on first Gaussian chaos gives
\[
 P^2=\operatorname{Cov}F\succeq(E DF)(E DF)^T=(E DF)^2\succeq q(0)^2I.
\]
The last step squares a single positive symmetric matrix using its spectral theorem. It is not general operator monotonicity of squaring. Since P is the positive definite normalizer, (\|P^{-1}\|_{\rm op}\le q(0)^{-1}), uniformly in the density and approximating Hessian constants.

For the remaining covariance estimate, put (V=P^{-1}F) and (M=E[VH^T]). Isotropy and Cauchy–Schwarz give (\|M\|_{\rm op}\le1). Since P is symmetric positive definite,
\[
 E\langle F,H\rangle=\operatorname{tr}(PM),\qquad
 \operatorname{tr}(PM)\le\operatorname{tr}P.
\]
The trace identity is unaffected by replacing M by its transpose because P is symmetric; the chosen orientation agrees with the original. Diagonalizing P proves the inequality even though M need not be symmetric. Thus
\[
 r^2\ge\operatorname{tr}P^2+m-2\operatorname{tr}P=\|P-I\|_F^2.
\]
Finally,
\[
 \|P^{-1}F-H\|_2
 \le\|P^{-1}\|_{\rm op}(r+\|(I-P)H\|_2)
 \le2q(0)^{-1}r.
\]
This is a coupling for the original centered isotropic density and the full equality orbit. It removes normalization distortion without an assumed condition-number bound.

All smallness thresholds depend only on m: the spectral cutoff, (h\le R), and the Lemma A residual threshold. Their finite minimum is positive. For gaps above that cutoff, independent centered isotropic coupling costs at most (\sqrt{2m}). The original prescription (C_m\ge\sqrt{2m}\delta_m^{-1/(m+6)}) therefore makes the result global. Finite derivative suprema of the known smooth matrix function specify constants; no unexamined compactness modulus is used.

For a nonsmooth density, the source supplies (\int(1+|x|^2)|f_j-f|\to0) and entropy convergence. Couple the common density part identically and the equal-mass residual parts independently. Their cost is at most twice their summed residual second moments, tending to zero. Means and covariances converge; positive definiteness of C gives convergence of (C_j^{-1/2}). The additional affine coupling cost tends to zero by bounded second moments, so the whitened laws converge in (W_2). Their entropy gaps also converge. Distance to any fixed subset of a metric space is 1-Lipschitz; hence distance to the whole orthogonal orbit passes to the limit without selecting or taking limits of orientations. Affine whitening preserves each approximant's finite positive Hessian bounds. This closes the original unrestricted scope.

In dimension one, (B=X_1^2) and the scalar retained slack give (|X_1^2-1|\le C\sqrt\delta). Therefore (X_1) is (O(\sqrt\delta)) from one of the two signs. The Y error is already of that size. Reconstruction, normalization, large-gap extension, and approximation give the claimed (1/2) exponent. No curl estimate is used. The zero-gap endpoint is also covered by exact source equality or by the zero-error argument above.

## 5. Counterexample and remaining diagnostics

For the original asymmetric Laplace family, direct integration gives mass 1, mean (1-a), second moment (2(1-a+a^2)), variance (1+a^2), and entropy (1+\log(1+a)). Its potential has slope (-1/a) on the left and 1 on the right, so it is convex. Standardization preserves full support and gives gap
\(\log(1+a)-\tfrac12\log(1+a^2)\to0).
Each one-sided exponential reference vanishes on an open half-line of positive mass. Hence both values (D(f_a\Vert\pm Z_1)) are infinite. In higher dimensions the product standardized law is positive everywhere, while any rotated orthant reference has an open complement. This proves the whole-orbit directed-KL failure. It is not a failure of reverse-directed KL or W2 stability.

The diagnostic (X_1=I_2,X_2=0) has B=I and zero commutators but fails coefficient symmetry. This correctly blocks using simultaneous diagonalization alone. For an affine scalar q, a symmetric cubic field can be a Jacobian despite noncommuting slices, confirming why the nonzero second jet matters. The blowup of (1/q'(-R)) rules out a global inverse-q Lipschitz shortcut. From (\omega(\lambda)\asymp\sqrt\lambda), the matrix array (B_m=\operatorname{diag}(m^{3/2},1,\ldots,1)) has normalized weight tending to zero while normalized trace diverges. This is only an obstruction to upgrading the scalar weight; no realized log-concave counterexample to U is produced.

The cone calculation also agrees with the source: for (T\sim\Gamma(n+1,1)) independent of centered isotropic uniform X on K, the covariance of ((TX,T)) is \(\operatorname{diag}((n+1)(n+2)I_n,n+1)\), and its gap is exactly (n\log(L_{\Delta_n}/L_K)). H53 therefore controls the whitened cone law. Its conversion to Banach–Mazur proximity would still require quantitative alignment of the cone vertex and positive ray heights. The source's exact support argument does not supply that estimate. No separate theorem S or additional finding follows here.

The new standard-library diagnostics perform exact rational tensor/block/rotation/jet/partition/covariance checks, threshold checks, and negative controls. Two midpoint-quantile resolutions illustrate the asymmetric Laplace distances to both one-dimensional orientations. They are **unvalidated numerical quadrature**, not rigorous upper bounds or error-certified distances. The same qualification applies to the author's Simpson quadrature on a truncated logistic interval: two-resolution agreement is not an error certificate. The smallest reporting correction, made here only, is “numerical approximations to fixed-orientation distances, whose exact values bound the orbit distance.” The exact bound follows immediately because the orbit infimum is at most the cost for a particular orientation; it does not bound numerical integration error. The author's diagnostic output is independently replayed for integrity, not substituted for the analytic arguments above.

## 6. Primary literature fact checks and attribution limits

Fresh primary response bytes, UTC timestamps, hashes, status codes, current version pages, and four versioned PDFs are retained in `literature/manifest.json`; exact text extraction is replayed offline. Current accessible arXiv versions are BDHR **1512.08031v1**, Auddy–Yuan **2007.09024v2**, Mu–Hsu–Goldfarb **1705.10404v1**, Filonov–Kachkovskiy **1008.4002v2**, Fradelizi–Marín Sola **2406.07406v1**, Melbourne–Nayar–Roberto **2309.01840v2**, Kipp **2411.08722v2**, and Rademacher **1404.5662v2**. These are accessible-version observations, not a claim about all possible journal updates.

* [BDHR, §3.1, Lemma 11 and Proposition 12](https://arxiv.org/abs/1512.08031v1): associativity characterizes exact symmetric orthogonal decomposability. I read the simple-ideal argument. It supplies no stated approximate residual estimate with Lemma A's threshold and constant.
* [Auddy–Yuan, Theorems 2.4 and 3.1](https://arxiv.org/abs/2007.09024v2): the former compares two already orthogonally decomposable tensors; the latter rounds an existing factorization whose factor matrices are near isometries, by polar decomposition. These inputs must not be replaced silently by a commutator residual. I read the factorization hypotheses and the polar-rounding proof passage.
* [Mu–Hsu–Goldfarb, Theorems 2.2 and 3.1, Lemma 3.2](https://arxiv.org/abs/1705.10404v1): best rank-one approximation, cubic optimization, and controlled deflation are prior techniques. Their input is a tensor already close to an orthogonally decomposable one. The article's journal reference is **2015**, although its arXiv submission is 2017; no 2017 discovery date is implied here.
* [Filonov–Kachkovskiy, Theorems 2–3 and their proofs](https://arxiv.org/abs/1008.4002v2): the norm is normalized Hilbert–Schmidt. The two-matrix power is (1/4), and the many-matrix iteration has a matrix-count-dependent power. I53's real block proof is self-contained and permits dimension-dependent constants; it does not claim that external result is uniform when the matrix count grows.
* [Fradelizi–Marín Sola, Conjecture 3(iii), Proposition 5.2, Lemma 5.2](https://arxiv.org/abs/2406.07406v1): the actual cone identities and auxiliary-dimensional limit were inspected. They do not state a quantitative reverse section transfer. A fresh attempt at the author's PDF again failed TLS certificate verification; that failure and the original failure remain recorded. The newer journal proof was not obtained, so the author report's version limitation remains.
* [Melbourne–Nayar–Roberto](https://arxiv.org/abs/2309.01840v2): the cached author-hosted published text, Theorem 1.1 and §§3.1–3.3, establishes the scalar sharp inequality through rearrangement and two-piece log-affine reduction. H53 does not assume an unstated quantitative stability theorem from it.
* [Rademacher](https://arxiv.org/abs/1404.5662v2), Theorems 1–2, and [Kipp](https://arxiv.org/abs/2411.08722v2), Theorem 1.5 and proof: these concern structural restrictions at local/global maximizers. Kipp's moment/covariance kernel and second-variation argument was inspected. Neither cited statement provides the global cone-section estimate left open in I53.

No external paper is promoted to a true premise merely by being recent, and no external tensor perturbation theorem is needed for the proof verdict. This bounded primary-source audit checks attribution and logical inputs. The separate contribution review must assess substantiality and possible other antecedents. No MathDB score or priority claim is assigned.

## Objections and disposition

`objections.json` freezes each objection, response, and verdict. The principal objections were weak-versus-classical differentiation; Gaussian small-ball loss; jet signs and repeated indices; full symmetrization; a possibly nonmaximizing cubic direction; invalid squaring order; missing coefficient rotation; linear versus quadratic deflation growth; B's block aggregation and zero endpoint; covariance cross-moment orientation; degenerating Hessian constants; and moving supports. Every one is resolved within the original written mechanism as detailed above. There is no rejected original theorem followed by a repaired substitute.

The finite-record caveats are preserved: I53's initial inventory-order failure, its original assembly seal, primary TLS and HTTP failures, and mutable-ledger drift. My own verifier treats only the four named shared ledgers as mutable. All other input and author hashes are immutable assertions; search comparisons preserve multiplicity. No author, prior, or shared file was edited, and no staging, commit, publication, or agent spawning was performed.

## Reproduction

From the project root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i55_sharp_entropy_stability_r2/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i55_sharp_entropy_stability_r2/verify.py
```

Both commands are read-only and print their results. The verifier replays the independent diagnostics, the author's read-only verifier, complete corpus hashes and line multisets, source Git blobs, passage slices, PDF extractions, frozen inputs, and I55 artifact seal. It reports shared-ledger drift separately. The capture/fetch scripts are one-time provenance tools and are not needed for offline replay. Evidence PASS certifies these records and finite checks; the mathematical PASS is the analytic audit written above.
