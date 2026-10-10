# I56 independent contribution audit: sharp entropy stability

**Verdict: TECHNICAL ONLY, at the full H53 statement.** This is a fresh contribution review, not continuation of I53 and not a finding-count decision. It does not claim an exact published duplicate or reject the original proof. I55 owns the independent original-proof verdict. All pinned OpenAI statements **and proof operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises throughout.

The parent's specific objection is sustained by a complete reduction below. The normalized symmetric odeco equations have exactly the orthogonal-orbit tangent kernel. Their derivative has singular value **2 on the entire normal space**, for the combined Frobenius residual specified below. A nearest-orbit Taylor argument therefore gives a linear equation-residual error bound, uniformly in a neighborhood of the orbit. Elementary bounded-set compactness supplies entry into that neighborhood at each fixed dimension. The source's existing slack, exact Taylor compatibility, forward functional calculus and Gaussian reconstruction then give **the same exponent and unrestricted density scope as H53**, without Lemma A's cubic maximization or recursive deflation. This is more specific than a generic Łojasiewicz objection.

There is also unusually direct prior art for the allegedly missing algebraic interface: Biaggi–Draisma–Seynnaeve, published Proposition 4.1, explicitly computes the tangent space at \(\sum e_i^{\otimes3}\); its coordinates are precisely the off-diagonal conditions used here. That paper attributes the argument to Robeva; Robeva's Lemma 3.7 proof also computes the Jacobian rank. Neither paper is misrepresented as stating H53 or the normalized residual bound. The added normalization, Euclidean estimate and full analytic reduction are proved here.

## 1. Scope, frozen inputs and comparison standard

For \(Z_m=(E_1-1,\ldots,E_m-1)\), with independent mean-one exponentials, the audited assertion is
\[
 \inf_{O\in O(m)}W_2\bigl(\mathcal L(C^{-1/2}(X-a)),\mathcal L(OZ_m)\bigr)
 \le C_m\bigl(h(f)-m-\tfrac12\log\det C\bigr)^{1/(m+6)},\qquad m\ge2.
 \tag{H53}
\]
Here \(f\) is any log-concave probability density with mean \(a\) and positive covariance \(C\); \(C_m<\infty\) depends only on \(m\). In dimension one the proposed exponent is \(1/2\). No support, smoothness or Hessian restrictions survive in the conclusion. There is no specified numerical \(C_m\), dimension-uniform rate, sharp exponent, KL conclusion or Banach–Mazur simplex conclusion.

The exact review assignment, including the original author assignment, is frozen in [brief.txt](../sources/i56_sharp_entropy_stability_novelty/brief.txt). [inputs.json](../sources/i56_sharp_entropy_stability_novelty/inputs.json) freezes the original report, instructions, complete tree, current ledgers, original objections, seals and verification history. [author-evidence-hashes.json](../sources/i56_sharp_entropy_stability_novelty/author-evidence-hashes.json) references all other author evidence without recursively duplicating its archive. No author's claim of novelty is taken as an established premise.

The four mutable ledgers are `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md` and `frontier/iterations/README.md`. Their capture records the seven accepted findings and pending I55/I56 review; subsequent drift is informational. This child neither updates those ledgers nor decides the count. The original I53 inventory-order FAIL, initial seal, corrected seal and corrected PASS are retained separately. The I56 read-only replay independently reproduces the original corrected verifier's 81 artifacts, 11 inputs, 15 pins, 29 passages, 22 primary requests, 10 PDF replays, 4,170 assertions and 9,340 corpus files, with four informational author-era ledger drifts.

The standard is contribution beyond already accepted proof operations and ordinary finite-dimensional regularity, not the absence of a search hit. An original and correct construction can be useful while the final theorem remains technical at this standard.

## 2. The transverse estimate, with every hypothesis paid

All norms in this section are unnormalized Frobenius norms. Let
\[
 V=\operatorname{Sym}^3(\mathbb R^m),\quad D=\sum_{i=1}^m e_i^{\otimes3},\quad
 \mathcal M=\{U^{\otimes3}D:U\in O(m)\}.
\]
For \(T\in V\), write \((T_r)_{ab}=T_{abr}\), and define the polynomial map
\[
 \mathcal R(T)=\left(N(T),\ (A_{rs}(T))_{r,s=1}^m\right),\qquad
 N(T)=\sum_rT_r^2-I,\quad A_{rs}(T)=[T_r,T_s].
\]
The norm on the codomain is
\[
 R(T)^2=\|N(T)\|_F^2+\sum_{r,s}\|A_{rs}(T)\|_F^2.
 \tag{2.1}
\]
Both coefficient indices of the commutator array are included, as are both matrix indices. If \(\eta(T)\) is I53's operator-normalization/max residual, then
\[
 \eta(T)\le R(T)\le\sqrt{m+1}\,\eta(T).
 \tag{2.2}
\]
This explicit norm conversion precludes a dimension-free interpretation.

### 2.1 Exact zero set and orthogonal invariance

\(\mathcal R^{-1}(0)=\mathcal M\) over the **real** symmetric tensors. Indeed, the symmetric slices commute, hence have a common real orthogonal diagonalization. Rotate all three tensor indices by that orthogonal matrix. The transformed slices remain diagonal. Full symmetry then kills every coefficient except \(T_{iii}\). Normalization makes \(T_{iii}^2=1\), and each sign is absorbed into the corresponding basis vector because the tensor order is odd. The converse is immediate.

This is already the simultaneous-diagonalization operation in the pinned `rigidity.tex`, as well as a special normalized instance of Boralevi–Draisma–Horobeţ–Robeva's associativity characterization. No complex-variety statement is required. In particular, complex non-odeco components discussed by Biaggi et al. are not an obstruction to this real zero set.

For \(S=U^{\otimes3}T\),
\[
 S_r=U\left(\sum_aU_{ra}T_a\right)U^T,
\]
so \(N(S)=UN(T)U^T\) and
\[
 A_{rs}(S)=U\left(\sum_{a,b}U_{ra}U_{sb}A_{ab}(T)\right)U^T.
\]
Thus the residual norm, tensor norm and distance to \(\mathcal M\) are invariant. The orbit is compact since \(O(m)\) is compact.

### 2.2 Derivative and its entire kernel

For a symmetric perturbation \(E\), differentiating at \(D\), whose slices are \(D_r=e_re_r^T\), gives
\[
 (dN_D E)_{ab}=E_{abb}+E_{aab},
 \tag{2.3}
\]
\[
 (dA_D E)_{rs,ab}
  =(\mathbf1_{a=r}-\mathbf1_{b=r})E_{abs}
   +(\mathbf1_{b=s}-\mathbf1_{a=s})E_{abr}.
 \tag{2.4}
\]
For distinct \(r,s,t\), entry \((a,b)=(r,t)\) of \(dA_{rs}\) is \(E_{rst}\). Entry \((r,s)\) is \(E_{rss}+E_{rrs}\). Finally the diagonal of \(dN\) is \(2E_{aaa}\). Consequently the kernel is exactly
\[
 E_{iii}=0,\qquad E_{iij}+E_{ijj}=0\ (i<j),\qquad
 E_{ijk}=0\ (i,j,k\text{ distinct}).
 \tag{2.5}
\]
For a skew-symmetric matrix \(K\), the derivative of \((e^{tK})^{\otimes3}D\) at zero has
\[
 E_{iij}=K_{ji},\qquad E_{ijj}=K_{ij}=-K_{ji},
\]
and all other types vanish. Thus (2.5) is precisely the orbit tangent space; there are no additional infinitesimal directions. This also treats \(m=1,2\): the nonexistent triple-index conditions are simply absent.

The associativity part of this calculation appears in [Biaggi–Draisma–Seynnaeve, Proposition 4.1, p. 10](https://rendiconti.dmi.units.it/volumi/54/017.pdf), equations (3)–(4) (arXiv v1 calls it Proposition 4.2.1). The normalization removes its \(m\) diagonal/amplitude directions. Their §4.1 credits the argument to [Robeva, Lemma 3.7](https://arxiv.org/abs/1409.6685). The cited complex coordinate calculations are valid over the reals as polynomial identities; the proof above establishes the real statement directly.

### 2.3 Exact coercivity, not just a rank assertion

Write
\[
 d_i=E_{iii},\quad a_{ij}=E_{iij},\quad b_{ij}=E_{ijj},\quad
 c_{ijk}=E_{ijk}\quad(i<j<k).
\]
Let \(E_\perp\) denote the orthogonal projection onto the complement of (2.5). The Frobenius norm counts repeated-index coefficients three times and distinct-index coefficients six times. Hence
\[
 \|E_\perp\|_F^2=
 \sum_i d_i^2+\frac32\sum_{i<j}(a_{ij}+b_{ij})^2
       +6\sum_{i<j<k}c_{ijk}^2.
 \tag{2.6}
\]
In (2.3), the squared norm is \(4\sum d_i^2+2\sum(a_{ij}+b_{ij})^2\). In the ordered commutator array (2.4), a pair sum occurs four times and a distinct triple occurs twenty-four times, with signs immaterial after squaring. Therefore
\[
 \boxed{\ \|d\mathcal R_D(E)\|^2
 =4\sum_i d_i^2+6\sum_{i<j}(a_{ij}+b_{ij})^2
       +24\sum_{i<j<k}c_{ijk}^2
 =4\|E_\perp\|_F^2.\ }
 \tag{2.7}
\]
Equivariance transfers this equality to every point of \(\mathcal M\).

### 2.4 Nonlinear equation-residual error bound

Choose a nearest point \(S\in\mathcal M\) to \(T\), possible by compactness, and put \(E=T-S\), \(d=\|E\|_F\). Differentiating \(\|T-(e^{tK})^{\otimes3}S\|_F^2\) at its minimum shows \(E\) is perpendicular to every orbit tangent direction at \(S\). No uniqueness of the nearest point, globally defined coordinates, constant-rank theorem or tubular-neighborhood theorem is being assumed.

Because \(\mathcal R\) is quadratic,
\[
 \mathcal R(S+E)=d\mathcal R_S(E)+Q(E),\quad
 Q(E)=\left(\sum_rE_r^2,\ ([E_r,E_s])_{r,s}\right).
\]
The elementary product bounds give
\[
 \left\|\sum E_r^2\right\|_F\le\sum_r\|E_r\|_F^2=d^2,
 \qquad
 \left(\sum_{r,s}\|[E_r,E_s]\|_F^2\right)^{1/2}\le2d^2.
\]
Thus \(\|Q(E)\|\le\sqrt5d^2\), and (2.7) yields
\[
 R(T)\ge 2d-\sqrt5d^2.
 \tag{2.8}
\]
In particular,
\[
 \operatorname{dist}(T,\mathcal M)\le R(T)
 \quad\text{if }\operatorname{dist}(T,\mathcal M)\le1/\sqrt5.
 \tag{2.9}
\]
The premise here is proximity. We now pay for it from equation residual, rather than concealing it as an assumption.

If \(\eta(T)\le1\), then
\(\|T\|_F^2=\operatorname{tr}\sum T_r^2\le2m\).
On the compact set
\[
 \mathcal K_m=\{T\in V:\|T\|_F\le\sqrt{2m},\
              \operatorname{dist}(T,\mathcal M)\ge1/\sqrt5\},
\]
the continuous function \(R\) has a strictly positive minimum \(\alpha_m\): a zero would belong to \(\mathcal M\), a contradiction. If the set is empty set \(\alpha_m=1\). Therefore, with
\[
 \varepsilon_m=\min\{1/2,\alpha_m/(2\sqrt{m+1})\}>0,
\]
\[
 \eta(T)\le\varepsilon_m
 \quad\Longrightarrow\quad
 \operatorname{dist}(T,\mathcal M)\le\sqrt{m+1}\,\eta(T).
 \tag{2.10}
\]
This proves the exact fixed-dimensional replacement needed for Lemma A. Compactness supplies **only an entrance cutoff**. It supplies neither the exponent nor an unknown modulus; the linear estimate follows from the explicitly computed transverse derivative and quadratic remainder. A prescribed dimension-polynomial entrance threshold is not obtained by this argument. H53 does not require one.

## 3. Full H53 from the source and ordinary interpolation

To avoid judging only the tensor lemma, here is the complete reduction. It is independent of I53's cubic-maximization/deflation proof. It uses the same natural interpolation of the source's exact compatibility identities, whose derivation is spelled out so that no weak-derivative estimate is presumed.

First center and whiten a smooth log-concave density whose potential has positive finite lower and upper Hessian bounds. By the pinned affine normalization, there is symmetric \(P>0\) and a centered Gaussian transport \(F\) to \(P_\# f\) with
\[
 DF=q(A),\qquad \mathbb EA=0,\qquad A=L+Y,\quad
 L(x)=\sum_rx_rX_r,\quad B=\sum_rX_r^2.
\]
The actual `matrix.tex`, `mat:strict-remainder`, gives
\[
 \|Y\|_2^2\le1000\delta,\qquad\sum_i\omega(\lambda_i(B))\le2000\delta.
\]
The displayed source weight is continuous, positive off 1, coercive at infinity and bounded below by a positive multiple of \((\lambda-1)^2\) on \([1/2,2]\). Thus, below an absolute positive gap cutoff,
\[
 \operatorname{spec}B\subset[1/2,2],\quad
 \|B-I\|_F\le C\sqrt\delta,\quad \sum_r\|X_r\|_F^2\le2m.
 \tag{3.1}
\]
I53's elementary evaluation of the same weight gives the more specific cutoff \(5\cdot10^{-8}\); that numerical value is not needed for H53.

By the source's forward Frobenius Lipschitz inequality,
\[
 \|q(L)-DF\|_{L^2(\gamma_m)}\le e:=\sqrt{1000\delta}.
\]
Let \(K_{irs}=\partial_r q(L)_{is}-\partial_s q(L)_{ir}\). Its distributional value is the curl of \(q(L)-DF\). On a dimension-only ball around zero the coefficients of \(L\) are uniformly bounded by (3.1). Smooth matrix functional calculus, applied near the scalar matrix zero, bounds all derivatives of \(q(L)\) up to order three, independently of the density and its Hessian bounds. Consequently \(K\) and \(DK\) have dimension-only Lipschitz bounds there.

For a fixed smooth compactly supported unit-integral bump \(\rho\) and \(\rho_h=h^{-m}\rho(\cdot/h)\), integration by parts gives
\[
 |(K*\rho_h)(0)|\le C_m e h^{-m/2-1},\quad
 |D(K*\rho_h)(0)|\le C_m e h^{-m/2-2}.
\]
The local lower Gaussian density converts the field error to the required Lebesgue \(L^2\) bound. The Lipschitz bounds give errors \(C_mh\) between these averages and the actual jets. Taking \(h=e^{2/(m+6)}\) below the chosen ball radius, and \(e\le1\), proves
\[
 |K(0)|+|DK(0)|\le C_m\delta^{1/(m+6)}=:C_m\nu.
 \tag{3.2}
\]
At \(\delta=0\), use vanishing distributional curl and continuity directly. This is standard negative-Sobolev-to-pointwise interpolation for a uniformly smooth finite-parameter family, not an assertion that derivatives of an arbitrary small \(L^2\) error are small.

The source's `lem:linear-jacobian` gives the exact first two jets, with \(a=q'(0)>0\), \(b=q''(0)/2>0\):
\[
 K_{\cdot rs}(0)=a(X_re_s-X_se_r),
\]
\[
 \partial_tK_{\cdot rs}(0)
 =b\{(X_rX_t+X_tX_r)e_s-(X_sX_t+X_tX_s)e_r\}.
\]
Writing \(S_{rs}=X_re_s-X_se_r\), the braces equal
\([
 X_r,X_s]e_t+X_rS_{ts}-X_sS_{tr}+X_tS_{rs}\).
The bounded coefficient norm therefore turns (3.2) into \(O_m(\nu)\) coefficient-symmetry and commutator-array errors. Full symmetrization is an orthogonal projection on the tensor space; its distance from \(X\) is \(O_m(\nu)\). Call the result \(T\). Expanding the quadratic products gives
\[
 \eta(T)\le C_m(\nu+\sqrt\delta)\le C_m\nu.
\]
Every constant here is a bump norm, a fixed local derivative bound or a finite-dimensional product/norm constant. Lower the dimension-only deficit cutoff so that \(\eta(T)\le\varepsilon_m\). Equation (2.10) now supplies \(T^*=\sum_j u_j^{\otimes3}\) with
\[
 \|X-T^*\|_F\le C_m\delta^{1/(m+6)}.
 \tag{3.3}
\]

Define
\[
 H(x)=\sum_ju_j\{t(\langle u_j,x\rangle)-1\},\quad
 t(s)=-\log\Phi(-s),\quad L^*(x)=\sum_j\langle u_j,x\rangle u_ju_j^T.
\]
Then \(DH=q(L^*)\), \(\mathbb EH=0\), \(\operatorname{Cov}H=I\), and \(H_\#\gamma_m=\mathcal L(UZ_m)\). Gaussian orthogonality identifies the coefficient norm in (3.3) with \(\|L-L^*\|_2\). The source's forward Lipschitz inequality followed by Gaussian Poincaré gives
\[
 r:=\|F-H\|_2\le\|DF-DH\|_2
 \le\|Y\|_2+\|L-L^*\|_2\le C_m\delta^{1/(m+6)}.
 \tag{3.4}
\]
All maps belong to Gaussian \(H^1\); \(q\) grows at most linearly and \(L^*\) is linear. No inverse-\(q\) bound or transport tail truncation is used.

For clarity, the covariance normalization can be removed even without the stronger Jensen bound already available inside the source normalization proof. Since \(\operatorname{Cov}F=P^2\), put \(G=P^{-1}F\); both \(G,H\) are centered isotropic. The cross covariance \(M=\mathbb E(GH^T)\) is an operator-norm contraction by scalar Cauchy–Schwarz. Diagonalizing \(P\) yields \(\operatorname{tr}(PM)\le\operatorname{tr}P\), hence
\[
 r^2=\operatorname{tr}P^2+m-2\operatorname{tr}(PM)
 \ge\|P-I\|_F^2.
\]
Shrink the cutoff so \(r\le1/2\); then \(P\succeq I/2\), and the existing Gaussian coupling gives
\[
 W_2(f,H_\#\gamma_m)\le\|P^{-1}F-H\|_2
 \le2\{r+\|(I-P)H\|_2\}\le4r.
 \tag{3.5}
\]
Thus no uncontrolled condition number remains. Alternatively, the source's spectral-measure Jensen/first-chaos argument gives \(P\succeq q(0)I\), exactly as I53 records.

For larger deficits, independent coupling of centered isotropic laws gives \(W_2\le\sqrt{2m}\); enlarge \(C_m\) using the positive dimension-only small-gap cutoff. This establishes the claimed global bound for the smooth class.

For arbitrary log-concave \(f\), use the actual `geo:approximation` proof, whose exponential envelope yields weighted \(L^1\) convergence with weight \(1+|x|^2\), entropy convergence, mean convergence and covariance convergence to \(C>0\). Weighted \(L^1\) implies \(W_2\) convergence by coupling the common density part identically and the two residual parts independently. Centering and whitening preserve the limit because the covariance matrices converge to a positive matrix. Their entropy gaps converge by affine invariance. Distance to the fixed entire orbit of laws is 1-Lipschitz in \(W_2\), so the bound passes to the limit. No approximation rate, uniform approximant Hessian bounds or limiting orientation selection is required.

For \(m=1\), (3.1) directly puts the single coefficient within \(O(\sqrt\delta)\) of \(\{1,-1\}\). Reconstruction and normalization give the claimed exponent \(1/2\). This completes the full-scope reduction.

## 4. What is inherited and what I53 contributes

The complete main manuscript was read: scalar/certificate estimates, noncommuting matrix completion and slack cancellation, transport normalization, approximation, rigidity including the full equality/compactness proof, and the cone geometry. All eleven cached main-family files and four general-Mahler companion files have independent Git-blob checks against the full tree. Additional companion statements are identified in [pinned-manifest.json](../sources/i56_sharp_entropy_stability_novelty/pinned-manifest.json); exact excerpts and read ranges are in [passages.json](../sources/i56_sharp_entropy_stability_novelty/passages.json).

The source already supplies more than a qualitative equality classification. Its strict remainder controls nonlinear Gaussian chaos and the first-chaos sum of squares. Its exact compatibility proof explicitly extracts coefficient symmetry and commutation from the first two Taylor terms. Its compactness proof already uses the forward spectral Lipschitz inequality, Gaussian Poincaré, covariance convergence, affine de-normalization and unrestricted approximation. I53's mollification pays an ordinary interpolation loss for exactly those existing jets. Section 3 shows that no unproved global regularity or support hypothesis is added in quantifying those operations.

Lemma A gives a useful constructive version, with threshold \(10^{-6}m^{-4}\), coefficient error \(20m\eta\), and a transparent quadratic restriction budget. Its use of a globally maximizing cubic direction rather than an arbitrary eigenvector is meaningful within that proof. This review does not claim that its precise recursion is copied from an antecedent. But H53 discards the dimension-polynomial nature of that algebraic threshold when choosing its final cutoff and constant from unoptimized dimension-dependent analytic bounds. Replacing it with (2.10) leaves the theorem, exponent, metric and hypotheses unchanged. Thus no indispensable nonroutine contribution remains at the nominated statement's level.

Construction B is a genuine different proof route but does not rescue significance: it quantifies simultaneous diagonalization by conventional spectral partitions, with a weaker power. The one-dimensional claim, cone-law consequence and directed-KL counterexample are also technical within the stated standard. Dimension-uniform U and simplex Banach–Mazur stability are unpaid objectives and supply no credit to H53. R013 is neither used by the reduction nor an alleged duplicate.

## 5. Actual primary literature and companion comparisons

The following comparisons concern the actual statements/proof passages, not title matching. Current arXiv abstract histories and unversioned PDF responses were independently refreshed in UTC on 2026-10-10 (local review date 2026-10-09); received PDF filenames and first-page versions are recorded. These are the latest versions served by the endpoints at capture, not a certificate about every publisher revision. [Primary request manifests](../sources/i56_sharp_entropy_stability_novelty/literature/manifest.json) and [additional requests](../sources/i56_sharp_entropy_stability_novelty/literature/manifest-additional.json) preserve response bytes, hashes, timestamps and failures.

- **Boralevi–Draisma–Horobeţ–Robeva, arXiv 1512.08031v1**, §3.1, Lemma 11 and Proposition 12: exact associativity characterizes real symmetric odeco tensors. The proof splits into orthogonal simple ideals and forces each ideal to be one-dimensional. This is equation characterization, not a residual estimate. Its hypotheses are satisfied here by real full tensor symmetry and the Euclidean inner product; §2.1 also proves the needed normalized case directly. [Primary paper](https://arxiv.org/abs/1512.08031v1).
- **Biaggi–Draisma–Seynnaeve, arXiv 2206.01521v1 and published 2022 article**, §4.2, Proposition 4.1 in the journal: the associativity equations at the diagonal cubic have the triple-zero and paired-opposite tangent conditions. Remark 4.2 states smoothness at full-rank strongly odeco tensors. This is a direct antecedent to the parent's transverse-derivative objection. The real normalized Euclidean error bound is supplied in §2, so no assertion about scheme-theoretic equations or absence of other complex components is imported. **Robeva, arXiv 1409.6685v3**, Lemma 3.7, is the earlier Jacobian-rank argument credited there. [Published Biaggi et al.](https://rendiconti.dmi.units.it/volumi/54/017.pdf), [Robeva](https://arxiv.org/abs/1409.6685).
- **Auddy–Yuan, arXiv 2007.09024v2**, Theorem 2.4 compares two already odeco tensors in tensor spectral norm. Theorem 3.1 starts with explicit factor matrices whose singular values lie in \([1-\epsilon,1+\epsilon]\); its proof uses their polar factors and a telescoping product estimate. It does not turn I53's associativity residual into proximity. The author was correct about that limitation. Our replacement supplies proximity first and needs neither theorem as a black box. [Primary paper](https://arxiv.org/abs/2007.09024v2).
- **Mu–Hsu–Goldfarb, arXiv 1705.10404v1**, Theorem 2.2 and Lemma 2.3 start from a known orthogonally decomposable tensor plus a perturbation; maximization, first-order conditions and no singular-value separation produce component estimates. Theorem 3.1 and Lemma 3.2 control successive deflation; the text explicitly explains why errors act quadratically in unused directions. Equation-residual proximity is not their input. We attribute maximization and controlled deflation, not I53's exact residual recurrence, to this antecedent. [Primary paper](https://arxiv.org/abs/1705.10404v1).
- **Filonov–Kachkovskiy, arXiv 1008.4002v2**, Theorem 2 and its spectral-block proof give the two-matrix normalized Hilbert–Schmidt power \(1/4\). Theorem 3 gives power \(1/4^{k-1}\) for \(k\) matrices, with threshold \(16^{-2\cdot4^{k-2}}\). The matrix-size uniformity is not matrix-count uniformity. The real version follows by carrying out the displayed diagonalization/block restrictions with real symmetric matrices. This supports conventional fallback Construction B, not H53's linear tensor estimate directly. [Primary paper](https://arxiv.org/abs/1008.4002v2).
- **Fradelizi–Marín Sola, arXiv 2406.07406v1**, Conjecture 3(iii), Proposition 5.2, Lemmas 5.1–5.2 and their proofs: the sharp entropy/functional-isotropic formulation is connected to simplex slicing by a fixed cone lift in one direction and auxiliary dimensions tending to infinity in the other. No quantitative near-product law theorem follows from those limiting formulas alone. The pinned bibliography records a 2026 Indiana journal article, but this audit did not independently retrieve its final full text. The author-PDF TLS failure persists and is retained. This limitation does not affect the transverse reduction. [Primary preprint](https://arxiv.org/abs/2406.07406v1).
- **Melbourne–Nayar–Roberto, arXiv 2309.01840v2**, and the independently retrieved author-hosted published PDF: Theorem 1.1 is the scalar entropy lower bound. Sections 3–4 use entropy-preserving decreasing rearrangement with a variance comparison, degrees of freedom/localization to two-piece log-affine laws, and a scalar inequality. They do not furnish arbitrary-dimensional law-distance stability. We do not convert that minimization reduction into a quantitative near-minimizer decomposition. [Published article](https://link.springer.com/article/10.1007/s00440-025-01431-3), [author PDF](https://perso.pages.math.cnrs.fr/users/cyril.roberto/Articles/Melbourne-Nayar-Roberto.pdf).
- **Rademacher, arXiv 1404.5662v2**, Theorems 1–2 and the symmetry proof, and **Kipp, arXiv 2411.08722v2**, Theorem 1.5 and its proof: they constrain local isotropic maximizers. Kipp's bound \(\dim S(K^\circ)\le(n^2+3n)/2\) follows by selecting a deformation in the kernel of moment variations and obtaining a contradictory second variation. Kipp's **2407.01353v2**, Theorem 1.2, reduces a polytopal local maximizer with a simplicial vertex to a simplex. These are not quantitative global distances to a simplex or H53. [Rademacher](https://arxiv.org/abs/1404.5662v2), [Kipp's current theorem](https://arxiv.org/abs/2411.08722v2), [simplicial-vertex theorem](https://arxiv.org/abs/2407.01353v2).
- **Myroshnychenko–Tang–Tatarko–Tkocz, arXiv 2403.11994v3**, Theorem 1, is dimension-free stability of the *section direction of a fixed regular simplex*, expressed through the density at zero of an exponential linear combination. It is not stability of the isotropic constant over arbitrary bodies. The old and tilde author-PDF URLs both returned 404; the current arXiv and publisher article succeeded. This resolves the relevance of I53's failed simplex-slicing request without erasing it. [Current primary paper](https://arxiv.org/abs/2403.11994v3), [published article](https://link.springer.com/article/10.1007/s00454-025-00758-x).

The general-Mahler companion's `06-linear-equality.tex` deduces commutation from diagonal support of a spectral measure, then a cone product from a diagonal projection Jacobian. Its layer defect is different from the sharp entropy remainder. Its `09-consequences.tex` explicitly distinguishes the auxiliary-dimensional functional passage from an equality classification. The symmetric-Mahler companion concerns Hanner bodies and a different extremal value; the logBM companion concerns symmetric Wulff interpolation. None is misused to supply an unproved entropy deficit comparison or a simplex-section stability bridge.

The complete nontruncated tree has 13,223 entries and **749** manuscript roots. A fresh `rg --files --no-ignore` inventory hashes all **9,340** ignored corpus files. Three independent whole-corpus searches retain **84**, **137**, and **83** matching lines as sorted **multisets**, including irrelevant hits and multiplicities. The full manuscript inventory was screened and actual relevant source files were read; this is not a claim to have read all 9,340 files. The catalogue's 719 count and truncated root cache were not used as completeness evidence. Broader web searches found neighboring entropy-power and fixed-simplex-slicing results, not an exact H53 statement. That bounded observation is not a worldwide priority certificate.

## 6. Objections, recorded author positions and disposition

These are responses to the frozen report, not invented correspondence with its author. Machine-readable versions are retained in [objections-and-responses.json](../sources/i56_sharp_entropy_stability_novelty/objections-and-responses.json).

1. **“Proximity is the missing input, whereas perturbation theorems assume it.”** Correct for Auddy–Yuan and Mu–Hsu–Goldfarb as cited. It does not defeat the standard alternative: §2.4 obtains proximity from bounded residual compactness and then linear control from the paid transverse calculation. The same full H53 follows.
2. **“Compactness gives no power.”** Correct by itself. Here (2.7)–(2.9), not compactness, give the power one. Compactness only selects a positive fixed-dimensional cutoff, which H53 permits. The calculation also proves why a larger tangent kernel or singular stratum does not intervene under normalization.
3. **“Lemma A has an explicit polynomial threshold and controlled deflation.”** A useful improvement in proof constructiveness. H53 asserts arbitrary finite dimensional constants and has no optimized global constant or uniform dimensional rate. That improvement cannot distinguish its full theorem from §3.
4. **“Weak Hessian compatibility is a new analytic bridge.”** The source already identifies exactly the two required jets and gives their nonsingular coefficients. Uniform local smoothness of the bounded linear-field family plus distributional mollification gives (3.2) by elementary scaling. No density-specific inverse regularity or tail estimate remains unpaid. This is a technical quantification of an explicit source operation.
5. **“Affine normalization and nonsmooth support might defeat the alternative.”** Equations (3.4)–(3.5) pay the normalization cost, even without the source's stronger Jensen estimate. Weighted approximation and whitening continuity pay arbitrary support and nonsmoothness. These interfaces therefore do not distinguish H53.
6. **“The dimension-uniform and simplex applications make the contribution substantial.”** They remain unproved. A W2 approximation need not align a cone apex or give ray transversality at a fixed section. Neither is used to justify the verdict. The full-support asymmetric-Laplace directed-KL obstruction is sound as a screen but does not enlarge H53.
7. **“No exact prior statement was found.”** Retained as a limited search observation. The verdict is TECHNICAL ONLY rather than DUPLICATE because it rests on the explicit reduction, not an assertion of theorem identity with a published result.

The relevant problem family is quantitative near-extremizer structure for the sharp log-concave entropy bound/strong isotropic constant problem. The inequalities and equality cases are already premises. No verified problem-specific MathDB score was found in the inherited retained request, and none is asserted here.

## 7. Reproducible evidence and limits

From the project root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i56_sharp_entropy_stability_novelty/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i56_sharp_entropy_stability_novelty/verify.py
```

Both commands are offline and read-only. The independent diagnostics make **9,367 exact rational assertions**: complete derivative Gram identities in dimensions 1–7, tangent directions, quadratic Taylor remainders and their bound, normal-slice examples, the necessity of normalization, and rational orthogonal equivariance. They do not numerically estimate the compactness cutoff or certify a universal theorem. The universal coordinate proof and nearest-orbit argument are §§2–3.

The verifier checks its sealed inventory, frozen inputs, author's unmodified evidence hashes and retained failure history, full tree/manuscript inventory, pinned Git blobs, all corpus hashes, search line multisets, captured primary responses, fresh PDF-to-text replays, exact passage slices, and deterministic diagnostic output. It also executes the original I53 verifier unchanged and compares its immutable results while treating only the four designated ledgers as mutable. Primary PDF pages for the key tangent calculation, exact associativity proof and many-matrix exponent were rendered and visually checked against the extraction.

The optional live-fetch helper is separate from offline verification and refuses to overwrite its original manifest. Network failures are evidence limitations, not proof failures, and are retained. The verdict is a contribution recommendation under the pinned premises; it neither revises the original author evidence nor substitutes for I55's original-proof acceptance decision.
