# Structural233, independent substantial-contribution review, round 1

**Conditional verdict: TECHNICAL, conditional on full correctness of the ENTIRE unchanged frozen statement AND submitted proof. Full correctness remains UNDISCHARGED in this role.** This is a contribution recommendation for parent adoption, not a correctness verdict, acceptance, or count. I have neither read nor used another review or a parent assessment.

The object reviewed is exactly FROZEN-STATEMENT.md (1160 bytes, SHA256 `3d9a20ab3e17778919f3ae159b1e297d682c63b4a8c98474fb9c99d7e7fe65da`) together with author-proof.md (25166 bytes, SHA256 `302d436f1beb448f9c06031d6a078892a433099d5b845b84d4b76b351659d286`). No repair, restricted target, selected sublemma, alternate regularity definition, or intrinsic-distance replacement is being graded. The auxiliary estimates and smooth round-sphere discussion are included.

The reason for the conditional technical verdict is a complete compatible reduction using Source357's actual internal positive heat identities, cumulative normalization estimates, directional pinching, all-order iteration and ambient-distance argument. The finite constant in its headline theorem is not the strongest usable input. The extra relative estimate follows by keeping the exact positive increment, performing a fine positive interpolation, and retaining the source's already proved cumulative error budget. All changes to the fields satisfy the source iteration's hypotheses, with fixed constants chosen before the final flatness parameter. The derivation below explains this assertion, including every scale, all centers, noncommuting matrices, all jets and all ambient pairs. It is not a conclusion from the failure of other chart methods.

## 1. Scope, evidence and paid operations

Source357 is the exact eight-blob paper at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, under `preprints/Bi-Lipschitz-Coordinates-at-Regular-Points-of-Noncollapsed-RCD-Spaces-September-25-2026/`. I independently bound all eight admitted copies to the complete pinned tree by their Git blob hashes. I read the full operative driver, introduction, coordinates, pinching and renormalization files. The upstream proofs are stipulated true; this review uses, rather than audits, those proofs. The actual main theorem has dimension-only distortion (4\sqrt{A(n)}), not arbitrary distortion. Its internal estimates are stronger inputs than that final constant.

The following interfaces are used in their actual forms. Line coordinates refer to the exact admitted TeX bytes; the reading log also records byte intervals.

* `coordinates.tex` 143–394: after rescaling about a point with all Euclidean tangents, arbitrarily small all-center/all-scale flatness on every fixed enlargement; harmonic maps; positive averaged Gram matrices (R_i(y)); strong normalized harmonic approximation; nearby-center comparison; slow scale growth with any prescribed small positive exponent; and small positive Bochner mass. The reference measure is exactly the scaled normalized Hausdorff measure.
* `coordinates.tex` 398–465: the initial harmonic map is a homeomorphism on the required fixed ball onto an open value domain; there are central ellipsoids, and additive normalized distance estimates at each fixed scale ratio. This does not assert that the metric regular set is open.
* `coordinates.tex` 489–700: Gaussian and first-pole-gradient bounds, including integration against the positive matrix-valued Bochner measure and continuity at every pole; remote-cutoff control; positive heat matrices (Q_i), their inverses (H_i), monotonicity, near-identity initial normalization, and slow inverse growth. The singular part of the Bochner measure is included.
* `coordinates.tex` 719–1039: Gaussian-shell domination, positive heat decrements, matrix inverse increments, and the cumulative weighted quadratic-form budget, not just pointwise comparability. The proofs allow noncommuting matrices.
* `coordinates.tex` 1041–1166: center-dependent inverse-normalization error, including testing it against any positive coefficient dominated by a small multiple of (Q_i); arbitrary bounded collections of nearby centers; cumulative upper bounds and a separate weight-one covering hypothesis for the lower bound.
* The whole `pinching.tex`, especially its final directional conclusions: positive scale errors (E_i(x)), with a positive floor at each scale and \(\sup_x\sum_iE_i(x)\to0\), and directional mass bounds for differences (P_x-P_z) on any fixed enlargement. Its linear (L^1) estimates, Poisson/volume-drop control, harmonic affine improvement, radial transport and two-center argument are paid, including their all-center quantifiers.
* `renormalization.tex` 112–307, 308–506, 507–694, 695–839: displacement centers selected by an approximate infimum, positive-field estimates, Gevrey jets, inverse-transpose iteration, same-base inverse majorants, the diagonal square sum, accumulated metric errors, uniform tails and all-ambient-pair recovery. These are paid at their full hypotheses. They do not require a limiting (H_i), differentiable (H_i), or globally injective approximants.

The primary comparisons in sections 7–9 below are independent readings of actual selected proofs, with their limits stated separately. None supplies a hidden additional premise to the source-based reduction. No original-history mathematical body was read; no history clearance or literature-priority claim is made.

## 2. Exact positive increments give the leading metric

Work first in one sufficiently flat rescaled source model. Write (r_i=2^{-i}), (P_x=u(x)), and
\[
 Q_i(x)=P_{r_i^2}(\chi G)(x)+\lambda r_i^2I,\qquad H_i=Q_i^{-1}.
\]
All statements below are uniform for the testing centers in the fixed inner ball, every finite (k), and every vector \(\xi\). Constants may depend on fixed dimension, enlargement and cutoff parameters; they do not depend on (i,k,x\) or the final flatness index. Use (A[v]=v^TAv\), and write \(\varepsilon\downarrow0\) for a common bound on the source's smallness parameters after all fixed choices.

The cutoff Bochner identity is
\[
 \Delta(\chi G)=2\chi\mathsf M-2\kappa\chi G+\mathsf E_{cut}.
\]
The source chooses \(\lambda\to0\) large enough to dominate the cutoff and curvature errors. Consequently, for (t\in[r_i^2/4,r_i^2]\),
\[
 \partial_t\{P_t(\chi G)+\lambda tI\}=2P_t(\chi\mathsf M)+T_t,
 \qquad0\le T_t\le q_\nu I,\quad q_\nu\to0.
\]
Here (q_\nu\to0\) follows from the actual estimates on \(\kappa\), the cutoff error and \(\lambda\); a fixed upper bound is not all that is available. Define
\[
 C_i(x)=2\int_{r_i^2/4}^{r_i^2}P_t(\chi\mathsf M)(x)\,dt,
 \quad U_i=\int_{r_i^2/4}^{r_i^2}T_t\,dt.
\]
Then \(\Delta_i=Q_i-Q_{i+1}=C_i+U_i\), with (C_i,U_i\ge0\) and \(U_i\le q_\nu r_i^2I\).

The correct inverse calculation is by conjugation, not by commuting (Q_i,Q_{i+1}\). Put (E_i^{mat}=Q_i^{-1/2}\Delta_iQ_i^{-1/2}\). The source gives (0\le E_i^{mat}\le\varepsilon I\). Exactly,
\[
 H_{i+1}-H_i=Q_i^{-1/2}\big((I-E_i^{mat})^{-1}-I\big)Q_i^{-1/2}.
\]
Functional calculus for this one symmetric matrix yields
\[
 H_i\Delta_iH_i\le H_{i+1}-H_i
 \le(1-\varepsilon)^{-1}H_i\Delta_iH_i. \tag{2.1}
\]
Thus the sum of the inverse quadratic remainders is at most (C\varepsilon H_k\), rather than (k\varepsilon H_k\). Fix the source slow-growth exponent (a=1/16\). Since \(\|H_i\|\le C_a2^{2ai}\),
\[
 \sum_i H_iU_iH_i[\xi]
 \le C_aq_\nu\sum_i2^{-(2-4a)i}|\xi|^2
 \le Cq_\nu H_k[\xi].
\]
The last comparison uses (H_k\ge H_0\simeq I\). It follows that
\[
 \left|\left(I+\sum_{i<k}H_iC_iH_i-H_k\right)[\xi]\right|
 \le o_\nu(1)H_k[\xi]. \tag{2.2}
\]
The (I-H_0\) term is small in the same relative norm. This is the first sharp constant: it comes from the exact heat identity, already paid, and not from improving a fixed coarse (C_*\) by assertion.

For later localization, introduce the positive Gaussian envelope
\[
 W_i^c(x)=r_i^{2-n}\int e^{-c d(x,z)^2/r_i^2}\chi(z)\,d\mathsf M(z).
\]
Let (N_j=r_j^{2-n}\mathsf M(B_{r_j}(x))\) and let the source's weighted matrix be
\[
 \mathcal F_i=2^{-\gamma i}I+\sum_{j\le i}2^{-\gamma(i-j)}N_j,\qquad\gamma=1/2.
\]
Dyadic spatial shells give (W_i^c\le C_c\mathcal F_i\): for a shell of radius (2^hr_i\le1\), its coefficient on (N_{i-h}\) is at most
\(C2^{(n-2)h}e^{-c'4^h}\le C_c2^{-\gamma h}\). For shells beyond radius one, the source's raw cutoff-mass estimate \((\chi\mathsf M)(B_s(x))\le Cs^{n-2}I\), (s\ge1\), and the Gaussian give a remainder bounded by (C_c2^{-\gamma i}I\). For (n=2\) the power is simply zero; no strict (n>2\) argument is being used.

The source's cumulative weighted estimate now gives
\[
 \sum_{i<k}W_i^c(x)[H_i(x)\xi]\le C_cH_k(x)[\xi]. \tag{2.3}
\]
Its proof already pays the noncommuting transport of (H_i\xi\) across scales: for (j\le i\), the square of their difference in the (Q_j\)-norm is controlled by
\(C(i-j)2^{2a(i-j)}\sum_{\ell=j}^{i-1}(H_{\ell+1}-H_\ell)[\xi]\).
The geometric weights absorb this factor. Also \(\sum_i2^{-\gamma i}|H_i\xi|^2<\infty\), since (4a<\gamma\). These are precisely the summations needed here; no bound on \(\sup_i\|H_i\|\) is assumed.

## 3. Localization, moving poles and fine normalized interpolation

Take a Lipschitz scalar cutoff \(\eta_L(z;x,i)\) equal to one on (B_{Lr_i/2}(x)\), zero outside (B_{Lr_i}(x)\), between zero and one, with Lipschitz constant (C/(Lr_i)\). Define the localized positive increment
\[
 C_i^L(x)=2\int_{r_i^2/4}^{r_i^2}\int
 p_t(x,z)\eta_L(z;x,i)\chi(z)\,d\mathsf M(z)\,dt.
\]
For fixed (L\ge2\), (C_i^L(x)\le C r_i^{2-n}\mathsf M(B_{Lr_i}(x))\). In the omitted region split one Gaussian into two factors. One is bounded by (e^{-cL^2}\), and the other is still a Gaussian envelope. Therefore (2.3), with a fixed weaker exponent, gives
\[
 \sum_{i<k}(C_i-C_i^L)[H_i\xi]\le b_LH_k[\xi],
 \qquad b_L\le Ce^{-cL^2}\longrightarrow0. \tag{3.1}
\]
This is a cumulative estimate. It does not compare a tail with a small lower heat-kernel constant on an expanding ball.

If (d(x,y)\le hr_i\), (0<h\le1\), the source's all-pole gradient bound, integrated along a short geodesic, gives
\[
 |p_t(y,z)-p_t(x,z)|\le Ch r_i^{-n}e^{-c d(x,z)^2/r_i^2}.
\]
The difference of the two cutoffs is at most (Ch/L\); its product with the kernel satisfies the same envelope bound. Time integration has length at most (r_i^2\). For every fixed test vector (v\), including when the measure is singular,
\[
 |(C_i^L(y)-C_i^L(x))[v]|\le Ch W_i^c(x)[v]. \tag{3.2}
\]
The constants in this bound can be taken independent of (L\ge2\). It is a scalar estimate after testing a positive matrix measure, so no derivative of a measurable matrix field or exceptional-pole assertion has been introduced.

Choose a maximal (hr_i\)-separated net in the inner source ball. With the source Gevrey-2 bump \(\psi\), put
\[
 \psi_{i,y}(P)=\psi((hr_i)^{-1}R_i(y)^{-1/2}(P-P_y)),\quad
 g_i=\sum_y\psi_{i,y},\quad \phi_{i,y}=\psi_{i,y}/g_i.
\]
These functions are considered on the common open harmonic value domain \(\Omega=u(B_1(p))\). The denominator is at least one: a net point within (hr_i\) has normalized harmonic distance below (2hr_i\), after choosing flatness small *after* (h\). Support localization is not inferred circularly from the net spacing. First use the source's slow-growth separation to get (d(x,y)\le C_0r_i\) for an active center. Then use harmonic distance approximation on this fixed enlargement, with additive error smaller than (hr_i\), to improve to (d(x,y)\le4hr_i\). Packing at scale (hr_i\) gives at most (J(n)\) active centers, independent of (h\). Hence (1\le g_i\le J\), \(\sum\phi_{i,y}=1\), and (0\le\phi\le1\).

Here is the derivative cost of the denominator, which cannot be omitted. In the frozen (H_i\)-normalized coordinates, each bump has
\[
 r_i^m\|D^m\psi_{i,y}\|\le C_h^{m+1}(m!)^2.
\]
The same holds for (g_i\) with bounded overlap. Differentiating (g_i^{-1}\) produces ordered compositions (m=m_1+\cdots+m_\ell\), (m_j\ge1\), multiplied by (g_i^{-\ell-1}\), multinomial coefficients and products of (D^{m_j}g_i\). Since (g_i\ge1\),
\[
 {m!\over\prod m_j!}\prod(m_j!)^2
 =m!\prod m_j!\le(m!)^2.
\]
There are at most (2^{m-1}\) ordered compositions, and their fixed constants and the factor from differentiating the inverse are absorbed in a new exponential base. The usual symmetric multilinear product formula gives the same estimate; equivalently its ordered-partition form cancels the inverse-derivative factorial against repeated blocks. Thus
\[
 r_i^m\|D^m\phi_{i,y}\|\le C_h^{m+1}(m!)^2. \tag{3.3}
\]
For explicit one-variable majorants, the recurrence from (g_i g_i^{-1}=1\), divided by ((m!)^2\), has convolution coefficients \(\binom m\ell^{-1}\le1\), and proves the exponential bound directly; polarization only changes its exponential base. This also verifies the all-orders, rather than finite-order, assertion. Smoothness is needed on \(\Omega\), where (g_i>0\), not outside it.

Define the constant patch coefficient and its two sums by
\[
 A_{i,y}={1\over2}R_i(y)^{-1}C_i^L(y)R_i(y)^{-1},\quad
 S_i(x)=\sum_y\phi_{i,y}(P_x)A_{i,y},\quad
 Z_i(x)=\sum_{y\ {m active\ at}\ x}A_{i,y}.
\]
Their positivity is essential. The local heat bound dominates (A_{i,y}\) by a fixed multiple of the source patch matrix formed from (r_i^{2-n}\mathsf M(B_{Lr_i}(y))\). For (L,h\) fixed, the source gives
\[
 Z_i\le\varepsilon H_i,\qquad \sum_{i<k}Z_i\le C_{L,h}H_k. \tag{3.4}
\]
The normalized partition does not have a member of weight one in general. To use the source cumulative lemma, give **every active center auxiliary weight ONE**, only for bounding the unweighted (Z_i\). There are at most (J\) centers, and (B_{r_i}(x)\subset B_{Lr_i}(y)\) for an active center if (h\) is chosen small and (L\ge2\). Thus its stated covering condition holds. Its upper-bound proof in fact does not need that condition. This application does not assert that the actual \(\phi\)'s have weight one and does not replace them in (S_i\).

It remains to handle inverse normalization, rather than assuming neighboring inverses are harmless over infinitely many scales. Put
\(a_i=H_i(x)\xi\), \(e_{i,y}=R_i(y)^{-1}\xi-a_i\).
The exact paid normalization-error estimate implies
\[
 \sum_{i<k,y\ active}C_i^L(y)[e_{i,y}]\le C_{L,h}\varepsilon H_k[\xi]. \tag{3.5}
\]
Indeed (C_i^L(y)\le C_{L,h}\varepsilon Q_i(x)\); the source first bounds the sum of the (Q_i\)-squares of (e_{i,y}\) by (C_JH_k\), and permits any such positive testing coefficients. The factor \(\varepsilon\) is retained. By (3.2), (2.3) and \(\sum\phi=1\),
\[
 \left|\sum_{i,y}\phi_{i,y}C_i^L(y)[a_i]
       -\sum_i C_i^L(x)[a_i]\right|\le ChH_k[\xi]. \tag{3.6}
\]
The main positive sum on the left is bounded by (CH_k[\xi]\), for fixed parameters. The cross terms are bounded on the *whole combined index set*:
\[
 2\left|\sum_{i,y}\phi_{i,y}C_i^L(y)(a_i,e_{i,y})\right|
 \le2\Big(\sum\phi C_i^L(y)[a_i]\Big)^{1/2}
        \Big(\sum\phi C_i^L(y)[e_{i,y}]\Big)^{1/2}
 \le C_{L,h}\sqrt\varepsilon H_k[\xi].
\]
Together with (3.5), (3.1) and (2.2), this proves
\[
 \left|\left(I+2\sum_{i<k}S_i-H_k\right)[\xi]\right|
 \le\big(b_L+Ch+o_{\nu;L,h}(1)\big)H_k[\xi]. \tag{3.7}
\]
This is the author's proposed extra operation at its full uniform (x,k,\xi\) scope. It is obtained from exact paid positive identities plus localization, Gaussian-shell summation, positive quadratic-form algebra and a fixed fine cover. No new quantitative differentiability or geometric regularity theorem is needed. The order (L\), then (h\), then flatness is indispensable.

## 4. The fine fields satisfy the full source iteration

This is the compatibility step that a leading-constant argument by itself would leave unfinished. For each patch choose a single (z_{i,y}\) in its active source set with (E_i(z_{i,y})<2\inf E_i\), and set (c_{i,y}=P_{z_{i,y}}\). The positive source floor makes this possible even without continuity or an attained minimum. For every testing point where the bump or any of its derivatives is supported, (E_i(z_{i,y})\le2E_i(x)\). Both points are within a fixed multiple of (r_i\) of (y\). The source directional estimate, applied to the dominating local mass matrix, yields
\[
 A_{i,y}[P_x-c_{i,y}]\le C_Lr_i^2E_i(x),\qquad
 |P_x-c_{i,y}|_{H_i(x)}\le Cr_i. \tag{4.1}
\]
The finer spacing can improve the latter bound, but no such improvement is required. There is no scale-dependent choice of a moving displacement center when differentiating in value space.

Use exactly the source type of field,
\[
 v_i(P)=\sum_y\phi_{i,y}(P)A_{i,y}(P-c_{i,y}).
\]
The coefficients and centers are constant in (P\). With (Q=H^{-1}\), (Z=Z_i\), (S=S_i\), (E=E_i(x)\), positivity and (3.4) give
\[
 |Aw|_Q^2\le\varepsilon A[w],\quad
 |\xi^TAw|^2\le A[\xi]A[w],\quad SQS\le\varepsilon Z.
\]
Write (Dv_i\xi=S\xi+e_i(\xi)\). Applying (3.3) and (4.1) term by term gives all the source field inputs, now with constants depending on the fixed (L,h\):
\[
 \begin{split}
 r_i^{-1}|v_i|_Q&\le C\sqrt\varepsilon\sqrt E,\\
 |S\xi|_Q&\le\sqrt\varepsilon\sqrt{Z[\xi]},\\
 |e_i(\xi)|_Q&\le C\sqrt\varepsilon\sqrt E\,|\xi|_H,\\
 |\xi^Te_i(\xi)|&\le C\sqrt{Z[\xi]E}\,|\xi|_H,\\
 r_i|D^2v_i(\xi,\xi)|_Q
 &\le C\{\sqrt{Z[\xi]}|\xi|_H+\sqrt E|\xi|_H^2\}.
 \end{split} \tag{4.2}
\]
For example, (e_i(\xi)=\sum(D\phi_{i,y}\xi)A_{i,y}(P_x-c_{i,y})\). Its diagonal bound uses the positive-form inequality before summing the at most (J\) roots of (A_{i,y}[\xi]\). The second derivative has precisely the terms (D^2\phi\,Aw+2D\phi\,A\xi\), and those two positive inequalities give the displayed estimate. These calculations include all partition derivatives, rather than treating the partition as a constant weight.

In order (m\ge1\), the product has only (D^m\phi\,Aw\) and (mD^{m-1}\phi\,A\), because the displacement is affine. The isotropic bounds (A\le\varepsilon H\), \(|w|_H\le Cr_i\) and (3.3) consequently give
\[
 r_i^{m-1}\|D^mv_i\|_{H_i\to Q_i}
 \le\varepsilon C_{L,h}^{m+1}(m!)^2 \qquad(m\ge0). \tag{4.3}
\]
Thus the full all-orders Gevrey input survives the normalization. Increasing (C_{L,h}\) is harmless only because it is fixed before the final flatness choice; it is not discarded as a universal constant.

Set (h_0(P)=P\), (J_i=Dh_i\), and
\[
 h_{i+1}=h_i+J_i^{-T}v_i\quad\hbox{on }\Omega.
\]
Use a provisional metric bootstrap factor (A_0=2\). Freeze the normalized coordinates (P=P_x+r_iH_i(x)^{-1/2}X\). Under the old-level metric bootstrap the normalized inverse has bounded zeroth norm. The source's inverse-majorant argument uses
\(L_m=(m+1)((m+1)!)^\sigma\), with \(\sigma=2\), and the convolution ratios
\(\sum_{\ell=1}^{m-1}L_\ell L_{m-\ell}/L_m\to0\).
The finite low orders are absorbed by choosing a sufficiently large fixed base (B\); higher orders use these ratios. Crucially, differentiating the inverse retains that SAME exponential base (B\). Combining this with (4.3) bounds the increment jets by \(\varepsilon C_{A_0,L,h}B^mL_m\). When changing from (r_i\) to (r_{i+1}=r_i/2\), the old (m\)-jet, (m\ge2\), contracts by at least (2^{1-m}\); the relative added coefficient is bounded by
\[
 \varepsilon C_{A_0,L,h}B\,2^{1-m}(m+1)^3.
\]
Its supremum over all (m\ge2\) is finite. Choose flatness after (B\) to close the all-orders bound with factorial order (3\). This is the actual source mechanism, including the derivative loss in the inverse, not a claim that a finite (C^2\) estimate closes an infinite iteration.

For the metric estimate fix (x,\xi\), put (q_i=|\xi|_{H_i}\), (b_i=r_i|D^2h_i(\xi,\xi)|/q_i\), (K_i=J_i^{-T}\), and (W_i=K_iv_i\). The first two derivatives of (K_i\), from the normalized old-level jets, obey
\[
 |D_\xi K_iw|\le Cq_i r_i^{-1}|w|_{Q_i},\quad
 |D_\xi^2 K_iw|\le Cq_i^2r_i^{-2}|w|_{Q_i}.
\]
The three terms (K_iD^2v_i\), (2D K_i Dv_i\), and (D^2K_iv_i\) in (D^2W_i\) give
\[
 b_{i+1}\le\tfrac12b_i+C(\sqrt{Z_i[\xi]}+\sqrt{E_i}q_i),\qquad b_0=0.
\]
Here monotonicity (q_{i+1}\ge q_i\) supplies the factor one half. Convolution by (2^{-j}\) has finite \(\ell^1\) norm, so its \(\ell^2\) operator norm is bounded. Using (3.4), (H_i\le H_k\), and \(\sum_iE_i(x)\le\varepsilon\),
\[
 \sum_{i<k}b_i^2\le C\sum_{i<k}(Z_i[\xi]+E_iq_i^2)
 \le CH_k[\xi]. \tag{4.4}
\]
Similarly
\[
 |(J_{i+1}-J_i)\xi|^2\le C\varepsilon(Z_i[\xi]+E_iq_i^2). \tag{4.5}
\]
There is an exact contraction identity for the differentiated inverse:
\[
 \langle J_i\xi,(D_\xi K_i)v_i\rangle
 =-\langle D^2h_i(\xi,\xi),K_iv_i\rangle.
\]
Consequently the squared-metric increment is exactly
\[
 |J_{i+1}\xi|^2-|J_i\xi|^2
 =2S_i[\xi]+2\xi^Te_i(\xi)
  -2\langle D^2h_i(\xi,\xi),K_iv_i\rangle
  +|(J_{i+1}-J_i)\xi|^2. \tag{4.6}
\]
Every accumulated cross term is controlled: by (4.2) and (3.4), the first error sum is at most
\(C(\sum Z_i[\xi])^{1/2}(\sum E_iq_i^2)^{1/2}\le C\sqrt\varepsilon H_k[\xi]\).
For the inverse term use (4.4) in the same inequality with (b_i\) in place of \(\sqrt{Z_i[\xi]}\); even after dropping its extra \(\sqrt\varepsilon\) factor, it is at most (C\sqrt\varepsilon H_k[\xi]\). The square sum (4.5) contributes (C\varepsilon H_k[\xi]\). No \(\sum\sqrt{E_i}\) is required. Thus
\[
 \left||J_k\xi|^2-|\xi|^2-2\sum_{i<k}S_i[\xi]\right|
 \le C_{L,h,B}(\sqrt\varepsilon+\varepsilon)H_k[\xi]. \tag{4.7}
\]
Combining (4.7) with (3.7) gives arbitrarily small relative error:
\[
 (1-\theta)H_k\le J_k^TJ_k\le(1+\theta)H_k. \tag{4.8}
\]
This closes (A_0=2\) with slack. At level (k\), all inverse and jet estimates used to prove (4.7) concern levels below (k\). Hence the calculation proves invertibility at the new level before the new inverse is used. The all-orders assertion then follows from the old-level jet step. This is a finite-index induction with an all-orders statement at each index; it does not assume convergence of derivatives or uniform ellipticity of (H_i\) in the original Euclidean norm.

Finally, (4.2) and the metric bootstrap give \(|h_{i+1}(P_x)-h_i(P_x)|\le C\sqrt\varepsilon r_i\sqrt{E_i(x)}\). As each (E_i\le\varepsilon\), the geometric tail is uniformly bounded by \(\tau r_i\), with \(\tau\to0\) for fixed (L,h,B\). Thus (h_i\circ u\) converges uniformly on the source ball to a continuous (F\), and
\[
 \sup_x|F(x)-h_i(P_x)|\le\tau r_i. \tag{4.9}
\]
This proves the uniform tail needed for every pair, not merely pointwise convergence.

## 5. All ambient pairs, open image, parameter order and original units

For clarity, one admissible parameter order is
\[
 n,\eta\ \longrightarrow\ \theta\ \longrightarrow\ L\ \longrightarrow\ h
 \ \longrightarrow\ A_0=2,\sigma=2,B\ \longrightarrow\ D,\rho
 \ \longrightarrow\ \hbox{sufficiently late rescaling index }\nu.
\]
Choose \(0<\theta<\min\{1/100,\eta/[8(1+\eta)]\}\). Choose (L\) to make (b_L\) a sufficiently small fraction of \(\theta\), then (h\) to do the same for (Ch\). Fix all field and inverse-majorant constants, then (B\). Choose (D\) large compared with the fixed normalized Hessian bound and inverse central-ellipsoid radius. Set, for example, \(\rho=(16D+4)^{-1}\). Only then choose \(\nu\) so that all source flatness, all fixed-enlargement statements, support localization, jet absorption, (4.8), and \(4D\tau\le\theta\) hold. Require also the normalized harmonic additive distance error at the fixed ratio (2D\) to be at most a suitable fraction of \(\theta r_i/D\). The source permits arbitrarily small errors with these finitely many fixed constants, without a uniform rate. Finally require the original rescaling factor (s_\nu\) to satisfy (s_\nu\rho<R\).

For distinct (x,z\in B_\rho(p)\), put (t=d(x,z)\) in rescaled units and choose a dyadic index with (Dt\le r_i<2Dt\). The normalized harmonic distance estimate and (Q_i\simeq R_i\) give
\[
 (1-\theta)t\le|P_z-P_x|_{H_i(x)}\le(1+\theta)t
\]
after allotting smaller intermediate errors. The segment between (P_x,P_z\) is in the source central ellipsoid and hence in (u(B_{r_i/2}(x))\subset\Omega\). This is a supplied image-containment statement, not an assumption that the harmonic image of a ball is convex. Along this segment the source's nearby-center comparisons bound the scale-(i\) norms by a fixed multiple of the norm at (x\). The all-order bootstrap, already in order two, therefore bounds the Taylor remainder by
\[
 |h_i(P_z)-h_i(P_x)-J_i(P_x)(P_z-P_x)|
 \le {C_B\over r_i}|P_z-P_x|_{H_i(x)}^2
 \le {C'_B\over D}t\le\theta t.
\]
Use (4.8) on the linear term and (4.9) at the two endpoints; the latter costs at most (2\tau r_i\le4D\tau t\). Tightening the allotted small fractions gives
\[
 (1-4\theta)d(x,z)\le|F(x)-F(z)|\le(1+4\theta)d(x,z). \tag{5.1}
\]
The chosen \(\theta\) ensures (1-4\theta\ge(1+\eta)^{-1}\) and (1+4\theta\le1+\eta\). The same holds trivially at equal points.

Every distance used here is the original ambient distance in the rescaled space. No geodesic is required to stay in (B_\rho(p)\); the argument selects its scale from that ambient distance and uses the source central ellipsoid to do the value-space Taylor comparison. Thus it proves the requested co-Lipschitz bound, not just a differential inequality for an intrinsic length metric. It gives injectivity and a continuous inverse onto the image. For openness use the already paid harmonic homeomorphism (u:B_\rho(p)\to u(B_\rho(p))\), whose image is open, and invariance of domain for (F\circ u^{-1}\). The image (V\) is open. Subtract (F(p)\) so (0\in V\).

Rescaling back by (s_\nu\), multiply target coordinates by (s_\nu\), and take (r=s_\nu\rho\). The exact Hausdorff measure scales by (s_\nu^{-n}\), and the curvature bound becomes (s_\nu^2K\); every real (K\) is covered. The original space is complete, separable, geodesic and full noncollapsed RCD, with full-support exact normalized \(\mathcal H_d^n\) finite on bounded sets, throughout. The source flat setup uses the regular-point hypothesis that **all** tangents are Euclidean. Nothing replaces it by almost-everywhere regularity or existence of one Euclidean tangent. Each integer (n\ge2\) is retained; constants depend on (n\), with no common-in-(n\) claim. Both \(\eta>0\) and (R>0\) were arbitrary, and the permitted dependence of (r\) includes all the supplied data. The resulting domain is the full open ambient ball, and the target is an open Euclidean set, not a measurable piece. There is no assertion about a uniform radius, an atlas, harmonicity of (F\), regularity of its pulled-back tensor, or openness of the metric regular set.

The round-sphere auxiliary is likewise a classical compatible consequence, not an additional operation. On a smooth round sphere, use normal coordinates on a larger ball of radius (a\) with metric coefficients between ((1-\delta)^2I\) and ((1+\delta)^2I\). On a much smaller ball of radius (b<a/3\), any ambient minimizing path exiting the larger ball has length at least (2(a-b)>2b\), whereas the path through the center has length below (2b\). Thus ambient minimizers stay in the larger coordinate neighborhood. Integrate the lower tensor bound along them and the upper bound along the straight coordinate segment (in the normal-coordinate Euclidean ball) to obtain both all-pair bounds. Shrink (a\), then (b\), to meet any \(\eta,R\). Exact normalized Hausdorff measure is the Riemannian volume under this convention. A sphere of radius (s\) has \(\operatorname{Ric}=(n-1)s^{-2}g\), so for any prescribed finite (K\) a suitable radius has \(\operatorname{Ric}\ge K\). This example neither requires zero curvature nor turns the theorem into an isometry assertion on a fixed positive-radius ball.

## 6. Summable metric Reifenberg: strongest compatible use

I used Gigli–Violo, arXiv **2406.13771v1**, reading the main statements (269–333), the product/tail/all-pair argument (618–744), the transition construction at 1244–1432, the local argument at 1433–1584, and the finite-color smooth gluing proof at 2043–2174. This is more than the theorem name or a GH analogy, but not a claim to have read every construction lemma in the paper. Its remaining intermediates are listed in READING-LIMITS.md.

The operative input is a spatially uniform summable scale-flatness sequence, with compatible local models. The proof constructs smooth models and transition maps with multiplicative distance errors of the form (1+C(\epsilon_i+\epsilon_{i+1})\), and displacement errors of order (\epsilon_i r_i\). Thus a tail starting at (m\) has product
\[
 \prod_{i\ge m}(1+C(\epsilon_i+\epsilon_{i+1}))
 \le\exp(2C\sum_{i\ge m}\epsilon_i),
\]
which approaches one when the uniform tail sum tends to zero. The distance estimates in the proof concern the limiting metric space, not only lengths of selected curves. The local construction additionally keeps domains inside larger ones with a fixed boundary margin; the transition and tail estimates are only asserted where that margin is retained.

A coarse initial constant in the *local Euclidean start* is not an obstruction to almost isometry. Start instead at a sufficiently late smooth model (W_m\), retain an interior subdomain, and choose a small normal-coordinate neighborhood in its smooth metric. Its tensor is as close to Euclidean as prescribed. The model pseudodistance agrees with the relevant local Riemannian distance at sufficiently short separations; restriction to a smaller neighborhood prevents a short connecting path from leaving the larger one. The all-pair product and uniform displacement tail then transfer the small distortion to the limiting metric space. This is the strongest compatible summable-Reifenberg route. The gluing proof explains what it needs: fixed finite colors, controlled chart-transition (C^1\) errors, (C^2\) local models, a boundary gap, and errors small enough to absorb a finite (D^N\)-type loss. These are substantive hypotheses, not supplied by merely writing down GH approximations independently at each scale.

The source has \(\sup_x\sum_i E_i(x)\to0\), a directional weighted energy budget, and arbitrarily small uniform flatness, but it does not state \(\sum_i\sup_x\epsilon_i(x)<\infty\) for its raw GH discrepancies. Interchanging the supremum and sum is not justified. Nor does a qualitative GH modulus applied to each (E_i\) automatically produce a summable sequence. To run this particular metric-Reifenberg proof directly on the raw source approximations, the missing bridge is a compatible model/transition construction whose *uniform distortion sequence* has a summable small tail. No separating RCD example is asserted. In fact sections 2–5 construct the needed compensated metric operation by another paid route, using a quadratic rather than a raw-GH budget. Thus the absence of this particular bridge cannot support SUBSTANTIAL here. I do not claim the source hypotheses are outside the strongest possible application of Gigli–Violo; I claim the independent direct reduction makes that exclusion unnecessary.

## 7. Coherent planes: actual square-sum and ambient-pair mechanism

For David–Toro, arXiv **0910.4869v1**, read in Latin1, I read the coherent-collection and initial-model definitions and theorems at 594–864, the full square-error lemma at 2501–2644, and the all-pair argument through Proposition 8.34 at 2648–2987. The full preceding graph/diffeomorphism construction and later ambient-extension sections were not independently reread. They are not premises of sections 2–5.

The input is extrinsic: a coherent collection of balls and affine (d\)-planes in one finite-dimensional Euclidean ambient space, with nearby same-scale and parent-child plane coherence, and a smooth initial surface locally represented by small (C^2\) graphs. It is stronger data than intrinsic GH closeness of an RCD ball. The quantity \(\epsilon'_k(f_k(z))\) measures the relevant local interplane discrepancies; the bi-Lipschitz criterion has a uniform bound
\[
 \sup_{z\in\Sigma_0}\sum_k\epsilon'_k(f_k(z))^2\le M.
\]
The crucial proof operation is cancellation of first-order tangential distortion. In the derivative of the averaged projection, the normal components are first order in the plane discrepancy, their effect on tangential length is second order, and the partition derivatives use \(\sum D\theta=0\). Lemma 7.32 obtains a length factor (1+C(\epsilon'_k)^2\), not a factor linear in \(\epsilon'_k\). The product is bounded by \(\exp(CM)\). This is exactly why a square sum can suffice despite divergent sums of individual angular errors.

The all-pair proof does more than integrate along an intrinsic path. It transports paths forward and backward on the approximating surfaces, chooses the scale at which the two transported points separate by a fixed fraction of the mesh, and uses a uniform spatial tail (C\epsilon r_k\). Dividing this tail by the stopping-scale separation gives (C\epsilon\). Keeping the factors rather than rounding them to fixed constants yields distortion approaching one when the relevant square-sum bound and flatness tend to zero, after choosing a sufficiently small smooth initial-model chart. A final coarse factor such as two in a displayed global theorem is therefore not an irreducible barrier. A small tail must be uniform over the relevant starting points; convergence of a separate square series at each point alone does not give that uniform tail. Restriction to an inner neighborhood is also required for its smooth initial model and local coherence.

What is not supplied directly by Source357 is a finite-dimensional extrinsic embedding together with coherent planes whose square discrepancies are controlled by its directional energy and whose Euclidean chord metric is the original intrinsic ambient metric to arbitrarily small relative error. Taking every plane to be \(\mathbb R^n\) in harmonic value space erases precisely the varying Gram metric and does not establish this condition. Deriving such an embedding-and-plane package would be a real missing step *for that proposed alternative*. It is not evidence of substantiality for the submitted theorem: the source already supplies the matrix analogue of the necessary compensation, and sections 2–5 carry it through without introducing planes. No example separating all such plane realizations is used or claimed.

## 8. RCD harmonic stability, rectifiable pieces and analytic charts

These comparisons retain the precise scope of the results rather than treating “harmonic coordinates” or “rectifiability” as an open-chart theorem.

**Ambrosio–Honda, 1703.04939v1.** I read the local Sobolev compactness and gradient/Laplacian stability proofs at 1010–1160, the Dirichlet replacement convergence argument at 1164–1267, and harmonic approximation at 1339–1359. The Dirichlet result uses the equality of the two relevant zero-boundary Sobolev spaces at the chosen radius; this is not automatic at every radius. Local harmonic approximation can choose a suitable intermediate radius and restrict inward. Compactness of functions and strong energy/gradient convergence then provide harmonic approximations to limit linear coordinates. These are compatible paid ingredients in the source's harmonic preparation. They do not alone give a uniform positive lower Gram bound on a neighborhood at every later scale, injectivity on an entire ball, or an all-pair small-distortion open chart. In this reduction those are obtained by the actual source normalization and iteration, not inferred from Sobolev convergence.

**Mondino–Naber, 1405.2222v3.** I read the rectifiability good-set argument at 1323–1437. Its maximal excess/gradient control removes a small bad set; on a good set the same distance-coordinate map has all-scale estimates, which yield almost-isometric pair bounds there. Weak-(L^1\) estimates control the removed measure, and countably many such pieces cover almost every point. This is stronger than a mere GH approximation, and its distortion can be arbitrarily close to one. It is nonetheless a statement on measurable pieces, not a proof that every prescribed regular point belongs to a whole open good ball. An exceptional measure-zero point cannot be restored by the weak-type bound alone. The source's all-center construction, including its supplied harmonic homeomorphism and directional sums, is the paid mechanism used here to handle the prescribed point and the entire ball.

**De Philippis–Gigli, 1708.02060v3, revised June 2025.** I read statements at 609–631 and 716–750, the noncollapse/convergence proof at 1744–1775, and the volume-rigidity proof at 1776–1825. At the operative geometric interface, normalized Hausdorff measure, Bishop–Gromov density, volume convergence and Euclidean rigidity identify the Euclidean limit and yield qualitative quantitative flatness by compactness. The rigidity proof passes from extremal volume information through the cone/density mechanism to Euclidean space, rather than simply labeling a tangent regular. These operations justify small flatness under the proper noncollapsed and normalization hypotheses. They provide no summable rate from a general qualitative modulus. The present reduction needs no such rate: its fixed parameters are chosen first and then the point-dependent radius is reduced.

**Kapovitch–Mondino, 1907.02614v3.** I read 740–879, including the neighborhood/topological stability argument. Nearly maximal volume at a center propagates quantitative near-Euclidean information to nearby centers and smaller scales via volume comparison, followed by the topological Reifenberg mechanism. This explains why a *neighborhood* bound can follow from the appropriate initial noncollapsed volume condition; it would be inaccurate to dismiss the comparison simply as pointwise regularity. Its topological/Hölder output and stability toward a smooth model do not themselves supply the sharp Lipschitz conclusion in the submitted scope. Conversely, when a smooth local model with controlled small distortion and a summable correction is present, the smooth-start argument in section 6 applies. No unproved uniform radius over arbitrary regular-point families is used.

**HZ26, 2608.16021v1 (the exact version identified by the brief).** I read definitions at 1690–1731; regular-point/rigidity criteria at 1732–1794; the transformation discussion at 1795–1964; chart characterization and its proof at 1967–2080; good-set/Hessian criteria at 2083–2193; and the nondegeneracy argument at 2195–2328. This last argument and the transformation discussion extend the author's selective comparison. The transformation discussion is itself an outline that invokes HP Corollary 3.6 and Propositions 3.7 and 4.7; I have not independently read those separate primary proofs. Its scope is therefore reported, not silently promoted to a wholly independently discharged alternative derivation.

The actual distinctions are these. Infinitesimal positive Gram data by itself is not injectivity; the elementary absolute-value example already distinguishes them. The analytic open-chart criterion combines neighborhood flatness, appropriately scaled Morrey bounds on Laplacians, and a neighborhood essential lower bound for Gram nondegeneracy. The quantitative good-set version keeps all-scale averaged Gram matrices close to positive comparison matrices. Hessian Morrey control of the form (r^{1-\delta}\fint_{B_r}|\operatorname{Hess}\phi|\le\gamma\), \(\delta>0\), yields decaying Gram oscillation and a summable scale comparison. The nondegeneracy proof uses pointwise Morrey control to show that a putatively degenerate linear combination has too-small growth, contradicting the lower growth supplied by the chart approximation and volume packing. Pointwise nondegeneracy at one point is still not an essential uniform lower determinant throughout an open neighborhood.

For the source harmonic map (u\), the Laplacian is zero, so a Laplacian requirement alone is no obstruction. The issue is the other hypotheses: each finite-scale (R_i(y)\) is positive, but it need not have an unnormalized lower bound uniform in (i\); the source only bounds inverse growth with an arbitrarily small exponent chosen before rescaling. Also its small normalized Bochner mass yields a Hessian estimate with the scale (r^{-1}\) times a small energy factor, not automatically the power improvement (r^{\delta-1}\) for any fixed \(\delta>0\). Replacing this by a Morrey power bound would require an extra rate not in the stipulated interface. The limit (F\) is not claimed to have the Laplacian, Hessian or tensor regularity needed to run those criteria backward.

These observations do not prove that the candidate hypotheses fail every analytic chart criterion, and no such example is supplied. They identify precisely what a direct use of the inspected criteria would still need. The complete alternative used for the verdict instead is sections 2–5, which normalizes the Gram geometry scale by scale and uses only square-summable directional errors. The unread HP and related rigidity intermediates are not essential premises of that reduction. An exhaustive analytic-literature comparison remains outside the evidence here; it is not converted into a novelty claim or a reason for SUBSTANTIAL.

## 9. Colding–Naber: actual construction and compatibility

I read **1111.2184v1** at 103–181, 188–281, 283–380, and 384–430: its statements, embedding argument, volume-preserving sphere-diffeomorphism construction, angle argument and the Hölder-metric obstruction. In addition, I fetched **1108.3244v1**, the cited antecedent, and read its entire construction Lemma `l:ExamTech` and proof, lines 204–300, bytes [14494,21714). This closes the author's quoted-lemma reading limit for the near-tip mechanism actually used in this comparison. Its large-radius extension is described briefly rather than computed in that primary proof; the local comparison below uses the explicit near-tip formulas only.

The construction takes volume-preserving diffeomorphisms \(\varphi_s\) of the round sphere, with (g_s=\varphi_s^*g_{\mathbb S}\), and forms
\[
 \bar g=dr^2+r^2h(r)^2g_{f(r)}.
\]
Every link is isometric to the round sphere, although its tensor in the fixed angular coordinates varies. The diffeomorphisms are built from a rotation Killing field multiplied by a rotation-invariant tubular cutoff. Its divergence vanishes, so the flow preserves the volume form. Pieces begin and end at the identity. A covering construction makes fixed angular pairs have prescribed limiting separations along selected parameter sequences. Reparameterization ensures bounded first and second metric derivatives and the spatial derivative bound required by the construction lemma.

The antecedent proof computes the Ricci components, uses the fixed volume form to cancel the problematic trace derivatives, and chooses, near zero,
\[
 h(r)=1-\frac{E}{\log(-\log(r_0r))},\qquad
 f(r)=-F\log(\log(-\log(r_0r))).
\]
With small constants in the stated order its radial, tangential and mixed Ricci estimates give nonnegative Ricci. In particular (h\to1\), (f\to-\infty\), and
\[
 |rf'(r)|=\frac{F}{\log(-\log(r_0r))(-\log(r_0r))}\longrightarrow0.
\]
The important features are infinite total angular travel and vanishing travel per logarithmic scale, not a positive lower distortion of every chart. Truncating in identity intervals gives the smooth approximating metrics. The example is smooth off its tip, all its tangent cones are Euclidean, and its radial minimizing geodesics can have arbitrarily oscillating mutual comparison angles. The (C^{0,\beta}\)-metric obstruction uses a *summable* dyadic angle-change estimate arising from a Hölder tensor. A fixed arbitrarily small bi-Lipschitz distortion on a shrinking ball does not give that summable estimate.

One can make the compatibility particularly concrete within the actual allowed construction. Choose the concatenated smooth flow pieces with bounded Eulerian angular velocity \(\sup_{s,x}|\partial_s\varphi_s(x)|_{g_{\mathbb S}}\le M\). This can be imposed simultaneously with the stated metric-derivative bounds: every compact smooth piece has finite bounds on its velocity and the three required metric derivatives; slowing its parameter sufficiently reduces the first derivatives and both terms in the second derivative. Smooth cutoffs flat at the endpoints permit the pieces to be concatenated with identity intervals. Their order and angular-distance events are retained, and the truncation times can be taken in the retained identity intervals. No assertion is made that bounded metric derivatives *alone* bound a Killing component of velocity, or that every unspecified choice of the paper's parametrization has this additional bound.

For this permissible choice define the explicit untwisting homeomorphism
\[
 \Psi(r,x)=r\varphi_{f(r)}(x),\qquad\Psi(0)=0.
\]
It maps radial balls onto Euclidean radial balls. For a tangent pair ((a,v)\), put (w=rD\varphi_{f(r)}v\), and let (V=\partial_s\varphi_s|_{s=f(r)}\). Then
\[
 |(a,v)|_{\bar g}^2=a^2+h^2|w|^2,
 \qquad |D\Psi(a,v)|^2=a^2+|w+a\,rf'V|^2.
\]
Both (1-h\) and \(|rf'|M\) tend uniformly to zero as (r\downarrow0\). The two triangular linear transformations in this display and their inverses therefore have norm (1+o(1)\). Integration gives almost-isometric length comparison on each sufficiently small punctured radial ball, extending across the tip by continuity. For all ambient pairs in a still smaller ball (B_b\), choose a larger (B_a\), (b<a/3\): a minimizing path exiting (B_a\) costs at least (2(a-b)>2b\), whereas the path through the tip costs at most (2b\). Thus ambient minimizers remain in (B_a\). The straight segment in \(\Psi(B_b)\) lifts inside (B_b\); these two families of paths give both ambient distance inequalities. Infinite angular twisting and failure of every Hölder tensor persist because the angular-distance events were retained. The slow functions above need not have a Hölder modulus.

This is a compatibility calculation within the actual construction's choices, not a replacement of the frozen theorem, and not a claim about a particular unrecorded parametrization. It shows directly why neither failure of the original angular coordinates nor the Hölder obstruction separates the submitted almost-isometric-chart assertion. The finite-dimensional embedding theorem in the same primary paper is a different result: it gives finite distortion into higher Euclidean dimension, not an open image in \(\mathbb R^n\). Its external finite-dimensional projection lemma was not independently read and is not used here. The example argument is in dimensions (n\ge3\); it supplies no obstruction in dimension two either. No unproved separating example supports the contribution verdict.

## 10. Objections resolved, limits and final conditional finding

The principal objections and resolutions are:

1. **A fixed source leading constant cannot be declared near one.** Agreed. Equations (2.1)–(3.7) replace that coarse comparison using the exact positive heat increment and its actual cumulative budget. They establish a leading error (b_L+Ch+o_{\nu;L,h}(1)\), not an unspecified fixed (C\).
2. **Noncommuting inverse matrices can accumulate errors.** The conjugated inverse identity and the source normalization-error estimate control their entire sum. Positivity permits the combined-index cross-term estimate; pointwise closeness alone is not used to sum infinitely many errors.
3. **A partition with sum one loses the weight-one covering hypothesis.** The actual partition is retained for the leading term. Auxiliary unit weights are used only for the upper bound on the unweighted active sum, where the source hypotheses hold. No weight-one assertion about the partition is made.
4. **Finer covers may destroy the iteration through derivative costs.** Every partition derivative is included in (4.2)–(4.3); the cost (C_{L,h}\) enters the all-order base before flatness is selected. Fixed displacement centers use the source positive floor and approximate infimum, not an unproved continuous minimizer.
5. **Inverse differentiation or cross terms might require summable square roots.** The full inverse-majorant step, the diagonal recurrence and (4.6)–(4.7) show exactly which sums occur. Only \(\sum E_i\) and the paid weighted matrix sum are used.
6. **Differential control need not imply all ambient pairs or openness.** The central ellipsoid, stopping scale and uniform tail supply the ambient estimate, then the paid harmonic topology and invariance of domain supply the open image. No intrinsic-metric substitution occurs.
7. **Primary comparators might already give arbitrary distortion.** Their small product/square-sum tails indeed do so under compatible hypotheses; a coarse theorem constant is not treated as a barrier. The specific raw-GH, extrinsic-plane and analytic-Morrey bridges were not established from the source. They are unnecessary because the complete heat-based reduction already establishes technicality. Their absence is not novelty evidence.
8. **Angle examples might separate the result.** They do not supply the asserted obstruction. The actual construction and its antecedent support the explicit compatibility calculation in section 9.

The additional mathematical work in the submission is useful: it extracts an almost-isometric conclusion from the strongest internal source mechanisms and makes the constant-loss bookkeeping explicit. At this scope, however, the surviving operation is positive heat-increment localization and interpolation with compatible source estimates, followed by an already paid iteration. It does not require an additional geometric or analytic estimate beyond those interfaces. The fine-cover algebra, Gaussian tail estimate, noncommuting inverse identity and parameter order have been derived here, rather than named as “standard.” They cover the whole frozen statement and the submitted auxiliary discussion, not merely a selected leading estimate.

**The conditional contribution recommendation is therefore TECHNICAL.** Its condition is full correctness of the entire unchanged statement and proof, which remains **UNDISCHARGED** here. This review makes no correctness PASS finding, no acceptance decision and no count. It does not establish worldwide novelty or nonnovelty by exhaustive literature search. Essential comparison for this source-based technical reduction is complete; the explicitly unread external intermediates limit broader literature comparisons, not an input needed in the reduction. If the parent requires a conclusion specifically about an exhaustive literature reduction through one of those unread routes, that distinct comparison is unfinished and must not be represented as settled.
