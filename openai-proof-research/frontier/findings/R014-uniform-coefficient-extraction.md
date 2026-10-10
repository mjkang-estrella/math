# R014 — Dimension-uniform coefficient extraction from nonlinear curl

**Accepted as the eighth substantial finding.** The [complete I61 proof](../iterations/i61-averaged-entropy-coefficient-rounding.md) passes [I63's independent original-proof review without repairs](../reviews/i63-entropy-coefficient-extraction-r2.md). [I64's separate contribution review](../reviews/i64-entropy-coefficient-extraction-novelty.md) judges the uniform compatibility implication **SUBSTANTIAL**, with the bounded-energy symmetric repair included in the same finding as a technical supporting operation. Both parent reproductions pass. Acceptance uses the stipulated OpenAI corpus at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; it does not certify worldwide priority, human peer review or a formal proof.

## Exact theorem

Let \(q(a)=\varphi(a)/\Phi(-a)\), where \(\varphi,\Phi\) are the standard Gaussian density and distribution function. For every fixed finite \(K\ge0\), every integer \(m\ge1\), and every family of real symmetric \(m\times m\) matrices \(X_1,\ldots,X_m\), assume
\[
B=\sum_r X_r^2\preceq KI,
\qquad L(x)=\sum_r x_rX_r,
\qquad \mathsf X_{ijr}=(X_r)_{ij}.
\]
Write \(\operatorname{Sym}\) for orthogonal projection onto fully symmetric cubic tensors, and use unnormalized Frobenius norms. Define
\[
t=\frac1m\mathbb E_{x\sim\gamma_m}\sum_{i,r<s}
\left|(Dq(L(x))[X_r])_{is}-(Dq(L(x))[X_s])_{ir}\right|^2,
\]
where \(Dq(A)[H]\) is the Fréchet derivative of the spectral matrix function. Then
\[
\boxed{\quad
\frac{\|\mathsf X-\operatorname{Sym}\mathsf X\|_F^2+
\sum_{r,s}\|[X_r,X_s]\|_F^2}{m}
\le\chi_K(t),\qquad \chi_K(t)\longrightarrow0\quad(t\downarrow0).
\quad}
\]
Write E_X for the numerator on the left. The same modulus works for all dimensions and all such families. It is zero at zero, and for \(0<t\le1/2\) it satisfies
\[
\chi_K(t)\le\frac{C_K}{\log(e/t)},\qquad C_K<\infty.
\]
There is no assumption of full tensor symmetry, approximate normalization \(B\approx I\), density realization, or a bounded third-slot Gram matrix. The commutator sum includes the whole ordered family; its cardinality grows with dimension.

An explicit admissible modulus is as follows. For \(R\ge1\), put
\[
a_R=\min_{[-R,R]}q'>0,\quad h_R=\min_{[-R,R]}q''>0,
\quad M_R=16R^2a_R^{-2}+16h_R^{-2}(1+2a_R^{-2}),
\]
\[
F_K(R)=8(1/3+18K)a_R^{-2}+8M_R,
\qquad D_K=4K^2+504K^3.
\]
Then one may take
\[
\chi_K(t)=\min\left\{K+4K^2,
\inf_{R\ge1}\bigl(F_K(R)t+D_K/R^2\bigr)\right\}.
\]
No sharp rate or optimized numerical constant is claimed.

## Proof and dependencies

The full proof and all constants remain in the unchanged I61 report, §§3–5; I63 checks each original step. Its essential chain is:

1. The Gaussian conditional-excess survival function gives strict \(q''>0\), with \(a_R\ge R\varphi(R)\) and \(h_R\ge R e^{-R^2-4R-20}/(2\pi)\). This uses the source's scalar identities and an explicit positive double integral, not sampled scalar minima.
2. At each \(x\), diagonalize \(L(x)\), rotate all three coefficient indices, and use the same basis at \(-x\). For one triple, the two measured curls are \(e_+=\alpha A-\beta C\) and \(e_-=\gamma A-\eta C\), with divided differences of \(q\) at the original and reflected eigenvalues. Strict convexity makes \(\alpha-\beta\) and \(\gamma-\eta\) have opposite signs. Their weighted elimination controls both \(A-C\) and \((\lambda_i+\lambda_s)A-(\lambda_i+\lambda_r)C\). Repeated eigenvalues are handled without dividing by a spectral gap.
3. Wick expansion and row-column Cauchy–Schwarz give \(\mathbb EL^2\preceq KI\), \(\mathbb EL^4\preceq3K^2I\). The crossing Wick term need not be positive. These operator bounds control every slot acting on a fixed tensor, including the input slot whose Gram operator need not be capped.
4. Let \(J\) swap slots two and three, \(S=(I-J)\mathsf X\), \(Z(x)=(I-J)(L_1+L_2)\mathsf X\), and \(\Pi=1_{[-R,R]}(L)^{\otimes3}\). The projection union bound gives tails \(12K^2m/R^2\) for \(S\) and \(144K^3m/R^2\) for \(Z\). After the paired local estimate and Gaussian reflection,
   \[
   \|S\|^2/m\le8a_R^{-2}t+12K^2/R^2,
   \quad \mathbb E\|Z\|^2/m\le4M_Rt+144K^3/R^2.
   \]
   No cutoff is differentiated, and no rare full-spectrum event is assumed.
5. With the vector convention \(S_{rs}=X_re_s-X_se_r\), direct polynomial expansion gives
   \[
   Z_{\cdot rs}(x)=[X_r,X_s]x+
   \sum_vx_v(X_rS_{vs}-X_sS_{vr}+X_vS_{rs}).
   \]
   Gaussian coefficient orthogonality and the family cap imply
   \(\sum_{r,s}\|[X_r,X_s]\|^2\le2\mathbb E\|Z\|^2+18K\|S\|^2\).
   Also \(\|\mathsf X-\operatorname{Sym}\mathsf X\|^2=\|S\|^2/3\).
6. Combining these bounds yields the displayed infimum. First taking \(R\) large, then \(t\) small, proves the uniform vanishing modulus. The scalar lower bounds give \(F_K(R)\le C(1+K)e^{52R^2}\); choosing \(R^2=\log(1/t)/104\) for sufficiently small \(t\) yields the logarithmic rate. The elementary bound \(K+4K^2\) covers the remaining range. If \(K=0\), every matrix is zero.

The pinned entropy manuscript supplies the actual Mills function, the transport/normalization setting, divided-difference and tensor-rotation operations, and the retained near-equality slack. Mahler's linear-rigidity proof supplies a related positive spectral-measure mechanism. The tracial Gamma and Kadison–Kastler companions already contain fourth-moment clipping and row-column tools. These operations and classical matrix calculus are explicitly credited, not claimed as discoveries. Exact source ranges and blob identities are retained in the [I64 evidence](../sources/i64_entropy_coefficient_extraction_novelty/).

## Symmetric repair and upstream application

For \(K>0\), put \(T=\operatorname{Sym}\mathsf X\), \(e^2=\|T-\mathsf X\|^2\). I61 §5 constructs a fully symmetric tensor \(W\) such that
\[
B_W\preceq4KI,\quad \|W-\mathsf X\|^2\le26e^2,
\quad \|B_W-B\|^2\le234Ke^2,
\]
\[
\sum_{r,s}\|[W_r,W_s]-[X_r,X_s]\|^2\le936Ke^2.
\]
Specifically, project \(T\) in all three slots by \(P=1_{[0,4K]}(B_T)\). The original first-flattening cap pays the discarded mass: if \(k=\operatorname{rank}(I-P)\) and \(a=\|(I-P)T\|\), then \(2\sqrt{Kk}\le a\le e+\sqrt{Kk}\), hence \(a\le2e\). The three-slot projection loses at most \(3a^2\). Ordinary Gram and commutator perturbation estimates give the other constants. This technical repair is part of R014, not another finding.

For the normalized smooth transport class in I59/I61, provided the original coefficients satisfy the same fixed cap, write \(u=\delta/m\), where \(\delta\) is the sharp entropy deficit. The audited source application gives
\[
t\le A_Ku,\quad \beta=\|B-I\|^2/m\le2000u/c_K,
\quad \eta=E_X/m\le\chi_K(A_Ku),
\]
with \(A_K,c_K>0\) depending only on \(K\), as defined in I61 §§2 and 8. Consequently
\[
\frac{\|B_W-I\|^2+\sum_{r,s}\|[W_r,W_s]\|^2}{m}
\le2\beta+(2+2340K)\eta.
\]
This is the new upstream-enabled use: a dimension-uniform reduction of capped near entropy equality to an approximately normalized, approximately associative symmetric tensor. It does not yet give distance to one globally oriented exponential-product law.

## Significance and remaining limits

The contribution is control of the original pencil's total algebraic residual from averaged nonlinear curl, uniformly while both dimension and family size grow. A single divided-difference measurement can vanish by cancellation while the coefficient symmetry error remains nonzero. Existing positive spectral-surplus estimates do not start with this antisymmetrized measurement. The paired elimination pays that missing comparison.

I64 explicitly compares Bathory's paired nonlinear derivative estimates and commutator-surplus calculus, Gaussian Hodge projection, incompatible-tensor inequalities, almost-commuting matrix families, odeco tangent equations and approximate algebra results. The parent read the closest paired-conjugation proof and the full-gradient surplus calculation. The former controls an inner product of whole matrix transforms; the latter assumes a full-gradient surplus. Neither directly controls these projected tensor measurements. Fourth-moment clipping, the repair and logarithmic optimization remain credited technical ingredients. The bounded comparison does not exclude a shorter proof or establish worldwide priority.

Global algebra rounding AR remains unproved and unrefuted, even at exact \(B=I\). Original uncapped heavy directions remain unresolved. Source approximation of laws does not preserve the new coefficient cap. The unrestricted entropy target U and its proposed square-root law-distance rate are not proved. Generic channel countermodels are not counterexamples to the linked tensor problem. All further consequences of this coefficient bridge count once within R014.

## Validation

- [I61 parent evidence](../experiments/i61-parent-verification.json): the author evidence and diagnostics reproduce; the proof is preserved unchanged.
- [I63 parent reproduction](../experiments/i63-parent-verification.json): 102 sealed artifacts, 33,917 independent exact assertions, ten PDF text replays and unchanged I61 replay. The written review, rather than finite computations, supplies the original-proof PASS.
- [I64 parent reproduction](../experiments/i64-parent-verification.json): 137 sealed artifacts, eighteen inputs, 26 pinned files, 450 prior evidence hashes, 49 read contracts, 62 passages, 36 primary requests (35 successful and one retained timeout), twenty PDF text replays and 18,051 independent exact assertions. All 9,340 corpus files match the complete 749-manuscript tree. I61 and I63 replay unchanged. One PDF font warning is preserved; extracted text matches exactly.

Expected drift of the four parent ledgers is reported separately; no author artifact or old seal is rewritten. Candidate commit: `e0f1fcc2`; original-proof integration: `8c013c14`. This acceptance and I64 integration receive their own commit, published through the authorized project-only history filter.
