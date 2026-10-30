# Matrix-disk contribution review, round 1

2026-10-14. Independent primary-literature contribution review of the attained complete matrix-polynomial disk package. This is not a proof acceptance, not a count increment, and not a worldwide-priority certificate. The author's handoff and the parent's preliminary read are not gates. Exact algebraic checks in the discovery directory support finite identities only.

## Verdict

**SUBSTANTIAL**, for one package: arbitrary finite base dimension, arbitrary finite coefficient size and degree, attained equality for a specified matrix polynomial, the fixed polynomial unitary coefficient channel on each irreducible attaining block, its rational exterior inverse, and the full determinant lemniscate of that block. The disk conclusion for the whole numerical range is the last line of that package.

No primary statement read here already asserts this package. No explicit reduction assembled from those statements preserves every quantifier in it. The unpaid steps are in the section "Unpaid bridge". Jin's scalar theorem, Jin's geometric circle criterion, the Åhag–Czyż–Virtanen complete theory through dimension three, R016, the dimension-five technical extension, and R019 stay antecedents.

Acceptance still waits on a separate adversarial proof review and on parent integration. This file does not accept the candidate. A gap in the Fatou passage, the factor one half, the ordinary transpose, or the circle-criterion interface would leave the package unproved. Substantiality does not fill that gap.

## Statement under review

Primary text: `frontier/campaigns/2026-10-14/matrix-disk-discovery/analysis.md`, SHA-256 `e74dda6b866d7780b57911aef30a2bfb99589e7036864b1da6a302072ab462b6`, 18601 bytes. Sections 1 and 9.

For every finite \(n,m\ge 1\), every \(A\in M_n(\mathbb C)\), and every finite \(m\times m\) matrix polynomial \(F\), put \(M=\max_{z\in W(A)}\|F(z)\|\) in Euclidean operator norms, with base-first evaluation \(F[A]=\sum_k A^k\otimes C_k\). If \(M>0\) and \(\|F[A]\|=2M\), then \(W(A)\) is a nondegenerate closed disk.

On any unitarily irreducible reducing block \(B\) with \(\|F[B]\|=2M\), after normalizing \(M=1\), there are fixed coefficient subspaces \(E,G\) of equal positive dimension \(r\), constant isometries \(U:\mathbb C^r\to E\) and \(V:\mathbb C^r\to G\), and an \(r\times r\) polynomial \(J(z)=V^*F(z)U\) such that \(J\) is unitary at every point of \(\partial W(B)\), \(\det J\) is nonconstant,

\[
\{z:|\det J(z)|<1\}=\operatorname{int} W(B),\qquad
\{z:|\det J(z)|=1\}=\partial W(B),
\]

and \(J(z)^{-1}\) is rational, analytic off \(W(B)\), continuous up to that boundary, and zero at infinity. These are determinant and matrix-channel conclusions. No constant scalar channel \(v^*Fu\) is asserted.

No simple-support hypothesis, boundary-regularity hypothesis, scalar coefficient channel, or dimension bound is imposed. No holomorphic or rational witness, nonattained complete supremum, quantitative near-equality modulus, or classification of every matrix with disk numerical range is claimed. Pinned OpenAI mathematics at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated and is not re-audited. The actual direct and structural statements used below were read.

## What a technical reduction had to preserve

A technical verdict would require an explicit deduction of the whole package from older theorems such that all of the following survive:

- every finite base dimension and every finite coefficient size and degree;
- attainment by the specified polynomial \(F\), rather than by some other scalar or matrix function;
- fixed coefficient subspaces, possibly of rank greater than one, and one polynomial \(J\) unitary on the boundary of each irreducible attaining block;
- a rational exterior inverse of \(J\) vanishing at infinity;
- the full lemniscate identities, with no extra exterior component;
- restoration of every inactive reducing block;
- passage through the outer analytic approximation without a uniform strict contraction gap.

Each route below drops at least one of these. The closest machines are recorded first.

### 1. Jin's scalar theorem, then a circle criterion already inside its proof

Jin, *Rigidity at the Extremal Crouzeix Constant*, preprint 202609.0079, version 2, Theorem 1: for every \(N\ge 1\) and every \(A\in M_N(\mathbb C)\), \(\psi(A)=2\) implies that \(W(A)\) is a nondegenerate closed disk. Here \(\psi\) is the scalar functional-calculus constant. Lemma 7 produces a scalar finite Blaschke extremizer from that scalar supremum, including from a nonpolynomial \(H^\infty\) extremizer. Proposition 3 collapses that scalar function to a reduced rational function \(U/V\). Proposition 4 identifies its full unit level set with the boundary. Proposition 6 is the circle criterion. Corollary 1 is holomorphic scalar equality under an interior-spectrum hypothesis.

Theorem 1 does not take a matrix polynomial as input. Åhag–Czyż–Virtanen, arXiv:2608.27346v4, introduction, record that both Jin's scalar argument and the Lorist–Schwenninger scalar argument state that their methods do not yield the completely bounded inequality. The obstruction they attribute to Lorist–Schwenninger is a commutativity hypothesis lost under matrix amplification. arXiv:2608.03841 was not reopened in this round; that sentence in v4 is the interface.

Proposition 6, read in the retained Sections 1–8 extract and matched against the live v2 rendering, assumes a compact convex body whose boundary is the full level \(|U/V|=1\) for coprime polynomials with \(\deg U>\deg V\), strict convexity, nonvanishing derivative on that boundary, and the Hermitian tangent condition \(\det(sI+uH+vJ)=0\) on an open arc. Those hypotheses are real, and convex polynomial lemniscates without the Hermitian condition are outside the criterion. The candidate invokes Proposition 6 only after it has built \(\det J\). Proposition 6 does not build \(J\).

The scalar collapse \(f=2a/c\) in Jin's Proposition 3 uses one pair of scalar equality vectors. It does not produce fixed subspaces of a specified matrix polynomial, and it does not survive a witness whose every constant scalar compression misses equality.

### 2. Complete constant equals scalar constant, then Jin

Åhag–Czyż–Virtanen v4, Theorem 1.6: if the base dimension is at most three, then \(\psi_{\mathrm{cb}}(A)=2\) if and only if \(\psi(A)=2\). Corollary 12.4: if the dimension is at most three and \(W(A)\) is not a nondegenerate disk, then \(\psi_{\mathrm{cb}}(A)<2\). The proof quotes Theorem 1.6 and Jin's Theorem 1. Corollary 12.5 classifies the \(3\times 3\) equality cases. The introduction states the resulting complete disk conclusion for dimensions at most three and, separately, the all-dimensional scalar polynomial classification in Theorem 12.2.

Version 3's Section 11, read in full from the retained extract, has the same division of labor. Proposition 11.1 and Theorem 11.2 classify scalar polynomial equality in every finite dimension: after an affine change, the polynomial is a monomial and the matrix has a reducing Crabb–Choi–Crouzeix block. Corollary 11.4 is the complete disk statement for dimension at most three. Theorem 11.7 is a scalar holomorphic statement with the extra hypothesis \(\operatorname{alg}(f(A))=\operatorname{alg}(A)\), and its conclusion is that the domain is a disk and \(f\) is linear. Proposition 11.9 is a Jordan-block constraint for a scalar extremizer. None of these is a matrix-polynomial theorem in arbitrary dimension.

Version 4, Theorem 5.3, still supplies a minimal rectangular extremal of some cb-norm greater than 1, with \(r+s\le d\) and orthogonal Schmidt families. The introduction's display (1.4) uses that reduction only to locate a possible failure of the inequality above 2, and only at levels with \(r,s\ge 2\). Once the complete bound is known, that display does not fire. At the value 2, both scalar levels and genuinely rectangular levels remain possible. R019 is a \(2\times 2\) polynomial on a \(6\times 6\) irreducible disk matrix with \(\|P[N]\|=2\) and no constant scalar compression of that same \(P\). Theorem 5.3 does not forbid that configuration, and it does not return a rational exterior inverse or a full lemniscate.

The square-function rigidity in the v4 introduction is also scalar: an operator attaining norm 2 under the \(\tau=1/2\) square-function bounds has a reducing copy of \(\begin{psmallmatrix}0&0\\2&0\end{psmallmatrix}\). That operator is a scalar functional-calculus value, not \(F[A]\).

### 3. Same-witness scalarization through dimensions four and five

R016, accepted, states the disk and a constant scalar channel \(p(z)=v^*Pu\) for every specified equality witness through base dimension four. Its rank step uses a simple top support eigenvalue, rank \(d-1\) of the positive boundary field, and the isotropic bound on \(XX^*-YY^*\). I245 records that this exterior limit and residual extraction are dimension-independent, and that the dimension enters only in the simple-support step. The parent note `crouzeix-five/analysis.md` replaces that step in dimension five by Leake–Lins–Spitkovsky, Theorem 5.7, and keeps the same scalar channel. The note labels itself a technical deduction and asks for no new-result credit. This review agrees. It is not recounted.

R019, accepted, is an irreducible \(6\times 6\) example with exact matrix-polynomial attainment, Schmidt rank two, and every constant unit compression of that polynomial strictly below 2. The optional scalar deduction in I287 shows that each individual scalar polynomial misses equality on that disk. It does not prove \(\psi(N)<2\), and it does not prove a nondisk theorem. I292 already judged the example substantial as an obstruction to unrestricted same-witness scalarization. The amplification hierarchy and the strict scalar-gap question remain that old distinction.

I245, Section 8, notes that a matrix Schur function with a constant unitary channel defeats a scalar maximum-principle shortcut before rank reduction, while the dimension-four rank argument still applies. That sentence explains why R016 scalarizes. It does not construct a higher-rank polynomial \(J\), an exterior inverse, or a determinant lemniscate, and it stops at dimension four.

Extending the simple-support search past dimension five would still require a simple top eigenvalue. R019 has no such eigenvalue in any direction. A reduction that needs one cannot preserve arbitrary dimension.

### 4. Equality case of the pinned direct estimate, read off the published chain

The pinned direct manuscript, local `direct.tex`, Theorem `thm:domain` and Proposition `prop:coefficients`, proves \(\|F[A]\|\le 2\) on an analytic convex neighborhood. The diagonal test at lines 399–406 chooses \(C_0=\overline{P_0}\) and \(C_k=\overline{P_k}/2\), then replaces the boundary norm by the upper coefficient bound. The resulting inequality \(d_N\le a^2/\gamma^2\) can saturate at \(\gamma=2\) without a recorded contraction defect. The positive-block comparison gives an integrated inequality, not constancy of the diagonal resolvent compressions and not a rational cross channel.

The outer-approximation section passes the bound from neighborhoods to an arbitrary compact convex numerical range. It contains no equality-case theorem. The Markov kernel and both unit marginals are present, as nonnegative ingredients of the upper bound. The manuscript does not form the triple variance integral, pass it to the limit by Fatou, or conclude that an arbitrary-rank diagonal field is constant.

The structural companion, local `structural.tex`, Theorems `thm:structural` and `thm:representation`, attains an optimal similarity of condition number \(\kappa\le 2\) and one positive boundary density for the similar matrix. Its endpoint extremal produces a contractive rational disk function for that metric problem. The abstract and the two main theorems are bound and representation statements. They do not classify numerical ranges on which a specified polynomial attains the value 2, and the density is not the original resolvent field used by the candidate. I292 already separated this construction from the R019 witness. The same separation applies here.

### 5. Inner polynomials, Grunsky equality, and special families where the two constants agree

A square polynomial that is unitary on the unit circle has determinant a unimodular monomial. That classifies an inner polynomial after the boundary is already a circle. It does not start from an arbitrary compact convex set and an arbitrary attaining \(F\). Crouzeix, *Some constants related to numerical ranges* (2016), Lemma 10.1, characterizes the closed unit disk by a determinant identity in the Ando factorization. The interface read here is that lemma as reproduced in the public PDF text. It constrains matrices whose range is already the disk. It does not extract \(J\) from a complete witness on an unknown range.

Beckermann–Stylianopoulos, arXiv:1606.00553, record the Grunsky coefficient inequality and the area form of its equality case. The direct manuscript cites the weighted form of that calculus as the source of a non-strict coefficient bound. Equality in the Grunsky inequality is a univalence or area statement for the exterior map. It is not the assertion that a matrix polynomial attaining the complete Crouzeix constant forces a circular numerical range.

Crouzeix–Greenbaum, arXiv:2508.12768, Theorem 2, as read from the preprint text: for the weighted-shift family \(M=P_d\operatorname{diag}(\alpha_1,\ldots,\alpha_d)\), one has \(\psi(M)=\psi_{\mathrm{cb}}(M)\le 2\), and both constants are strictly less than 2 when the product of the weights is nonzero. This equates the two constants on one classical family. It does not treat an arbitrary matrix or a specified polynomial of coefficient size greater than one.

Knese's realization theorems were compared in I292 for the R019 polynomial. A contractive colligation reproduces an inner factorization. It does not decide the numerical range of an unrelated attaining block. That comparison is not reopened as a new reading in this round.

## Unpaid bridge

The following steps are the part of the argument that the sources above do not contain. They are one bridge, and they are the content to which this substantiality verdict attaches. Correctness of the steps is for the proof gate.

1. **Retain the Hilbert–Schmidt Markov defect inside the optimal finite diagonal test.** For the direct manuscript's kernel \(K_j\) and the finite test \(G_{jN}\) with coefficients \(\overline S\) and \(\overline{A_{kj}}/2\), the Faber decomposition gives \(\|G_{jN}\|_{\partial}^2=d_{jN}-\delta_{jN}\), with \(\delta_{jN}\) the contraction defect of the Markov operator. The ordered test then reads \(\gamma_j d_{jN}\le a_j\|G_{jN}\|_{\partial}\), hence \(\gamma_j^2 d_{jN}^2\le a_j^2(d_{jN}-\delta_{jN})\). The published chain stops one step earlier, at the upper coefficient bound, where this defect is invisible. Sending \(N\to\infty\) at fixed \(j\), then using the inherited residual vanishing \(E_{Xj}\to 0\), forces \(\delta_j\to 0\). No uniform spectral gap of the operators \(T_j\) is required for that scalar limit.

2. **Pass the defect through moving outer domains by the variance integral and Fatou.** The two marginal normalizations give the nonnegative triple identity for \(\|u_j(\lambda)-u_j(\nu)\|_{\mathrm{HS}}^2\). Along an almost-everywhere subsequence, uniform convergence and injectivity of the exterior maps produce the limiting kernel pointwise off the diagonal. Fatou yields vanishing of the limiting integrand. Jin's Lemma 8, whose hypotheses are interior spectrum and nonempty interior, supplies one curved exposed analytic arc. On that arc the limiting kernel is positive for almost every other angle, because a support line at a different boundary point cannot contain the exposed point. Thus the diagonal test function is constant, and its zero mean makes \(X^*RX=S\) and \(Y^*RY=T\) almost everywhere. The argument does not use rank one. It is compatible with the disk kernel and with R019.

3. **Rationalize the original cross channel from the scalar trace.** The trace \(r(z)=\operatorname{tr} X^*(zI-B)^{-1}X\) satisfies \(q\,r\circ h=1\). Accretivity of a separated resolvent keeps \(r\) zero-free off \(K\), and the boundary lower bound extends by continuity. The cross field \(C(z)/r(z)\) is therefore rational off \(K\), continuous up to the boundary, and \(O(z^{-1})\) at infinity. The vanished block slack then fixes the kernel and range of this boundary field: they are the ranges of the constant Gram matrices \(S\) and \(T\), of some common positive rank \(r\).

4. **Turn the constant ordered test into a polynomial unitary channel with exterior inverse.** Equality for the constant test \(\overline S\) produces the boundary identity \(F(h)\overline S=\tfrac12\overline M\). The fixed ranges of \(\overline S\) and \(\overline T\) therefore carry an \(r\times r\) polynomial \(J\) which is unitary on the boundary. The same identity, with the ordinary transpose required by entrywise conjugation, defines a rational \(Q\) off \(K\) with \(Q(\infty)=0\) and \(JQ=I\) on the boundary, hence as rational functions. Rank greater than one is allowed. This is why the construction does not contradict R019 and does not assert a constant scalar channel.

5. **Pay the full lemniscate, then quote Proposition 6, then restore inactive blocks.** The exterior maximum principle for \(Q\), using \(Q(\infty)=0\), gives \(\|Q\|<1\) off \(K\). With \(\|J\|\le 1\) on \(K\) and \(\|J\|=1\) on the boundary, \(f=\det J\) satisfies the two full level identities. Nonvanishing of \(f'\) and absence of boundary segments then give a smooth strictly convex oval. The support lines of \(W(B)\) satisfy the Hermitian determinant condition for \(\operatorname{Re} B\) and \(\operatorname{Im} B\). Proposition 6, with \(U=f\) and \(V=1\), returns a circle. A polynomial of constant modulus on that circle is a monomial, so \(|f|\le 1\) on the whole \(W(A)\) forces every inactive summand into the same disk.

Steps 1–4 are the unpaid passage from a specified complete witness to a determinant that can enter Proposition 6. Step 5 applies credited geometry and the standard monomial form of a polynomial finite Blaschke product. The geometry and the monomial are not a second discovery.

## What this verdict does not award

- The complete bound \(\|F[A]\|\le 2\max\|F\|\), the Faber kernel, both marginals, the ordered tests, and the outer approximation are the pinned direct manuscript. The optimal similarity and the similar-matrix density are the structural companion.
- Scalar disk rigidity in every finite dimension is Jin, Theorem 1. The circle criterion, its projective contact count, and the curved-arc lemma are Jin, Propositions 5 and 6 and Lemma 8.
- Scalar polynomial equality in every finite dimension, including the monomial and Crabb–Choi–Crouzeix block, is Åhag–Czyż–Virtanen, v4 Theorem 12.2, already present as v3 Theorem 11.2.
- Equivalence of the scalar and complete constants, and complete disk rigidity, through base dimension three, are v4 Theorem 1.6 and Corollary 12.4.
- Same-witness scalarization through dimension four is R016. The dimension-five extension is the parent technical note. The rank-two disk witness without a constant scalar channel is R019.
- The Kippenhahn support determinant, the variance identity for one fixed doubly stochastic kernel, and the fact that a polynomial finite Blaschke product is a monomial are classical inputs inside the bridge. None of them, quoted alone, preserves the package.
- Equality of \(\psi\) and \(\psi_{\mathrm{cb}}\) for Choi's weighted shifts is Crouzeix–Greenbaum, arXiv:2508.12768, Theorem 2.
- The seventeen exact checks in `checks.json` certify finite identities and mutations for the R019 interface, the factor one half, the transpose, and a two-point variance normalization. They do not prove the outer limit, Fatou's passage, Proposition 6, or the theorem.

## Relation to the proof gate

No proof verdict is issued. The inherited exterior convergence and residual vanishing are used at the scope already stated in I245 and R016: dimension-independent, before the simple-support step. This review did not re-audit that argument and did not re-execute `check.py`.

The literature comparison is independent of whether every limit in analysis Sections 4–7 is correct. In particular, this file does not certify almost-everywhere convergence of the kernels, positivity on the curved arc, nonvanishing of the trace, the ordinary transpose in \(Q\), or the identification of Proposition 6's full-level hypothesis with \(\det J\). Those are the proof gate's pressure points. If one of them fails, the package is not established.

## Limits

No worldwide priority is claimed. The searches were bounded: the pinned direct and structural manuscripts, Jin v2, Åhag–Czyż–Virtanen v3 Section 11 and v4 through its stated complete and scalar equality theorems, R016, R019, I245, I291, I292, the dimension-five note, and targeted queries for an all-dimensional complete equality theorem. Absence from that search is not a proof that no other paper exists. Details and unread ranges are in `sources.md`.

The disk conclusion is not, by itself, a second result beside the channel. The holomorphic and nonattained problems remain open, including the question whether \(\psi_{\mathrm{cb}}(A)=2\) implies \(\psi(A)=2\) in dimensions greater than three. R019 does not settle that comparison.
