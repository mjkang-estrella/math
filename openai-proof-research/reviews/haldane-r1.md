# PD1 — independent referee report, round 1

Date: 2026-10-08. Scope: section 1, PD1, of `proposals/probability_dynamics.md` only. No earlier reviews were supplied. The pinned OpenAI theorems are accepted as premises; their proofs are not being audited.

**Verdict: ACCEPT the mathematical corollary, with minor presentation and literature corrections below.** Equations (1)–(5) have the stated constants and are proved under the accepted hypotheses. I found no missing factor of two, invalid operator inequality, or illegitimate thermodynamic-limit passage. Acceptance concerns a valid model-specific deduction, not demonstrated publication novelty.

The reviewed section, from `## 1.` up to but excluding `## 2.`, had SHA-256 `9e7a0500a05f05e7e9c4ebed744237e17936c0d0d85241cbef20a3265b69508b`. Only this review file was written; no proposal, source, experiment, or shared index was changed.

## 1. Premises and canonical source check

`sources/upstream.json` pins `openai/math` at **`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`**. I read the actual periodic manuscript's introduction, assembly, and model statements, rather than relying on the catalogue.

- [`preprints/The-periodic-spin-one-Haldane-gap-September-24-2026/build/introduction.tex`, Theorem `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-periodic-spin-one-Haldane-gap-September-24-2026/build/introduction.tex) supplies uniqueness for even $L\ge60$, and the full spectral gap $\gamma_L>\delta=\log(20)/784$ for even $L\ge2304$. Thus both properties apply throughout PD1's range. The Hamiltonian has coupling one and self-adjoint spin-one generators with Casimir $2I$.
- [`build/assembly.tex`, Corollary `cor:local-limit`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-periodic-spin-one-Haldane-gap-September-24-2026/build/assembly.tex) supplies local-limit existence and a local gap inequality for every such limit. Its closing paragraph expressly does not identify different subsequential limits. PD1 needs only compactness and convergence on local observables for its limiting moment claims.

Both canonical URLs returned HTTP 200 and matched the local cached files byte for byte. The assembly file's SHA-256 is `d7c1415b78c2d2b6d1cf00f38fa578e1e1c1075b50f3342186380855afbd0eb3`.

**Reported malformed assembly link:** it is not present in the version I inspected. Its commit component already equals the canonical revision above. The assembly URL displayed here is the exact replacement to use if integrating an older version with the repeated hash segment; no link edit is needed in the inspected version.

For the companion check, I inspected the boundary-field manuscript's main theorem, conclusion, and topology section, including [`build/sections/topology.tex`, Corollary `cor:topology`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-boundary-field-gap-for-the-spin-one-Heisenberg-chain-September-24-2026/build/sections/topology.tex). These concern boundary-selected odd open chains and their index, not PD1's block MGF or response estimates. No duplicate of PD1 was found in these checked statements. This is a bounded companion check, not an assertion about every upstream manuscript.

## 2. Symmetry and quadratic estimates

### Singlet invariance: correct

For every global rotation $U(g)$, commutation with $H_L$ and uniqueness imply $U(g)\Omega_L=\chi(g)\Omega_L$. The restriction is a continuous one-dimensional representation of $SU(2)$; it is trivial. Differentiation gives

\[
S_{\mathrm{tot}}^\alpha\Omega_L=0,
\qquad S_{\mathrm{tot}}^\alpha=\sum_jS_j^\alpha.
\]

Thus $\omega_L(S_j^\alpha)=0$, $\omega_L(A_a)=0$, and the full-block charge annihilates the ground vector. Uniqueness also gives translation invariance of the **state**; the translation eigenvalue of the vector need not be one. The proposal uses only state invariance and is correct on this point. Rotational invariance makes the three diagonal bond expectations equal, so

\[
\omega_L(X_j)=\frac{2e_L}{3},\qquad
X_j=S_j^xS_{j+1}^x+S_j^yS_{j+1}^y,
\quad e_L=E_0(L)/L.
\]

The two-site total-spin sectors $J=0,1,2$ give bond energies $\tfrac12J(J+1)-2=-2,-1,1$. Therefore $e_L\ge-2$, as used. No numerical ground-energy estimate is needed.

### Gap inequality and signs: correct

For self-adjoint $F$, the spectral gap gives

\[
\delta\operatorname{Var}_{\omega_L}(F)
\le\langle F\Omega_L,(H_L-E_0)F\Omega_L\rangle
=\frac12\omega_L([F,[H_L,F]]).
\]

The sign convention is fixed by

\[
[F,[H,F]]=2FHF-F^2H-HF^2.
\]

With $T_j=S_j^+S_{j+1}^-$, one has

\[
[A_a,T_j]=(a_j-a_{j+1})T_j,
\qquad
[A_a,[H_L,A_a]]=-\sum_j(a_j-a_{j+1})^2X_j.
\]

Hence the Dirichlet form equals $-e_LD(a)/3\le2D(a)/3$, proving (3). A nonempty proper contiguous block has exactly two crossing bonds, including a one-site block or its complement, and $D(\mathbf1_B)=2$. The resulting variance bound is $4/(3\delta)=348.940839127\ldots<349$.

### Response: correct as a finite-volume derivative

For fixed $L$ and real $a$, the ground eigenvalue remains simple in some neighborhood of $h=0$, by finite-dimensional isolated-eigenvalue perturbation theory. In the gauge $\langle\Omega_L,\Omega'_L\rangle=0$, differentiation for $H_L-hA_a$ yields

\[
E'_L(0)=0,\qquad
(H_L-E_0)\Omega'_L=A_a\Omega_L,
\]

and therefore

\[
-E''_L(0)=2\langle A_a\Omega_L,
(H_L-E_0)^{-1}_{\Omega_L^\perp}A_a\Omega_L\rangle
\le\frac{2}{\delta}\omega_L(A_a^2)
\le\frac{4}{3\delta^2}D(a).
\]

The inverse is positive, so the lower bound zero is also correct. The factor two is necessary and present. This is the response to the specified spatial field, not a positive-temperature fluctuation formula. The proposal correctly disclaims a size-independent interval of analyticity. For constant $a$, both sides vanish.

### Structure factor: correct

Write $Z_q=C_q+iT_q$, where $C_q=\sum_j\cos(qj)S_j^z$ and $T_q=\sum_j\sin(qj)S_j^z$. These commute, so $Z_q^*Z_q=C_q^2+T_q^2$. For the periodic momenta $q=2\pi k/L$,

\[
D(\cos(q\cdot))+D(\sin(q\cdot))
=\sum_j|e^{iq(j+1)}-e^{iqj}|^2
=4L\sin^2(q/2).
\]

Dividing the sum of two applications of (3) by $L$ gives exactly (5), including $q=0$ and $q=\pi$. The absolute square should mean $Z_q^*Z_q$; this natural interpretation is consistent with the proof. No infinite-volume structure-factor convergence or matching asymptotic has been established or is needed.

## 3. Exponential moments: complete constant audit

Let $F=e^{tQ_B/2}$ and $M(t)=\omega_L(F^2)>0$. For internal bonds, conservation of $S_j^z+S_{j+1}^z$ gives commutation with $F$; bonds outside $B$ also commute. Thus only the two crossing bonds contribute for a proper block.

On a crossing bond, put $\sigma=\mathbf1_B(j)-\mathbf1_B(j+1)\in\{-1,1\}$. Since $[Q_B,T_j]=\sigma T_j$, conjugation multiplies $T_j$ and $T_j^*$ by $e^{\sigma t/2}$ and $e^{-\sigma t/2}$. Factoring the double commutator between two copies of $F$ proves the exact identity

\[
[F,[h_j,F]]=-2\bigl(\cosh(t/2)-1\bigr)FX_jF.
\]

This is valid for either orientation and either sign of $t$. It does not treat $F$ and $X_j$ as commuting.

In total-$S^z$ sectors $\pm2,\pm1,0$, respectively, the self-adjoint $X_j$ has blocks

\[
(0),\qquad
\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\begin{pmatrix}0&1&0\\1&0&1\\0&1&0\end{pmatrix}.
\]

The eigenvalues are $0$, $\pm1$, and $0,\pm\sqrt2$, giving **$\|X_j\|=\sqrt2$**. Congruence preserves order, so $-FX_jF\le\sqrt2F^2$, even though $F$ and $X_j$ need not commute. Combining the factor $1/2$ in the gap identity, the factor $2$ in each bond identity, and two crossing bonds gives

\[
\delta\{M(t)-M(t/2)^2\}
\le2\sqrt2\bigl(\cosh(t/2)-1\bigr)M(t).
\]

There is no lost factor at this step.

For $|x|\le1$,

\[
\cosh x-1=\sum_{n\ge1}\frac{x^{2n}}{(2n)!}
\le x^2(\cosh1-1)<x^2.
\]

Thus $|t|\le2$ implies $\cosh(t/2)-1\le t^2/4$. With

\[
\tau=\sqrt{\delta/\sqrt2}=0.0519799633351962\ldots,
\qquad
\kappa(t)=\frac{2\sqrt2}{\delta}\bigl(\cosh(t/2)-1\bigr),
\]

one obtains $\kappa(t)\le t^2/(\sqrt2\delta)\le1/2$ throughout the closed interval $[-\tau,\tau]$. Equality at the last upper bound causes no problem: $1-\kappa\ge1/2>0$, and $-\log(1-u)\le2u$ holds for $0\le u\le1/2$.

Writing $g=\log M$, the resulting recursion is

\[
g(t)\le2g(t/2)+\frac{\sqrt2}{\delta}t^2,
\]

and its $n$-fold iteration is

\[
g(t)\le2^ng(t/2^n)
+\frac{\sqrt2t^2}{\delta}\sum_{k=0}^{n-1}2^{-k}.
\]

For each fixed finite $L,B$, $g(0)=g'(0)=0$ and analyticity imply $2^ng(t/2^n)\to0$. The Taylor remainder may depend on $L,B$; this is harmless because the dyadic limit is taken first at fixed $L,B$, leaving a bound whose constants are uniform. This proves (1). No uniform-in-volume Taylor expansion was assumed.

At the endpoint, $2\sqrt2\tau^2/\delta=2$. Hence $M(\tau),M(-\tau)\le e^2$. The two one-sided Markov inequalities give

\[
\omega_L(\mathbf1_{\{|Q_B|\ge r\}})\le2e^2e^{-\tau r}
\quad(r\ge0).
\]

Separately, scalar functional calculus gives $e^{\tau|Q_B|}\le e^{\tau Q_B}+e^{-\tau Q_B}$, proving the moment bound $2e^2=14.7781121978613\ldots$. **The endpoint exponential moment is not being inferred by integrating a tail at the same rate**, which would be insufficient. Empty and full blocks are trivial. The tail bound can exceed one for small $r$, which is valid; it may optionally be capped at one.

## 4. Thermodynamic-limit quantifiers

The valid assertion is:

> For every locally convergent subsequence of even periodic ground states with lengths tending to infinity, its limit state satisfies (1) and (2) for every fixed finite interval $I\subset\mathbb Z$, every real $|t|\le\tau$, and every $r\ge0$, with the same constants. Equation (3) holds for every finitely supported real coefficient family on $\mathbb Z$.

Use the centered-ring embedding from `cor:local-limit`, with the closing bond eventually outside each fixed support. For any fixed $I$, all functions of $Q_I$ in these statements, including its spectral projectors, belong to a fixed finite-dimensional local matrix algebra. They converge in expectation under local convergence. The discontinuity of an indicator as a scalar function is irrelevant: one is evaluating a fixed matrix projector, not taking a weak limit of varying random variables and applying a discontinuous test function.

For finitely supported $a$, use zero extension and $D_{\mathbb Z}(a)=\sum_{j\in\mathbb Z}(a_{j+1}-a_j)^2$; this agrees with the ring expression for sufficiently large rings. The same locally convergent subsequence works for all the claims. Convergence on an entire local matrix algebra already covers every $t,r$; no extra uncountable diagonal extraction is needed. Rotation invariance passes to the limit and gives the same assertions for every **unit** spin axis.

No conclusion here requires a unique or pure infinite-volume state, convergence of the full sequence, an infinite-block charge operator, identification with boundary-field limits, or interchange of field derivatives and volume limits. The finite-ring uniform estimate also applies to size-dependent blocks on those rings, but convergence of their distributions is a separate assertion. Equations (4) and (5) should remain explicitly finite-volume statements.


## 5. Literature and novelty qualification

The additional search covered ground-state exponential concentration, conserved-charge fluctuation area laws, block magnetization, and Poincaré-to-exponential-integrability arguments. Relevant primary sources and precise limitations are:

1. **Direct ground-state concentration precedent.** Kuwahara, Arad, Amico and Vedral, [*Local reversibility and entanglement structure of many-body ground states*, arXiv:1502.05330v3](https://arxiv.org/html/1502.05330), Section V, equation (7), derive exponential concentration for additive observables in unique gapped ground states. Their displayed projection-norm estimate has decay scale proportional to \(\sqrt{|I|/\mathrm{gap}}\). It is an important antecedent but does not, as stated there, give PD1's interval-length-independent rate. PD1 uses charge conservation to remove all interior-bond contributions. Add this substantially closer reference alongside the general quantum-concentration citation.
2. **Charge-fluctuation area laws are established background.** Song et al., [*Bipartite Fluctuations as a Probe of Many-Body Entanglement*, arXiv:1109.1001](https://arxiv.org/pdf/1109.1001), Section III.C, explicitly discusses constant fluctuation scaling in gapped one-dimensional systems and treats the spin-one AKLT chain. This supports the proposal's caution about area-law novelty. The AKLT example has a different interaction and does not establish the present pure-bilinear theorem.
3. **The concentration mechanism has classical antecedents.** Bobkov and Ledoux, [*Poincaré's inequalities and Talagrand's concentration phenomenon for the exponential distribution*, PTRF 107 (1997), 383–400](https://www.math.univ-toulouse.fr/~ledoux/Poincare.pdf), establish concentration and exponential-integrability consequences of Poincaré inequalities. This is precedent for the spectral-gap-to-concentration strategy, not a theorem being applied directly to the noncommutative ground state here.
4. **The existing Anshu–Metger reference is legitimate but broader.** [*Concentration bounds for quantum states and limitations on the QAOA from polynomial approximations*, Quantum 7 (2023), 999](https://arxiv.org/abs/2209.02715), treats shallow-circuit outputs, injective MPS, and specified Hamiltonian evolutions. Its abstract does not license applying an injective-MPS theorem to the exact Heisenberg ground state. PD1 does not make that application, so this is a citation-scope clarification, not a proof defect.

The checked sources do not demonstrate priority for the explicit pair of constants \((\tau,2e^2)\) in the pure bilinear model. Nor does failure to locate that exact pair establish substantive novelty: routine changes of constants are not a new principle. The defensible contribution is a self-contained, explicit, model-specific corollary of the accepted gap release. I found no exact duplicate in the checked sources, but a general conserved-charge concentration theorem could subsume it. The project should retain its explicit no-priority disclaimer.

## 6. Exact requested edits and validation disposition

These are minor refinements; **no change to (1)–(5), \(\delta\), \(\tau\), or \(2e^2\) is required.**

1. **Make the derivative assertion match the formula.** Replace “its derivative at zero is well-defined” with: “For fixed \(L\) and \(a\), \(E_L(h)\) is real analytic in a neighborhood of zero; in particular \(E_L''(0)\) exists.” Retain the existing disclaimer about a size-independent analyticity interval.
2. **Make the limit scope explicit.** Replace the last proof paragraph with the following, or append its qualifications:

   “Let \(\omega\) be any local limit along even lengths \(L_n\to\infty\). For each fixed finite interval \(I\), all the operators in (1) and (2) are bounded elements of its local matrix algebra, including the spectral projectors. Local convergence therefore preserves these inequalities for all \(|t|\le\tau\) and \(r\ge0\). Equation (3) likewise passes to every finitely supported real family \(a\), with \(D(a)=\sum_{j\in\mathbb Z}(a_{j+1}-a_j)^2\) after zero extension. Global rotation invariance passes to the limit and gives the assertions for every unit spin axis. Equations (4) and (5) are asserted here at finite volume. No uniqueness or purity of the limiting state is required.”
3. **Strengthen the concentration attribution.** Add the Kuwahara–Arad–Amico–Vedral Section V, equation (7), citation above, with this sentence: “Exponential concentration for additive observables in unique gapped ground states already follows from local reversibility; its displayed generic bound has a subsystem-size-dependent scale. The present calculation uses charge conservation to obtain a boundary-controlled scale for this model.” Preserve the existing disclaimer that a general conserved-charge version may already exist.
4. **Qualify the release-dependent claim.** Replace “a proof with no unproved gap hypothesis” with “a deduction whose gap input is the pinned theorem accepted in this project, rather than an additional model conjecture.” This states accurately what was validated without auditing upstream truth.
5. **Canonical assembly link.** Use the canonical URL in section 1 of this review if repairing an older proposal. In the inspected file this correction is already satisfied.

Validation performed: the supplied standard-library experiment passes. Independently, I constructed the two-site interaction in the orthonormal spin-weight basis and checked all entries of the weighted identity as polynomial coefficients in the two real weights. I checked the exponential identity as a Laurent-polynomial identity in \(r=e^{t/2}\) for both crossing orientations, and checked internal-bond conservation. All passed. The displayed fixed-total-spin blocks establish the operator norm analytically. The MGF recursion, its endpoint, centering, response denominator, Fourier normalization, and local-limit argument were then verified directly as above. These checks validate the new deduction; none purports to test the accepted upstream gap.
