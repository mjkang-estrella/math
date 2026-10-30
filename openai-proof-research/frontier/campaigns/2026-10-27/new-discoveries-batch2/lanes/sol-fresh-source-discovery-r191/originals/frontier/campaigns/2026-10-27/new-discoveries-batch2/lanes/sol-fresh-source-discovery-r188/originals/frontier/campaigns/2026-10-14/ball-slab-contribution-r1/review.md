# Ball–slab second-order contribution review, round 1

2026-10-14. Independent contribution review of the frozen second-order ball–slab candidate. This file does not certify the proof, does not accept the candidate, and does not increment a count. Upstream theorem truth at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated. A separate proof gate is active; nothing below is a proof PASS.

## Verdict

**TECHNICAL, conditional on validity.**

The full all-BV lower bound does not merit a separate frontier result beyond R018. After the credited minimizing replacement, every low-energy ball-localized competitor is a centered \(C^1\) graph pair with energy \(O(S)\). On that class the proposed expansion is the Robin constant of four shrinking circles for the Jacobi/Dirichlet form R018 already uses, evaluated at the parabolic radius selected by inverting Lacasse–Grest–Levine (29), with the nonlinear area remainder brought below \(T_2\) by interpolating the Hölder seminorm already stated in Acerbi–Fusco–Morini Theorem 4.2. That is standard Green-kernel bookkeeping. The coefficient \(2\pi\) and the log–log inversion are not new. Formula (D) is the algebraic comparison of that expansion with I346’s exact cylinder value \(g(R)\).

The hardest new deduction, stated in full below, is real and is still inside that bookkeeping. It is the step a proof gate has to check. It is not a new singular capacity mechanism, a new vanishing mode, or an unpaid bridge of the kind that made R018 substantial.

Validity is open. If the uniform trace compliance or the interpolated remainder fails, the second-order claim is unpaid. The credited leading law must not be redescribed as (A).

## Statement under review

Primary text: `frontier/campaigns/2026-10-14/ball-slab-second-order/candidate.md`, SHA-256 `30bb73d2601754dcc6aa9eb26537e083256849acd3b5cf94a710970dfe067e54`, 24763 bytes. On-disk bytes match the assignment and the candidate’s `provenance.json`.

On the unit cubic flat torus, \(P\) is De Giorgi perimeter. For \(R<1/3\) and small \(\varepsilon>0\),

\[
L_R(\varepsilon)=\inf\bigl\{P(E)+P(F)-4\pi R^2-2:
E\subset F\text{ a.e.},\;|E|=4\pi R^3/3,\;|F|=2(R-\varepsilon)\bigr\},
\]

over all finite-perimeter pairs. No symmetry, smoothness, topology, connectedness, or graph restriction is imposed. Write \(\ell=|\log\varepsilon|\), \(S=\varepsilon^2/\ell\), \(T_2=\varepsilon^2\log\ell/\ell^2\), \(\delta=1/3-R\), and

\[
g(R)=2\pi\sqrt{4R^3/3}-4\pi R^2.
\]

\(M_B\) is the same infimum with the additional closed constraint that \(E\) lie within a fixed \(L^1\) distance \(\eta_0=(4\pi/81)/10\) of the compact orbit of radius-\(1/3\) balls. The outer set stays unrestricted inside that auxiliary minimum.

**(A).** Uniformly as \(R<1/3\) tends to \(1/3\) and \(\varepsilon\to 0\), with no relation between \(\delta\) and \(\varepsilon\),

\[
M_B(R,\varepsilon)=\frac{2\pi\varepsilon^2}{\ell+\log\ell}+O(\varepsilon^2/\ell^2).
\]

**(B).** \(M_B=2\pi S-2\pi T_2+o(T_2)\).

**(C).** For all sufficiently close parameters, \(L_R(\varepsilon)=\min\{M_B(R,\varepsilon),g(R)\}\). This identity is credited to I346.

**(D).** If \(R_\varepsilon<1/3\) tends to \(1/3\) and \((\delta_\varepsilon-3S)/T_2\to\alpha\in\mathbb R\), then

\[
\bigl(L_{R_\varepsilon}(\varepsilon)-2\pi S\bigr)/T_2\to\min\bigl\{-2\pi,(2\pi/3)\alpha\bigr\}.
\]

The \(O\) in (A) means a constant bound \(C\varepsilon^2/\ell^2\) for all sufficiently close parameters, with \(C\) independent of \(\delta/\varepsilon\) and of \(\delta/S\). No claim is made about the contact set of an exact minimizer, radial symmetry, a unique crossing, or coexistence.

## What each verdict had to mean

SUBSTANTIAL would require a singular lower passage that is not already paid by R018’s all-BV logarithmic contact law, and that is not the transcription of a classical contact inversion onto that law. TECHNICAL is the class for a quantitative closure of a paid mechanism by the standard kernel, interpolation, and Taylor expansion of the area integrand. DUPLICATE would require a read theorem that states (A) or (D) on this class. UNRESOLVED would require the mechanism itself to be ambiguous, or a read theorem whose overlap could not be decided. Search silence is not a fifth verdict and is not a novelty certificate.

The full quantifiers stay in force: all finite-perimeter nested pairs, joint \(R\to 1/3\) with no rate restriction, and both the lower bound and the matching recovery at scale \(\varepsilon^2/\ell^2\). A radial or smooth-only reading is not substituted for that statement.

## Credited theory, with the error R018 actually leaves

### R018 / I275 / I277

R018, accepted on the fixed-radius theorem, states that for each fixed \(R\in(1/(2\pi),1/3)\) and all finite-perimeter nested pairs,

\[
\lim_{\varepsilon\downarrow 0}\ell\, L_R(\varepsilon)/\varepsilon^2=2\pi.
\]

I277 PASS covers that limit. I278 judged the sharp all-BV lower passage SUBSTANTIAL. The passage I278 isolated is I275 §§4–5:

- exact inclusion in one horizontal chart, with \(W=A\psi\circ F\) and the actual inverse parametrization;
- a spectral cutoff \(N\) fixed before \(\varepsilon\to 0\), so that degrees \(2\) through \(N\) are \(o(\varepsilon)\) and the high-mode curvature loss is an arbitrary relative factor \(\zeta\);
- circle averages at radius \(c\sqrt{\varepsilon}\), an outer radius of order one whose average is \(o(\varepsilon)\), and the annular inequality \(2\pi[m(a)-m(b)]^2/\log(b/a)\);
- positive parts \((s+h)_+^2+(s-h)_+^2\ge 2s^2\), so axial drift does not lower the leading coefficient.

The parameter order is part of the theorem: \(\zeta\), the chart radius, \(N\), and \(c\) are fixed, then \(\varepsilon\to 0\), then \(c\) and \(\zeta\) tend to zero. Each fixed positive \(\zeta\) or \(c\) leaves a relative loss. A relative loss of size \(\zeta\) changes the energy by \(\zeta\cdot 2\pi\varepsilon^2/\ell\). The second-order scale is \(T_2=\varepsilon^2\log\ell/\ell^2\), smaller by \(\log\ell/\ell\). The same proof therefore reaches the leading coefficient and does not reach (A). I275’s area remainder is \(o(\varepsilon^2/\ell)\), which is likewise too coarse to divide by \(T_2\).

I278 already recorded that the logarithm, equal sharing, annular capacity, and moving-contact Green couplings are classical, and that a smooth axial calculation alone is TECHNICAL. The substantial increment over R017 was the first all-BV passage through a shrinking two-point obstacle. That passage is now credited. It is not renominated.

### I346 and I283

I283 gives the explicit tube-in-slab competitor and \(0\le L_R(\varepsilon)\le g(R)\), with \(g(R)/\delta\to 2\pi/3\). It records that \(R018\) is not uniform at \(R=1/3\), and that a completed minimum of two branches would still need its own contribution judgment.

I346 proves, as a research theorem judged TECHNICAL in that record,

\[
M_B(R,\varepsilon)/S\to 2\pi,\qquad L_R(\varepsilon)=\min\{M_B(R,\varepsilon),g(R)\},
\]

uniformly as \(R\to 1/3\) and \(\varepsilon\to 0\), with the cylinder local minimum exactly \(g(R)\). The ball half repeats I275’s cutoff, annulus, and positive-part argument on a compact radius interval. The cylinder half is the spectral gap \(\min\{4\pi^2-81/4,243/4\}>0\) after translations are removed. I346 states that at the leading tie \(\delta/S\to 3\), higher-order terms can decide the class, and that no second-order tie rule is proved. Its own assessment is that the sharp logarithmic passage remains R018’s, and that there is no new vanishing Jacobi mode.

(C) is that identity. (D) is the tie rule I346 withheld, obtained by inserting (B) into (C) and expanding \(g(1/3-\delta)=(2\pi/3)\delta+O(\delta^2)\). Under \(\delta=3S+\alpha T_2+o(T_2)\) one has \(\delta=O(S)\) and \(\delta^2/T_2\to 0\), so

\[
(g(R)-2\pi S)/T_2\to(2\pi/3)\alpha,
\]

while (B) gives \(-2\pi\) on the ball side. The minimum of those two limits is algebra. It is the same comparison I346 already made at scale \(S\), read one order later.

## Primary statements that fix the coefficient and the inversion

### Lacasse–Grest–Levine

Lacasse, Grest, and Levine, arXiv:mtrl-th/9603005v1, Section III, read on the ar5iv HTML of that preprint from the two-plate setup through (32) and the small-compression discussion that follows. The parallel-plate droplet is axisymmetric. Compression and facet size satisfy

\begin{align*}
\varepsilon_{\mathrm{LGL}}&\approx -4X^2\bigl(\ln X+\tfrac12\bigr),&(27)\\
X&\equiv(\rho_f/2)^2,&(28)\\
\xi&\approx -2X\ln X,&(29)\\
f&=d\varepsilon_{\mathrm{LGL}}/d\xi\approx 4X,&(30)\\
\varepsilon_{\mathrm{LGL}}&\approx\tfrac14 f^2\bigl[k-\ln f\bigr],\quad k=2\ln 2-\tfrac12.&(31)
\end{align*}

Here \(\xi=(R-h)/R\) is the dimensionless plate compression and \(\varepsilon_{\mathrm{LGL}}\) is the relative excess area. Equation (29) is transcendental. Its small-root inversion is elementary: if \(u=-\ln X\) and \(\ell_\xi=|\ln\xi|\), then \(u=\ell_\xi+\ln\ell_\xi+O(1)\) and

\[
\varepsilon_{\mathrm{LGL}}=\xi^2/u\cdot\bigl(1-1/(2u)\bigr).
\]

The excess area \(4\pi R^2\varepsilon_{\mathrm{LGL}}\) is therefore

\[
4\pi\,\delta_{\mathrm{geom}}^2\big/\bigl(\ell_\xi+\ln\ell_\xi+O(1)\bigr)
\]

for a rigid-wall droplet whose one-sided compression is \(\delta_{\mathrm{geom}}\). The authors say there is no closed form for the energy as a function of \(\xi\); they then invert (31) numerically by the integral equation (32). The asymptotic inversion itself is the relation (29). It is classical. It produces the denominator \(\ell+\log\ell\) and the second term of size \(\varepsilon^2\log\ell/\ell^2\). Their calculation is rotationally symmetric, with rigid plates and one free droplet surface. It does not state an all-BV lower bound on the torus.

R018’s leading coefficient is \(2\pi\), half of this rigid-wall \(4\pi\), because the gap is shared by two free interfaces. I278 already treated that sharing as elementary. Once the leading free-interface coefficient is \(2\pi\varepsilon^2/\ell\), replacing \(\ell\) by \(\ell+\log\ell\) is the same inversion, and the \(O(1)\) inside the logarithm moves the energy only by \(O(\varepsilon^2/\ell^2)\), which is the remainder in (A). No independent coefficient sits at scale \(T_2\).

### Lv

Cunjing Lv, arXiv:1704.05830v2, HTML. Read the abstract and opening, the exact elliptic expressions (5)–(7), the highly compressed series (17)–(19) and (23)–(25), and the liquid-Hertzian section: (28)–(32) at fixed plate distance, and (35)–(39) together with (43) at fixed volume. The appendix derivations were not re-done.

Equation (29) is \(\xi=-\sigma^2\ln(\sigma/(2e^{1/2}))+O(\sigma^4\log(1/\sigma))\). The text then writes \(\ln\xi\approx 2\ln\sigma+\ln\ln(1/\sigma)\), which is the same log–log inversion, and says the pure square scaling \(\xi\sim\sigma^2\) is the linear model while the logarithm is required for the next precision. The fixed-volume surface energy (38) is

\[
U=4\pi x_2^2\gamma\Bigl[1-2(\hat x_2-1)-(\hat x_2-1)^2\ln\bigl((\hat x_2-1)/(2e^{5/2})\bigr)+\cdots\Bigr].
\]

This is an asymptotic expansion of one axisymmetric nonwetting droplet between rigid planes. It is a higher-order confined-drop precedent for the logarithm of the contact parameter. It is not a theorem over nested finite-perimeter pairs, and it does not force the contact set of the torus minimizer to be a round disk.

### What those formulas do not do

They do not prove (A). They do fix the formal scale \(a^2\log(1/a)\sim\varepsilon\) and the energy shape \(\varepsilon^2/(\ell+\log\ell)\). A contribution claim that consisted of extracting \(2\pi\) or of inverting \(\xi\approx-2X\log X\) would be a duplicate of R018 plus this classical inversion. The candidate’s own literature note says the same. This review agrees, and then asks whether the all-BV closure at that scale is something further. The next sections say it is not.

## Regularity and scalar inputs actually compared

### Acerbi–Fusco–Morini

Retained primary pages `afm-2013-page-7.txt` and `afm-2013-page-22.txt`. Definition 2.5 is the \(\omega r^N\) comparison for every ball and every finite-perimeter competitor supported in that ball. Theorem 4.2: if \(E_h\subset\mathbb T^N\) are \(\omega\)-minimizers of area, with uniformly bounded perimeter, and \(\chi_{E_h}\to\chi_E\) in \(L^1\) for a \(C^2\) limit, then for large \(h\) the boundary is a global normal graph and the graph functions tend to zero in \(C^{1,\alpha}\) for every \(\alpha\in(0,1/2)\). The underlying regularity proof was not read. The PDF was not re-downloaded in this review; the theorem text is the retained page.

R018 and I346 already invoke this theorem to obtain \(C^1\)-small graphs of exact minimizing replacements. The candidate uses the same conclusion at \(\beta=1/4\): the Hölder seminorm of the gradient is bounded along every such sequence, because the graphs converge in \(C^{1,1/4}\). The algebraic rate \(\|D\psi\|_\infty\le C\|D\psi\|_2^{1/5}\) is then the standard interpolation of a bounded Hölder seminorm against a small \(L^2\) norm. With \(\|D\psi\|_2=O(S^{1/2})\) this is \(O(S^{1/10})\), and the cubic area remainder is \(O(S^{11/10})\). Since \(S^{11/10}=o(\varepsilon^2/\ell^2)\), the qualitative \(o(S)\) left by I275/I346 becomes smaller than \(T_2\). No rate of \(C^{1,\alpha}\) convergence is imported. The rate is manufactured from boundedness plus the energy. That manufacture is real analysis on a credited hypothesis. It is not a new regularity theorem.

Uniformity as \(R\to 1/3\) is a compactness reading of the same sequential statement: a blowing-up \(C^{1,1/4}\) norm along \(R_n\to 1/3\) would contradict Theorem 4.2 on the normalized limit. I346 already ran that compactness for \(C^1\)-smallness. Carrying the Hölder seminorm along is the same reading, one derivative of regularity finer, which the printed theorem already contains.

### Pinned scalar profile and Milman

Local entry `354-paper.tex`, SHA-256 `ab75095f542adf4073a41a26a3c3ae97be7b55fa19674ec4fb4c288f7145a813`. Read Theorem `intro:main` and the attribution through the start of the proof section. The proof was not audited. The profile is

\[
I(V)=\min\bigl\{(36\pi)^{1/3}v^{2/3},\,2\sqrt{\pi v},\,2\bigr\},\qquad v=\min(V,1-V),
\]

with balls and shortest tubes at volume \(4\pi/81\), and coordinate slabs on \([1/\pi,1/2]\), extended by complements. This is the stipulated source of \(g(R)\) and of the two equality orbits. It contains no paired contact expansion.

Milman, arXiv:2403.06602v3, HTML introduction through Theorem 1.2, Theorem 1.3, and Corollary 1.4. These are scalar isoperimetric statements for the cube and the flat torus: ranges where spheres, cylinders, and planes minimize, and a reduction of the profile conjecture to two transition volumes. They do not constrain a nested pair \((E,F)\) with two free interfaces, and they do not produce a logarithmic contact cost. The unduloid and numerical arguments were not read.

### Neighboring logarithmic expansions that are different problems

A bounded search for a second-order isoperimetric contact law returned these statements, each read only at the displayed theorem or abstract:

- Barnard–Pearce–Solynin, logarithmic capacity bounded by diameter and area. Planar capacity geometry, no droplet.
- Solynin–Zalgaller, the regular \(n\)-gon minimizes logarithmic capacity among \(n\)-gons of given area. Different extremal problem.
- The second-order expansion of fractional perimeter as \(s\to 1\), and Alberti–Cozzi–Massaccesi–Mirmina, arXiv:2605.07543, stability between two fractional perimeters. Different functionals.
- Muratov–Novaga–Ruffini style charged-drop model, arXiv:2303.05460, Theorem 6.15 as displayed in the HTML: a unique minimizer of a Coulomb-perturbed perimeter whose energy contains \(\gamma^2\varepsilon^6\log(\gamma\varepsilon^4)/(64\pi)\). The logarithm is a contact correction for a charged liquid drop. The scaling, the energy, and the constraint are different. The proof was not read. The display is enough to keep it out of (A) and not enough to mine further constants.

No read statement is (A) or (D). That sentence is a coverage limit. It is not evidence that the all-BV refinement is a new frontier mechanism.

Original Morse–Witten and Höhler–Weaire articles were not opened in this round. I278’s record of their abstracts is not adopted here as a theorem comparison. Ginot et al. was not re-opened. The candidate’s failed TIB/WIAS PDF was not retried; no theorem is attributed to it.

## The hardest new deduction

R018 controls the obstacle by discarding a fixed block of low modes and estimating the high-mode Dirichlet integral on an annulus. The loss \(\zeta\) and the parabolic loss \(c^2/(2R)\) are sent to zero after \(\varepsilon\to 0\). Both are larger than \(T_2\) if they stay fixed. A cutoff \(N(\varepsilon)\) growing fast enough to make the relative loss \(o(\log\ell/\ell)\) fights the \(C^1\) bound on the complementary low block, whose dimension grows. The candidate does not take that route. The deduction that replaces it is the following.

On the mean-zero face torus and on spherical degrees \(\ell\ge 2\), the inverse kernels of \(-\Delta\) and of \(-\Delta_{S_R}-2/R^2\) have the parametrix

\[
K=-(1/(2\pi))\log|x-y|+H,\qquad |H|\le C,
\]

with \(C\) uniform for \(R\) near \(1/3\). The sphere comparison is the classical logarithmic kernel of the spherical Laplacian, plus an \(\ell^{-3}\) coefficient difference that is uniformly summable, plus the finite-rank removal of degree one. For the actual polar chart of a \(C^1\)-small graph, the horizontal inverse \(F\) is bilipschitz at scale \(a\), and the weight in I275’s formula satisfies \(A(p,0)=1\), hence \(A=1+O(a^2)\) on the circle of radius \(a\). The four source measures — two weighted pullbacks of the centered sphere graph and two face circles — therefore have self-energies

\[
(1/(2\pi))\log(1/a)+O(1)+O(a^2\log(1/a)).
\]

Cross terms between the poles are bounded by separation. Faces sit in separate quadratic summands. The dual of the summed circle means is

\[
\|\Lambda_a\|_*^2\le (2/\pi)\log(1/a)+C,
\]

uniformly in the small \(C^1\) graph and in \(R\) near \(1/3\). At the test radius \(a=\sqrt{\varepsilon/\ell}\), one has \(\log(1/a)=(\ell+\log\ell)/2\), the parabolic gap \(q_R(a)\) is \(O(\varepsilon/\ell)\), and the axial drift cancels by adding the two inclusion inequalities. The resulting energy lower bound is (5.3) once the interpolated remainder \(O(S^{11/10})\) is absorbed.

This is the hardest step. It has to be true uniformly, on the nonlinear pullback, with the weight error \(O(a^2)\) rather than an \(O(\|\psi\|_{C^1})\) height error, or the \(O(1)\) in the compliance is not uniform and (A) fails. The matching upper bound has a companion bookkeeping step: the tangent profile \(a^2(\log(d/a)+1/2)=R\varepsilon\) is the classical contact profile, and the vertical area expansion has Hessian \(I+O(r^2)\), whose integral against \(|DZ|^2\) is \(O(\varepsilon^2/\ell^2)\) rather than a fixed fraction of \(S\).

## Why that deduction is bookkeeping

The quadratic form being inverted is the one in I275: sphere Jacobi energy of the degree-one-free graph, plus the two face Dirichlet integrals. The annular Cauchy–Schwarz inequality is the leading term of the same logarithmic kernel, integrated between \(a\) and a fixed outer radius. Replacing \(\log(b/a)=\ell/2+O(1)\) by the Robin constant \((1/(2\pi))\log(1/a)+O(1)\) of the circle, and summing four copies because the form is a direct sum, is the closed form of that estimate. The factor \(2/\pi\) is four times \(1/(2\pi)\). Combined with the area factor \(1/2\) and with \(L=(\ell+\log\ell)/2\), it reproduces \(2\pi\). checks.py records the rational skeleton of this arithmetic and of the tangent-profile energy. The script was inspected and not rerun; rerunning it would rewrite a file outside this review directory. The skeleton is not geometric evidence.

The test radius \(a=\sqrt{\varepsilon/\ell}\) is the radius at which the parabolic obstacle \(r^2/(2R)\) costs a relative height \(O(1/\ell)\), which squares into an energy error \(O(\varepsilon^2/\ell^2)\). That choice is the inversion of (29), written in the free-interface normalization R018 already fixed. Exact cancellation of the axial shift \(h\) by adding the two inequalities is the same drift control as I275’s positive-part inequality, in the form available once both circles are tested at one radius inside the kernel.

Nothing in this chain creates a scale other than the logarithmic capacity of a shrinking contact, which R018 paid, or a coefficient other than the one forced by \(2\pi\) and by \(\log(1/a)=(\ell+\log\ell)/2+O(1)\). The \(O(1)\) is not evaluated. The theorem stops where that constant stops affecting \(T_2\). A sharper expansion with an explicit second constant in the denominator is not claimed and is not required for (B) or (D).

I346’s moving-radius work was TECHNICAL because it reused this capacity uniformly and compared it with an ordinary spectral gap. The present paper reuses the same capacity one order further down. The joint limit and the absence of a rate restriction are already the quantifiers of I346’s leading law. Keeping them for the error \(O(\varepsilon^2/\ell^2)\) is uniformity of constants on the same compact radius interval, not a new degeneracy at \(R=1/3\). The sphere gap at degree 2 and the cylinder gap after translations stay positive, as I346 computed.

The all-BV quantifier does not reopen R018. Arbitrary competitors are reduced to the graph class by the minimizing replacement, lattice comparison, and AFM theorem already used for the leading law. The new estimate never sees a rough set except through that reduction. I278’s substantial step was the first connection of the unrestricted minimum to the concentrating obstacle. The connection is credited. Sharpening its error is a corollary of the kernel that represents the same quadratic form.

## Objections

These are conditions on validity and on what may be counted. They do not propose a radial, smooth, fixed-radius, or rate-restricted substitute.

1. **The second-order lower bound is a proof-gate item.** Sections 3–6 of the candidate are unchecked here. The points that can actually fail are: a uniform \(C^{1,1/4}\) bound after the radius and the reference centers move; the sphere-kernel normalization and the \(O(\ell^{-3})\) difference; bilipschitz control of the actual pullback down to \(a=\sqrt{\varepsilon/\ell}\), including pairs near the diagonal; the weight error \(O(a^2)\) from \(A(p,0)=1\); absorption of \(S^{11/10}\) into \(O(\varepsilon^2/\ell^2)\); and the fixed-volume cancellation of the linear area variation against the free-patch correction. If any of these fails, (5.3) is unpaid. The leading limits in R018 and I346 remain the credited statements. They do not imply (A).

2. **(D) is not a second result.** It is (B) plus (C) plus the Taylor expansion of the explicit function \(g\). I346 already identified the leading tie and declined to call the comparison a new mechanism. The log–log shift of that tie is the same comparison.

3. **The displayed coefficient is forced.** \(2\pi\varepsilon^2/(\ell+\log\ell)=2\pi S-2\pi T_2+O(\varepsilon^2(\log\ell)^2/\ell^3)\). The \(-2\pi\) in front of \(T_2\) is the first correction in \(1/(\ell+\log\ell)=1/\ell-\log\ell/\ell^2+O((\log\ell)^2/\ell^3)\), with the \(2\pi\) taken from R018. An \(O(1)\) ambiguity in \(\log(1/a)\) is absorbed by the remainder in (A). There is no free second coefficient to discover at this scale.

4. **AFM is used as printed, not strengthened.** Theorem 4.2 gives \(C^{1,\alpha}\) convergence for \(\alpha<1/2\) along a sequence of \(\omega\)-minimizers. The candidate’s \(\beta=1/4\) is inside that range. The quasiminimality that puts the paired replacements under the theorem is the R018/I346 reduction. A proof gap in transferring the Hölder seminorm uniformly up to \(R=1/3\) is a gap in (3.1), not a reason to treat the interpolation lemma as a new geometric principle.

5. **The upper profile is the classical contact profile.** Equation (6.1) is the tangent matching of a parabola to a logarithm. LGL and Lv expand that regime. Paying \(O(\varepsilon^2/\ell^2)\) for the cutoff, the volume bumps, and the \(O(r^2)\) metric error is the estimate needed so the limsup meets (5.3). It is not a classification of minimizers.

6. **Bounded reading is not priority.** The screen below did not find a theorem stating (A). Morse–Witten, Höhler–Weaire, Ginot, and the unread TIB/WIAS file remain outside this comparison. Worldwide priority is not established, and its absence from the files that were opened is not a finding.

## What this verdict does not award

- The leading all-BV limit \(\ell L_R/\varepsilon^2\to 2\pi\) at fixed \(R\), the exact charts, the shrinking-circle capacity, and the drift inequality are R018 / I275 / I277 / I278.
- The joint leading limit, the separated wells, the exact identity \(L=\min(M_B,g)\), and the exact cylinder minimum \(g(R)\) are I346, already assessed there as TECHNICAL.
- The endpoint competitor and the failure of fixed-\(R\) uniformity are I283.
- The relation \(\xi\approx-2X\log X\), the energy shape \(X^2|\log X|\), and the log–log inversion are Lacasse–Grest–Levine (27)–(31). Lv (29), (31), and (38) are the same confined-drop expansion in geometric variables.
- Scalar equality cases are the pinned Theorem `intro:main`. Scalar phase ranges are Milman, Theorems 1.2 and 1.3 and Corollary 1.4.
- \(C^{1,\alpha}\) convergence of \(\omega\)-minimizing graphs is Acerbi–Fusco–Morini, Theorem 4.2.
- No acceptance, publication, increment, or proof certificate is made.
