> Archived exploratory draft. Some claims were corrected, rejected, or left unreviewed. Use [the final index](../README.md) and [screening decisions](../SCREENING.md) for accepted results.

# Probability, dynamics and mathematical physics: downstream deductions

Research date: 2026-10-08. Upstream revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All upstream statements below are **assumed true**, as requested. This report proves downstream deductions, not the upstream claims. Neither result below is claimed to introduce a new general transference principle or to have established publication priority.

## Ranked candidates

| Rank | Candidate | Assessment |
|---|---|---|
| 1 | Uniform exponential tails for block magnetization in the pure spin-one Heisenberg ground state; accompanying weighted fluctuation and response inequalities | Fully proved below. Explicit constants and passage to every periodic thermodynamic limit. The strongest candidate for a short model-specific corollary note. |
| 2 | Almost-sure fixed-disorder quantum transport from every lattice site in weakly disordered Anderson models in every dimension at least three | Fully proved below, including an unfiltered point-source statement. Classical Guarneri–Combes–Last mechanism in the newly available Euclidean fixed-disorder regime. |
| 3 | Dimension-free log-Sobolev inequality after bounded nonconvex perturbations of linearly subgaussian log-concave laws | Valid, but immediate Holley–Stroock transference; precise statement and proof sketch below. Lower novelty value. |
| 4 | Smooth zero-entropy, all-orders mixing dynamics with simple Lebesgue spectrum | Reject as a new proposal: upstream explicitly already gives these consequences. |

Sources were selected using `sources/CONTENTS.md` and the corresponding entries in `sources/overview.tex` (093, 144–145, 261, 268). Important retrieval issue: the supplied `sources/tree.json` has `truncated: true`, ends inside `lean/`, and contains **no `.tex` paths**. Pinned GitHub contents requests were therefore used to locate manuscript files, and actual text was downloaded from pinned raw URLs into `sources/cache/probability_dynamics/`. A later GitHub API rate limit was handled by following `\input` paths through raw URLs. No shared source index was modified.

## 1. Exponential block-spin tails and spatial response in the Haldane chain

### Exact upstream dependency

OpenAI, *The periodic spin-one Haldane gap*, [`build/introduction.tex`, Theorem `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-periodic-spin-one-Haldane-gap-September-24-2026/build/introduction.tex). For even periodic length (L\ge2304), the self-adjoint Hamiltonian

\[
 H_L=\sum_{j\in\mathbb Z/L\mathbb Z}\mathbf S_j\cdot\mathbf S_{j+1}
\]

has a unique ground vector (\Omega_L), and gap greater than

\[
 \delta=\frac{\log20}{784}=0.003821087083\ldots.
\]

The spin normalization is (\sum_\alpha(S^\alpha)^2=2I). Its [`build/assembly.tex`, Corollary `cor:local-limit`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-periodic-spin-one-Haldane-gap-September-24-2026/build/assembly.tex) supplies existence of subsequential local limits; alternatively the elementary compactness argument there suffices.

### Proposed theorem PD1

Put (\omega_L(B)=\langle\Omega_L,B\Omega_L\rangle) and

\[
 \tau=\sqrt{\delta/\sqrt2}=0.051979963335\ldots.
\]

For **every** even (L\ge2304), every contiguous block (B) of the ring, and every real (|t|\le\tau), let (Q_B=\sum_{j\in B}S_j^z). Then

\[
 \boxed{\quad \omega_L(e^{tQ_B})\le
       \exp(2\sqrt2\,t^2/\delta).\quad}                 \tag{1}
\]

In particular the projective measurement distribution of (Q_B) satisfies, for all (r\ge0),

\[
 \omega_L(\mathbf1_{\{|Q_B|\ge r\}})\le 2e^2e^{-\tau r},
 \qquad \omega_L(e^{\tau|Q_B|})\le2e^2.                \tag{2}
\]

These bounds are independent of both system size and block length. They hold for every finite interval in **every** subsequential local limit of periodic ground states, and for any spin axis in place of (z).

There are also explicit quadratic bounds. For every real family (a_j), define (A_a=\sum_j a_jS_j^z) and (D(a)=\sum_j(a_{j+1}-a_j)^2). Then

\[
 \omega_L(A_a)=0,\qquad
 \omega_L(A_a^2)\le\frac{2}{3\delta}D(a).              \tag{3}
\]

If (E_L(h)=\min\sigma(H_L-hA_a)), its derivative at zero is well-defined, and the zero-field response satisfies

\[
 0\le-E_L''(0)\le\frac{4}{3\delta^2}D(a).            \tag{4}
\]

Thus a nonempty proper block has (\operatorname{Var}(Q_B)\le4/(3\delta)<349). For (q=2\pi k/L), its static structure factor obeys

\[
 S_L(q):=\frac1L\omega_L\left(\left|\sum_j e^{iqj}S_j^z\right|^2\right)
 \le\frac{8}{3\delta}\sin^2(q/2).                    \tag{5}
\]

In particular this is a rigorous quadratic upper bound at small wave number; no matching asymptotic is asserted.

### Complete proof

**Symmetry and gap.** Uniqueness of the ground state makes its line invariant under global (SU(2)) and translations. Every continuous one-dimensional representation of (SU(2)) is trivial, so the ground vector is a singlet. In particular all one-spin expectations and (\omega_L(Q_B)) vanish. Translation and rotational invariance imply, with (e_L=E_0(L)/L),

\[
 \omega_L(S_j^xS_{j+1}^x+S_j^yS_{j+1}^y)=2e_L/3.
\]

Each spin-one bond has eigenvalues (-2,-1,1), since it is half the two-spin total Casimir minus (2I); hence (e_L\ge-2). For any self-adjoint (F), the gap gives

\[
 \delta\,[\omega_L(F^2)-\omega_L(F)^2]
 \le\omega_L(F(H_L-E_0)F)
 =\tfrac12\omega_L([F,[H_L,F]]).                     \tag{6}
\]

**Quadratic estimates.** Direct spin commutation gives, writing (X_j=S_j^xS_{j+1}^x+S_j^yS_{j+1}^y),

\[
 [A_a,[H_L,A_a]]=-\sum_j(a_j-a_{j+1})^2X_j.
\]

Consequently the right side of (6) is (-e_LD(a)/3\le2D(a)/3), proving (3). A block indicator has two jumps, giving the variance bound. For (5), apply (3) to (\cos(qj)) and (\sin(qj)), add, and use that the (S_j^z) commute and the two Dirichlet energies sum to (4L\sin^2(q/2)).

For completeness, differentiating the normalized isolated ground eigenvector at (h=0), and choosing its derivative orthogonal to (\Omega_L), gives

\[
 -E_L''(0)=2\langle A_a\Omega_L,(H_L-E_0)^{-1}_{\Omega_L^\perp}A_a\Omega_L\rangle.
\]

Indeed the first differentiated eigen-equation is

\((H_L-E_0)\Omega'_L=A_a\Omega_L\), since (E_L'(0)=-\omega_L(A_a)=0\); differentiating (E_L'(h)=-\langle A_a\rangle_h) proves the formula. The inverse is at most (1/\delta), and (3) gives (4). This derivative statement does not assert a size-independent interval of analyticity in (h).

**Exponential moments.** Set (F=e^{tQ_B/2}), (M(t)=\omega_L(e^{tQ_B})). Only the two bonds crossing the boundary of a proper block fail to commute with (F). On either crossing bond,

\[
 [F,[\mathbf S_j\cdot\mathbf S_{j+1},F]]
   =-2(\cosh(t/2)-1)F X_j F.                         \tag{7}
\]

To verify (7), write (X_j=(S_j^+S_{j+1}^-+S_j^-S_{j+1}^+)/2): each term changes (Q_B) by (+1) or (-1). Conjugation by (F) multiplies it by (e^{t/2}) or (e^{-t/2}); expanding (2FhF-F^2h-hF^2) gives (7). The longitudinal term commutes. In the self-adjoint spin-one representation (\|X_j\|=\sqrt2): its fixed-total-(S^z) blocks have eigenvalues in (\{0,\pm1,\pm\sqrt2\}). Thus (6) implies

\[
 \delta\big[M(t)-M(t/2)^2\big]
 \le2\sqrt2(\cosh(t/2)-1)M(t).
\]

Let (\kappa(t)=2\sqrt2(\cosh(t/2)-1)/\delta). For (|t|\le\tau<2), the elementary series bound (\cosh(t/2)-1\le t^2/4) gives (\kappa(t)\le t^2/(\sqrt2\delta)\le1/2). Therefore, with (g=\log M),

\[
 g(t)\le2g(t/2)-\log(1-\kappa(t))
       \le2g(t/2)+\sqrt2\,t^2/\delta.
\]

Iterating (n) times bounds the accumulated error by

\((\sqrt2\,t^2/\delta)\sum_{k=0}^{n-1}2^{-k}\le2\sqrt2\,t^2/\delta\).

For each finite ring, (g(s)=s\omega_L(Q_B)+O(s^2)=O(s^2)), so (2^ng(t/2^n)\to0). This proves (1) without any estimate depending on (|B|). Empty and full blocks are trivial because the state is a singlet. Apply Markov's inequality at (t=\tau) and (t=-\tau), noting (2\sqrt2\tau^2/\delta=2), to get the tail bound. The operator inequality (e^{\tau|Q_B|}\le e^{\tau Q_B}+e^{-\tau Q_B}) gives the exponential-moment bound.

For a fixed finite interval, all operators in (1)–(3), including its spectral projectors, are bounded local operators. Their expectations converge along every locally convergent subsequence. Passing to that limit preserves the inequalities; this works for each of the countably many finite intervals. Global rotations give the statement for any axis. This does not require uniqueness of the infinite-volume ground state. **QED.**

### Novelty assessment and validation

The double-commutator method is classical: [Hohenberg–Brinkman, *Sum rules for the frequency spectrum of linear magnetic chains*, PRB 10 (1974), 128](https://doi.org/10.1103/PhysRevB.10.128). Boundary scaling of conserved-charge fluctuations is also established physics: [Song et al., *Bipartite fluctuations as a probe of many-body entanglement*, PRB 85 (2012), 035409](https://arxiv.org/abs/1109.1001), and [Rachel et al., PRL 108 (2012), 116401](https://link.aps.org/accepted/10.1103/PhysRevLett.108.116401). These precedents rule out advertising (3) or a fluctuation area law as a new general principle. General quantum concentration also has a substantial literature, e.g. [Anshu–Metger (2023)](https://quantum-journal.org/papers/q-2023-05-11-999/).

What is newly available from the assumed release is a proof with no unproved gap hypothesis for the **pure bilinear spin-one model**, including the explicit size-independent exponential tail (2). No exact duplicate of this explicit statement was found in the bounded search. That is not a proof of literature novelty. The exponential-moment argument itself is an elementary gap-to-concentration iteration using charge conservation, and may already exist in a general conserved-charge formulation.

Companion check: read the periodic manuscript's introduction and complete `assembly.tex`; read the boundary-field companion's [`build/main.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-boundary-field-gap-for-the-spin-one-Heisenberg-chain-September-24-2026/build/main.tex), `sections/history.tex`, `sections/conclusion.tex`, and `sections/topology.tex`. The latter gives boundary-selected index (-1), already upstream; it does not state these block-tail or response bounds. Its selected open-chain states are **not** silently identified with periodic limits here.

The standard-library script `experiments/probability_dynamics.py` checks the weighted and exponential two-site double commutators exactly with rational arithmetic in a similar spin-one representation, plus the Casimir normalization and XY minimal polynomial. It passes and gives (\tau=0.0519799633352), (4/(3\delta)=348.940839127). This validates signs and constants in the new algebra, not the assumed upstream gap.

## 2. Fixed-disorder transport from every Anderson point source

### Exact upstream dependency

OpenAI, *Absolutely Continuous Spectrum for Weak Disorder Anderson Models in Dimensions at Least Three*, [`build/01-introduction.tex`, Theorem `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Absolutely-Continuous-Spectrum-for-Weak-Disorder-Anderson-Models-in-Dimensions-at-Least-Three-September-23-2026/build/01-introduction.tex). The operator is

\[
 (H_{\lambda,\omega}\psi)(x)=-\sum_{|y-x|_1=1}\psi(y)+\lambda V_x(\omega)\psi(x),
 \qquad V_x\stackrel{\mathrm{iid}}\sim\operatorname{Unif}[-1,1].
\]

For each fixed (d\ge3) there is (\lambda_d>0) such that every fixed (0<\lambda<\lambda_d) has almost surely purely absolutely continuous, nonzero spectral restriction to

\[
 I_3=(-6+e_2/2,-6+e_2),\quad
 I_d=-2d+(1/200,1/100)\ (d\ge4),
\]

where (e_2\in(0,1/100)) is the fixed sufficiently small upstream constant.

For the **every-point-source** version one additionally uses [`build/09-spectral.tex`, Proposition `prop:certificate-readout`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Absolutely-Continuous-Spectrum-for-Weak-Disorder-Anderson-Models-in-Dimensions-at-Least-Three-September-23-2026/build/09-spectral.tex): its conclusion includes (\langle\delta_0,\mathbf1_{I_d}(H)\delta_0\rangle>0), and its proof's `eq:spectral-all-positive` gives positivity at every site. The certificate hypotheses are verified in the upstream main theorem's application. Translation invariance and a countable intersection suffice to transfer the origin conclusion to all sites.

### Proposed theorem PD2

Fix (d\ge3) and (0<\lambda<\lambda_d). Almost surely, **simultaneously for every** (x\in\mathbb Z^d) and (p>0), there exist (c_{p,x,\omega}>0) and (T_{x,\omega}<\infty) such that

\[
 \boxed{\quad \frac1T\int_0^T\sum_y|y-x|_\infty^p
  |\langle\delta_y,e^{-itH_{\lambda,\omega}}\delta_x\rangle|^2dt
 \ge c_{p,x,\omega}T^{p/d}\quad(T\ge T_{x,\omega}).\quad}       \tag{8}
\]

In particular the lower time-averaged transport exponent, normalized by (p\log T), is at least (1/d). For (d=3), the averaged second spatial moment is at least a positive realization-dependent multiple of (T^{2/3}). This is an **unfiltered** point source, avoiding the possibility that a sharp spectral cutoff already has infinite position moments at time zero.

### Complete proof of the transference, including mixed spectral types

It suffices to prove a deterministic fact: if a normalized vector (\psi\in\ell^2(\mathbb Z^d)) has a nonzero absolutely continuous spectral component for a bounded self-adjoint (H), its time-averaged position moments about a chosen origin have the asserted lower growth.

Let the absolutely continuous part of its scalar spectral measure have density (w). Choose a Borel set (J) disjoint from a carrier of the singular part and a finite (M>0) such that (0<w\le M) on (J) and (b=\int_Jw(E)dE>0). Such a choice exists since (w\in L^1) and is not zero. Put (\phi=\mathbf1_J(H)\psi). Then

\[
 \|\phi\|^2=\langle\phi,\psi\rangle=b,\qquad
 d\mu_\phi/dE=\mathbf1_Jw\le M.
\]

For each site (y), the complex measure (\langle\delta_y,P(dE)\phi\rangle) has an (L^2(dE)) density (h_y) satisfying

\[
 \int|h_y|^2dE\le M.
\]

Here is the precise justification: the two-by-two matrix of spectral measures of (\delta_y,\phi) is positive. Its Radon–Nikodym matrix is positive for a dominating scalar measure, so on the absolutely continuous part (|h_y|^2\le w_yw_\phi), while the cross measure has no singular part because (\mu_\phi) has none. Integrating gives (\int|h_y|^2\le M\int w_y\le M\|\delta_y\|^2=M).

Plancherel, with Fourier kernel (e^{-itE}), now gives

\[
 \int_{\mathbb R}|\langle\delta_y,e^{-itH}\phi\rangle|^2dt\le2\pi M.
\]

If (Q_R) projects onto (|y|_\infty\le R), then for (R\ge1)

\[
 \frac1T\int_0^T\|Q_Re^{-itH}\phi\|^2dt
 \le\frac{2\pi M3^dR^d}{T}.                         \tag{9}
\]

Choose (R=cT^{1/d}), where (c=(b^2/(8\pi M3^d))^{1/d}), and (T\ge c^{-d}). The last bound is at most (b^2/4). At every time the inner product of the evolved (\phi) and (\psi) remains (b). Splitting this inner product inside and outside the ball, averaging, and applying Cauchy–Schwarz yields

\[
 b\le\left(\frac1T\int_0^T\|Q_Re^{-itH}\phi\|^2dt\right)^{1/2}
 +\sqrt b\left(\frac1T\int_0^T\|(1-Q_R)e^{-itH}\psi\|^2dt\right)^{1/2}.
\]

Thus the averaged mass outside the ball is at least (b/4), and its (p)-th moment at least ((b/4)R^p=(b/4)c^pT^{p/d}). This argument deliberately preserves the full initial vector (\psi); its remaining singular spectral component cannot invalidate the lower bound through interference.

Apply this fact to (\psi=\delta_x), taking (J\subset I_d) using the upstream positive local spectral weight. The probability-one event works for every site by countability. For each site the same (b,M,c,T_0) work for **all** (p>0), so no uncountable intersection of probability-one events is being taken. Changing the origin of (9) to (x) changes nothing.

Finally the moments of an unfiltered point source are finite at every finite time: the convergent series for (e^{-itH}\delta_x) has its (n)-th term supported in the graph ball of radius (n), and its norm is at most ((|t|\|H\|)^n/n!). Consequently its tails decay faster than any power at fixed (t), uniformly on compact time intervals. Thus (8) is not merely an infinite-moment tautology. **QED.**

### Novelty, duplicate check, and limits

This is the classical spectral-dimension/transport mechanism, not a new transport inequality: [Yoram Last, *Quantum Dynamics and Decompositions of Singular Continuous Spectra*, JFA 142 (1996), 406–445](https://doi.org/10.1006/jfan.1996.0155). Related primary work is [Germinet–Kiselev–Tcheremchantsev, *Transfer matrices and transport for Schrödinger operators*, Ann. Inst. Fourier 54 (2004), 787–830](https://aif.centre-mersenne.org/item/?id=AIF_2004__54_3_787_0). The distinction worth recording is **fixed positive disorder, arbitrarily long times, every (d\ge3), the original iid uniform lattice model**. Weak-coupling kinetic/diffusion limits send disorder to zero and are a different quantifier regime; upstream's introduction explicitly makes this distinction.

The full introduction and spectral section were inspected for a duplicate: the explicit upstream corollary is spectral coexistence with localized edge states, not (8). The same-family two-dimensional companion was checked in `build/sections/introduction.tex` and `build/sections/spectral.tex`; it concerns pure-point spectrum, explicitly disclaims dynamical localization, and does not duplicate (8). Numerical finite-box propagation would not validate arbitrarily long times on an infinite lattice, so none is offered as evidence.

No deterministic positive transport constant, explicit usable disorder threshold, diffusion, (T^{p/2}) growth, ballistic transport, pointwise-in-time lower bound, or positive conductivity follows from this proof. In particular (p/d) must not be relabelled a diffusive exponent. Simultaneity over all disorder strengths is not asserted; the full-probability event may depend on the fixed (\lambda).

## 3. Lower-ranked valid transference and rejected alternatives

**Bounded nonconvex perturbations.** The exact source is [`A dimension-free logarithmic Sobolev inequality for subgaussian log-concave measures`, `build/sections/01-introduction.tex`, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-dimension-free-logarithmic-Sobolev-inequality-for-subgaussian-log-concave-measures-September-23-2026/build/sections/01-introduction.tex). It assumes a centered log-concave Lebesgue density with (\sup_{|\theta|=1}\mathbb E\exp(\langle X,\theta\rangle^2/a^2)\le2), and proves (\operatorname{Ent}_\mu(f^2)\le Ca^2\int|\nabla f|^2d\mu). For any bounded measurable (W), (\nu=Z^{-1}e^{-W}\mu) consequently satisfies

\[
 \operatorname{Ent}_\nu(f^2)\le Ca^2e^{\operatorname{osc}W}\int|\nabla f|^2d\nu.
\]

Indeed if (m\le d\nu/d\mu\le M), use

\(\operatorname{Ent}_\eta(g)=\inf_{s>0}\int[g\log(g/s)-g+s]d\eta\),

whose integrand is nonnegative, to get (\operatorname{Ent}_\nu(g)\le M\operatorname{Ent}_\mu(g)), and compare the Dirichlet integrals by (1/m). Here (M/m=e^{\operatorname{osc}W}). This is exactly the known [Holley–Stroock perturbation principle](https://doi.org/10.1007/BF01011161), also explicitly stated as Theorem 1.7 in [Gozlan–Roberto–Samson's primary paper](https://perso.pages.math.cnrs.fr/users/cyril.roberto/Articles/Gozlan-Roberto-Samson-AOP-11.pdf). New coverage comes only from the general base measures now supplied upstream. The unperturbed quadratic transport inequality is **already** upstream Corollary `cor:intro-transport`, so reject that as a new theorem. No discretized Langevin complexity is claimed without extra regularity assumptions.

**Smooth mixing example.** The pinned [`smooth three-torus manuscript introduction`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/build/sections/01-introduction.tex) explicitly says its consequences section derives mixing, zero entropy, vanishing Lyapunov exponents, and all-orders mixing using the separate multiple-mixing theorem. These are duplicates. A central limit theorem cannot be inferred merely from mixing of all orders without quantitative control, so that proposed extension was not pursued.

**Other attractive but unsupported upgrades.** The periodic Haldane gap alone does not identify all infinite-volume ground states, prove a gapped interpolation to AKLT, or give a uniform nonzero magnetic-field plateau: the crude operator-norm perturbation scales with (L). Absolute continuity of the Anderson spectrum does not supply diffusion. These remain explicit gaps rather than proposed conclusions.

## Integration recommendation

Keep PD1 and PD2 as two independently auditable downstream corollaries, with labels **proved from assumed upstream results; classical transference in new model regimes; literature novelty not established**. PD1's uniform exponential-moment formulation deserves the next targeted literature check, particularly general concentration theorems for conserved charges in gapped ground states. No mathematical gap remains in the deductions presented here, but novelty review is necessarily incomplete. The source-cache retrievals and two uniquely assigned report/experiment files are the only writes; no staging, commits, or additional agents were used.
