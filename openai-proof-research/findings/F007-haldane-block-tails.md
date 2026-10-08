# F007 — Exponential block-spin tails and spatial response in the Haldane chain

Status: **proved model-specific corollary; independently reviewed and accepted**. Upstream gap accepted as a premise. No new general concentration principle or literature-priority claim.

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

### Theorem

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

These bounds are independent of both system size and block length. They hold for every finite interval in **every** subsequential local limit of periodic ground states, and for any unit spin axis in place of (z).

There are also explicit quadratic bounds. For every real family (a_j), define (A_a=\sum_j a_jS_j^z) and (D(a)=\sum_j(a_{j+1}-a_j)^2). Then

\[
 \omega_L(A_a)=0,\qquad
 \omega_L(A_a^2)\le\frac{2}{3\delta}D(a).              \tag{3}
\]

If (E_L(h)=\min\sigma(H_L-hA_a)), for fixed L and a it is real analytic in some neighborhood of zero, so its second derivative exists, and the zero-field response satisfies

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

Let ω be any local limit along even lengths L_n→∞, with the closing bond eventually outside each fixed support. For each fixed finite interval I, all operators in (1)–(2), including spectral projectors, lie in its fixed local matrix algebra. Local convergence preserves these inequalities for every |t|≤τ and r≥0. Equation (3) passes to every finitely supported real family a on Z, with D(a)=Σ_(j∈Z)(a_(j+1)−a_j)² after zero extension. Global rotation invariance passes to the limit and gives every unit spin axis. Equations (4)–(5) are asserted at finite volume only. Neither uniqueness nor purity of the limiting state is required. **QED.**

### Novelty assessment and validation

The double-commutator method is classical: [Hohenberg–Brinkman, *Sum rules for the frequency spectrum of linear magnetic chains*, PRB 10 (1974), 128](https://doi.org/10.1103/PhysRevB.10.128). Boundary scaling of conserved-charge fluctuations is also established physics: [Song et al., *Bipartite fluctuations as a probe of many-body entanglement*, PRB 85 (2012), 035409](https://arxiv.org/abs/1109.1001), and [Rachel et al., PRL 108 (2012), 116401](https://link.aps.org/accepted/10.1103/PhysRevLett.108.116401). These precedents rule out advertising (3) or a fluctuation area law as a new general principle. General quantum concentration also has a substantial literature, e.g. [Anshu–Metger (2023)](https://quantum-journal.org/papers/q-2023-05-11-999/).

What is newly available from the assumed release is a deduction whose gap input is the pinned theorem accepted in this project, rather than an additional model conjecture, for the **pure bilinear spin-one model**, including the explicit size-independent exponential tail (2). No exact duplicate of this explicit statement was found in the bounded search. That is not a proof of literature novelty. The exponential-moment argument itself is an elementary gap-to-concentration iteration using charge conservation, and may already exist in a general conserved-charge formulation.

Companion check: read the periodic manuscript's introduction and complete `assembly.tex`; read the boundary-field companion's [`build/main.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-boundary-field-gap-for-the-spin-one-Heisenberg-chain-September-24-2026/build/main.tex), `sections/history.tex`, `sections/conclusion.tex`, and `sections/topology.tex`. The latter gives boundary-selected index (-1), already upstream; it does not state these block-tail or response bounds. Its selected open-chain states are **not** silently identified with periodic limits here.

The standard-library script `experiments/probability_dynamics.py` checks the weighted and exponential two-site double commutators exactly with rational arithmetic in a similar spin-one representation, plus the Casimir normalization and XY minimal polynomial. It passes and gives (\tau=0.0519799633352), (4/(3\delta)=348.940839127). This validates signs and constants in the new algebra, not the assumed upstream gap.

A closer concentration precedent is [Kuwahara–Arad–Amico–Vedral,
*Local reversibility and entanglement structure of many-body ground states*,
§V, equation (7)](https://arxiv.org/html/1502.05330). Exponential concentration
for additive observables in unique gapped ground states is established
there, with a displayed subsystem-size-dependent scale. Here conserved
charge cancels interior bonds, yielding a boundary-controlled scale. A
general conserved-charge version may already exist; explicit constants
alone are not evidence of novelty.

### Validation disposition

[Independent review](../reviews/haldane-r1.md) accepted all constants and
equations after the five presentation refinements incorporated here. It
independently checked the commutator as a Laurent-polynomial identity and
the self-adjoint XY blocks. The parent independently checked the gap
variance inequality, crossing-bond factors, dyadic recursion and limit
order. `python openai-proof-research/experiments/probability_dynamics.py`
passed exact spin-algebra checks. The constant τ is approximately
0.0519799633352; the proper-block variance bound is below349. These checks
validate the deduction, not the upstream gap. No proof-assistant
verification is claimed.
