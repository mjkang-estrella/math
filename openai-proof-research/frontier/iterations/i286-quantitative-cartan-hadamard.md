# I286 — quantitative Cartan–Hadamard: the nonlinear bridge remains unpaid

**Verdict: developed gap; no substantial finding nominated.** The proposed dimension-only estimate is neither proved nor refuted here. The actual family 337 source and its filling companion do not provide the needed positive-deficit estimate. No finding-count change, independent acceptance, or worldwide novelty claim is made.

The single main target is the following. For each integer (n\ge2), does there exist (c_n>0) such that, for every complete simply connected smooth (n)-manifold with (\operatorname{Sec}_g\le0) and every measurable finite-perimeter set of volume (0<V<\infty),
\[
\delta(E)=\frac{P_g(E)}{n\omega_n^{1/n}V^{(n-1)/n}}-1
\ \ge c_n\alpha_{\rm geo}(E)^2,
\qquad
\alpha_{\rm geo}(E)=\inf_{p\in M}\frac{|E\triangle B_g(p,r_p(V))|_g}{V},
\quad |B_g(p,r_p(V))|_g=V?
\tag{Q286}
\]
Perimeter is full ambient BV perimeter. Sets may be unbounded or disconnected. There is no sectional-curvature lower bound, curvature-derivative bound, or additional local-geometry hypothesis.

The stipulated pin is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All pinned results are accepted as premises; their truth is not audited.

## Actual source contract

[Generalized Cartan–Hadamard isoperimetry and Euclidean equality rigidity](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026/build/sections/01-introduction.tex), **`thm:main`**, establishes the sharp equal-volume constant-curvature model comparison for *all* finite-volume finite-perimeter sets, with (n\ge2) and sectional curvature at most (\kappa\le0). At (\kappa=0) it proves (\delta\ge0).

Its **`thm:equality`** assumes *boundedness* and positive volume. Equality holds exactly for regions isometric, with their induced metric, to Euclidean balls, modulo null sets. Section 08, concluding converse, proves such an open region is an actual ambient geodesic ball: its radial straight segments map to ambient geodesics, so geodesic uniqueness identifies the isometry with the exponential map at its center. The theorem is therefore consistent with Q286 at zero deficit for bounded sets. It does not assert a quantitative rate, or equality classification for unbounded finite-volume sets.

The same manuscript's **`thm:extrinsic-sobolev`** (Section 03), **`lem:profile-curvature`** (04), **`prop:profile-ode`** (05), **`prop:equality-boundary`** (07), and Section 08's moment/flux proof were read as the most plausible bridge. The profile argument uses actual confined minimizers. The equality regularity and constant mean curvature use exact zero deficit.

[Sharp integral fillings in CAT(0) spaces](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/build/sections/01-introduction.tex), **`thm:main`**, supplies compactly supported integral fillings in proper CAT(0) spaces for cycle dimensions (k\ge2), with mass bound
\[
\mathbf M(S)\le
\frac{\mathbf M(T)^{(k+1)/k}}
{(k+1)^{(k+1)/k}\omega_{k+1}^{1/k}}.
\]
Its **`cor:cartan-hadamard`**, **`lem:top-dimensional-constancy`**, and **`lem:opposite-average`** do not turn a small perimeter deficit for the prescribed set into distance from a ball. The weighted chord estimates operate on a specially constructed extremizing cycle under a hypothetical violation of the sharp inequality. They cannot be applied to an arbitrary near-optimal boundary. The full declared theorem/proposition screen and the selected lemma passages contain no Q286 statement; this is a scoped comparison, not a proof of exhaustive literature novelty.

## Definition and finite-volume checks that are paid

Detailed proofs are in [analysis.md](../experiments/i286_quantitative_cartan_hadamard/analysis.md).

1. Each (r_p(V)) exists uniquely. Every finite-radius ball has finite volume; its volume is strictly increasing and continuous from zero to infinity. Polar metric domination gives (r_p(V)\le (V/\omega_n)^{1/n}). Cartan–Hadamard already gives infinite injectivity radius.
2. The infimum defining (\alpha_{\rm geo}) is attained, even for unbounded finite-volume (E). The overlap with the equal-volume ball is continuous in the center and tends to zero as the center escapes to infinity. Thus (0\le\alpha_{\rm geo}<2), and (\alpha_{\rm geo}=0) exactly when (E) is an equal-volume ambient ball modulo null sets.
3. If (A(E)=V\alpha_{\rm geo}(E)), then
   \[
   |A(E)-A(F)|\le |E\triangle F|+\big||E|-|F|\big|
   \le2|E\triangle F|.
   \]
   Strict BV truncation and smooth approximation therefore show that Q286 for bounded smooth, possibly disconnected sets with a common dimensional constant would imply Q286 in its full finite-volume scope. Exact-volume repair is unnecessary. This reduction is routine and is not nominated as substantial progress.
4. A radial divergence argument proves, for every center,
   \[
   \frac{|E\triangle B_g(p,r_p)|}{V}
   \le\frac2V\int_{\partial^*E}(d(p,x)-r_p)_+\,dP_g(x).
   \tag{R286}
   \]
   An infinite right-hand side is allowed. This is a geometric counterpart of the radial endpoint in Euclidean transport proofs; it does not pay its deficit-controlled input.

## The exact unpaid step

A sufficient bridge would select a center and control the radial boundary excess in R286 by (C_nV\sqrt{\delta(E)}). No such estimate is assumed here. Q286 may hold by a different route; this sufficient condition is not presented as equivalent or established.

Three attempted uses of the pinned proof fail at specific interfaces:

* **Equality regularity:** positive deficit gives only almost-minimality with a fixed additive error (n\omega_n^{1/n}V^{(n-1)/n}\delta). That error does not vanish with the size of a local modification. The exact stationarity, regularity, and constant mean curvature in `prop:equality-boundary` are consequently unavailable.
* **Spectral expansion:** the exact equality proof cancels the constant Sobolev slack before differentiating twice. With positive slack (s>0), an inequality (s+t^2Q(\phi)+o(t^2)\ge0) supplies no lower bound on (Q(\phi)) by letting (t\to0). Neither the sharp boundary spectral gap nor its upper radial-moment consequence survives that argument without a new quantitative step.
* **Dimension three:** the punctured flux square controls a Willmore-type deficit. Smooth Euclidean domains can have fixed unit-ball volume, (\delta(E_k)\to0), and (\int_{\partial E_k}h_k^2\to\infty). The explicit volume-preserving graph construction and proof are in analysis.md. Thus perimeter deficit cannot directly control the curvature energy required by this route, even in a flat Cartan–Hadamard manifold. This is a counterexample to an attempted auxiliary estimate, **not** to Q286.

Logarithm coordinates have an additional unresolved volume problem: their contraction gives (P_{\mathbb R^n}(\log_pE)\le P_g(E)) and (W=|\log_pE|\le V), but only
\[
\delta_{\mathbb R^n}(\log_pE)
\le(1+\delta(E))(V/W)^{(n-1)/n}-1.
\]
The uncontrolled factor (V/W), and the absence of a weighted symmetric-difference transfer, prevent importing the Euclidean quantitative theorem. No desired transport estimate is smuggled in as a hypothesis.

## Nearest collisions and scope

Fusco–Maggi–Pratelli, [Theorem 1.1 (2008)](https://annals.math.princeton.edu/wp-content/uploads/annals-v168-n3-p06.pdf), already proves exactly the Euclidean specialization, with the same relative perimeter deficit and squared volume asymmetry after adjusting its normalization. Figalli–Maggi–Pratelli, [Theorem 1.1 (2010)](https://people.math.ethz.ch/~afigalli/papers-pdf/A-mass-transportation-approach-to-quantitative-isoperimetric-inequalities.pdf), includes anisotropic Euclidean perimeters with a dimensional constant; its quantitative transport and trace-selection operations are genuine antecedents. A Euclidean or constant-norm restatement would collide directly.

Hoisington, [Theorem 1.4 and Proposition 4.2](https://arxiv.org/pdf/2111.06860), gives chord-integral refinements in Cartan–Hadamard geometry, including negative-curvature Yau comparison and exact rigidity. Their deficits are not Q286's asymmetry estimate. Actual statements and selected proof passages were read, not just search snippets.

Bögelein–Duzaar–Scheven's hyperbolic-space work is another immediate comparison. An [author's 2019 slides](https://wmii.uwm.edu.pl/dirac/f/Verena_Boegelein.pdf) display a stronger normal-oscillation inequality with a parameter-dependent constant. The publisher full paper was inaccessible; the slides omit the relevant parameter range in their final theorem display. No precise journal theorem, uniform all-volume assertion, or extension to variable curvature is inferred from that incomplete source.

The bounded internal comparison found R012/I38 (Gaussian propeller), R013/I49 (logarithmic Brunn–Minkowski), I43 (convex/torus comparison), I91 (finite CAT(0) configuration), and I249/R017/R018 (torus contact asymptotics). None of the relevant passages supplies Q286. Search absence proves neither literature novelty nor the absence of another project overlap.

The candidate was not rigorously shown false or already contained in a companion, so no fallback target replaces it. The outcome is the explicitly unpaid global nonlinear bridge, with validated definition/reduction checks and a concrete obstruction to the direct curvature method. No numerical scans, subagents, shared-ledger edits, staging, commits, or publication were used. Detached output hashes accompany the handoff.
