# Arithmetic bridge, research/review round 2

Date: 2026-10-08. Scope: the midpoint divisor-graph route to ordinary three-point Liouville cancellation. All theorems of the pinned OpenAI repository are accepted as true. Upstream revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

**Result.** No new three-point Chowla case or named conjecture is proved. There is, however, an unconditional bound for the specific four-midpoint cycle proposed for investigation: its total normalized absolute contribution, over distinct labels in the actual qualitative divisor bin, is at most
\[
 B^{\eta+(\epsilon-\eta)/16+o(1)}P_0^{-2},
 \qquad P_0=\exp(B^{1-\epsilon}). \tag{R2.1}
\]
This bound allows arbitrary bounded midpoint factors, including Liouville. It uses the prime restrictions and vertex weights, not a conjectural four-point correlation estimate. Thus that particular cycle is **not** the unresolved arithmetic obstruction suggested by the first scout. The directed singular-value trace has a further distinction explained below.

A second proved result is an obstruction to a specific implementation: plugging the natural **undeleted, unnormalized** upstream kernel into scout hypothesis A2 makes A2 false for every divisor family with the requisite bin mass, once the auxiliary scale is large. Rare, large entries already violate the proposed norm target. This does not refute A1+A2 as an abstract sufficient criterion or rule out a properly localized, weighted replacement.

The genuinely unresolved tasks are the remaining high-trace classes, with their singleton-prime cancellations, and cubic analytic centering. Averaged linear-form literature is relevant to the geometry but has the wrong scale/weight contracts for these tasks. The report supplies exact reasons rather than declaring the rank-three system intrinsically inaccessible.

## 1. Pinned source contracts checked

I read `AGENTS.md`, the source revision/catalogue, the first scout, and the actual family007 introduction and relevant qualitative/quantitative files. Nineteen local family007 files were rehashed against the existing pinned manifest, including their git blob hashes; see [verification](../sources/arithmetic_r2/arithmetic_r2_upstream_verification.json). This verifies local source identity, not the truth of upstream results. There is one manuscript in family007; no companion higher-order theorem is being assumed.

The common pinned source prefix is

`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/`.

The contracts used are:

- [introduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/introduction.tex), `thm:q-affine`, `thm:elliott`: two factors, fixed affine coefficients; the power-of-log exponent is absolute but the coefficient-dependent constants are not uniform for growing coefficients.
- [qualitative/graph-setup.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/graph-setup.tex), `eq:graph-constants` through `eq:graph-weights`, `prop:graph-estimate`: the exact weights and admissibility below.
- [qualitative/analytic-transfer.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/analytic-transfer.tex), `lem:raw-bin`, `lem:raw-lower-bound`, `prop:analytic-centering`, `eq:mrt-fixed-length`, `eq:analytic-overlap`: bin mass, cutoff deletion, centering, and the placement of the Fourier supremum.
- [qualitative/paths.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/paths.tex), `eq:trace-parameters`, `eq:trace-kernel`, `thm:high-trace`; [qualitative/thinning.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/thinning.tex), `eq:fixed-line-labels`; [qualitative/trace-count.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/trace-count.tex), `lem:trace-integration`, `eq:trace-fubini`: signs are retained during singleton center-prime averaging.
- [qualitative/localization.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/localization.tex), `eq:localization-trace`, `eq:localization-moment`, `eq:exceptional-blocks`, `eq:absolute-degree`: weighted block matrices and an average exceptional-block bound, not a uniform global unweighted norm theorem.
- Quantitative [01-setup.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/quantitative/01-setup.tex), `q:parameters`, `q:bins`; [02-finite-law.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/quantitative/02-finite-law.tex), `q:finite-law`, `q:finite-expansion`; [03-analytic.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/quantitative/03-analytic.tex), `q:center`; [04-paths-trace.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/quantitative/04-paths-trace.tex), `q:trace`, `q:word-comparison-budget`, `q:mixed-difference`: the available growing-parameter alternative.

For the qualitative construction, retain the upstream names
\[
 \epsilon=10^{-4},\quad \eta=10^{-6},\quad
 \kappa=400/\eta,\quad A=e^{2\kappa},\quad c_*=\eta.
\]
Core primes satisfy \(B^{1-\eta}<\log p\le B\); center primes satisfy \(B^{1-\epsilon}<\log p\le B^{1-\eta}\). Write these sets as \(\mathcal C,\mathcal Z\), with reciprocal masses
\(v_C=(\eta+o(1))\log B\), \(v_Z=(\epsilon-\eta+o(1))\log B\).
An admissible \(\mathcal D\) consists of squarefree products of these primes with
\[
 H<d\le\tau H,\quad 1<\tau<2,\quad
 H\le e^{C_0B},\quad \omega(d)\le\lceil C_0\log B\rceil.
\]
For our edges the upstream fixed shift is replaced by \(2h\). This is permitted. The kernel is
\[
 g_d(x,x+2hd)=w_d(x)w_d(x+2hd)A^{\omega_C(d)}1_{d_C\mid x}
 \prod_{p\mid d,\ p\in\mathcal Z}(1_{p\mid x}-\theta/p),\quad \theta=1/4,
\]
\[
 W(x)=(1+A)^{\omega_C(x)}2^{\omega_Z(x)},\qquad
 L_0=\prod_{p\in\mathcal C}(1+A/p)\prod_{p\in\mathcal Z}(1+1/p).
\]
The cutoffs take values in \([0,1]\), depend on core residues, and enforce the stated lower core-degree cutoff; the analytic application chooses a smooth cutoff equal to one near its mean. Bin selection gives
\(\sum_{d\in\mathcal D}A^{\omega_C(d)}/d\ge cL_0/B\).

Fix the alleged bias, then \(\tau,T,C_0\), then \(B,H,\mathcal D\). Only then send the original long cutoff to infinity. Finally increase \(B\). The trace length is \(\ell=2\lfloor B\rfloor\). Blocks have length a power of two \(D_0\asymp B^{10}H\). The high-trace theorem uses the finite residue law modulo \(Q_B=\prod_{p\in\mathcal C\cup\mathcal Z}p\).

## 2. Review of A1+A2 and the finite examples

The scout's abstract implication is correct. With its notation, complete multiplicativity gives exactly
\[
 R_N=\sum_d a_d S_h(\lfloor HN/d\rfloor).
\]
Since \(H\le d\le(1+\varepsilon)H\), the difference from \(VS_h(N)\) is at most \(V(\varepsilon N+1)\). Its directed matrix satisfies
\(C_N=u^TK_Nu\), \(\|u\|_2^2=M_N\), and \(M_N/N\to H\) because all divisor parameters are fixed first. Consequently A1 and A2 imply \(\limsup |S_h(N)|/N\le3\varepsilon\). This is a correct sufficient implication, not an upstream theorem.

For the proposed implementation one must additionally pay for the smooth core cutoffs absent from the scout's raw \(R_N\). The upstream Chebyshev/CRT argument does extend to this deletion: take absolute values of the triple, use \(|\lambda|=1\), and bound the two endpoint-cutoff failures by \(32/T^2\). Complete multiplicativity makes a coprimality exception unnecessary here. The upstream absolute-degree argument likewise permits the Liouville twist when deleting the periodic bad-vertex set or block-boundary edges. **The remaining centering estimate is still cubic.**

The character matrix identities, stationary 76-state renewal law and triple moment \(1/7\), and the finite raw-transfer identity were independently rerun. They pass; their proofs have the stated scopes. Neither finite example models all Liouville arithmetic assumptions. The character counterexample refutes a generic midpoint Schur-multiplier principle, not the particular bound proved in Section 4 below.

## 3. The rank-three observation is correct, but identify the trace first

The proposed symmetric cycle visits
\[
 x,\ x+2hd,\ x+2h(d+e),\ x+2he,\ x.
\]
Its midpoint forms are
\[
 m_1=x+hd,\quad m_2=x+2hd+he,\quad
 m_3=x+hd+2he,\quad m_4=x+he.
\]
They obey \(m_1+m_3=m_2+m_4\). Set
\[
 a=x+hd,\qquad r=h(d+e),\qquad s=h(e-d).
\]
Then the four forms are \(a,a+r,a+r+s,a+s\), and the change of variables has determinant \(2h^2\). Over an odd finite field not dividing \(h\), the unrestricted, uniformly averaged real fourfold product is exactly
\[
 \mathbb E_{a,r,s}f(a)f(a+r)f(a+r+s)f(a+s)=\|f\|_{U^2}^4. \tag{R2.2}
\]
This is an accessible complexity-one system, not four unrelated fixed-shift conjectures. On integers there is a fixed-index sublattice, and restrictions on \(d,e\) remain restrictions after this change. In particular a narrow common bin makes \(s\) much shorter than \(r\).

There is also a trace correction. The upstream qualitative localization uses \(\operatorname{Tr}((M^*M)^2)\), whose steps alternate in orientation. The displayed \(+d,+e,-d,-e\) walk is a symmetric-adjacency trace walk, not an alternating singular-value trace walk. It is among the broader closed lines in the upstream high-trace majorant, but should not be identified with a term of the directed fourth moment.

For the directed fourth moment let sources be \(x_1,x_2\), targets \(y_0,y_1\), and forward labels \(a,b,c,d\), where
\[
 y_0=x_1+2ha=x_2+2hd,\qquad
 y_1=x_1+2hb=x_2+2hc.
\]
Then \(a+c=b+d\), \(x_2=x_1+2h(b-c)\), and its midpoints are
\[
 x_1+ha,\quad x_1+hb,\quad x_1+2hb-hc,\quad x_1+h(a+b-c).
\]
These too have rank three, now in four variables. Their common fiber is
\[
 x_1\mapsto x_1+ht,\qquad (a,b,c,d)\mapsto(a-t,b-t,c-t,d-t). \tag{R2.3}
\]
If only two distinct labels are used in such a fourth-moment walk, the additive relation forces \(x_1=x_2\) or \(y_0=y_1\); the midpoint factors pair off and equal one for Liouville. A genuinely unpaired directed fourth-moment term needs a nontrivial additive relation among labels.

The extra fiber variable in (R2.3) is real freedom, but it does not restore the upstream prime cancellation. Conditional on a fixed midpoint \(m\) and a label \(a\),
\[
 p\mid a\quad\Longrightarrow\quad
 1_{p\mid x_1}=1_{p\mid m},\qquad m=x_1+ha.
\]
When that prime is retained in the label along the fiber, its centered factor has a fixed sign/value determined by \(m\). Translating labels also changes prime-band membership, squarefreeness, the bin, and every cutoff. There is no free uniform residue coordinate independent of the fixed midpoint data. Thus the fiber does not by itself reproduce `eq:trace-fubini`.

## 4. A proved bound for the proposed four-cycle family

**Proposition R2-P (absolute parallelogram bound).** Use exactly the qualitative weights above, the fixed step \(2h\), any admissible divisor family, and any permitted cutoffs. For sufficiently large \(B\), all primes exceed \(2h\). Let \(v_0=x,v_1=x+2hd,v_2=x+2h(d+e),v_3=x+2he,v_4=x\) and
\[
 P_{d,e}(x)=\prod_{i=1}^4\frac{g_{d_i}(v_{i-1},v_i)}{W(v_{i-1})},
 \qquad(d_1,d_2,d_3,d_4)=(d,e,d,e).
\]
For any functions \(U_{d,e}(x)\) bounded in modulus by one,
\[
 \limsup_{X\to\infty}\frac1X\sum_{x\le X}
 \sum_{\substack{d,e\in\mathcal D\\d\ne e}}
 |P_{d,e}(x)U_{d,e}(x)|
 \ll B^{\eta+(\epsilon-\eta)/16+o(1)}P_0^{-2}. \tag{R2.4}
\]
The limit has \(B\) fixed. Constants are uniform in the family and cutoffs. This includes the product of the four Liouville midpoints and all bad-vertex indicators. No Liouville distribution theorem is used.

**Proof.** Drop the cutoffs and bad-vertex indicators from this nonnegative majorant. Retain all vertex-normalization factors at primes in \(d\cup e\); dropping factors from other primes increases the expression. The resulting majorant factors over primes and is periodic in \(x\), so its ordinary mean equals its CRT mean.

If a core prime \(p\) divides \(d\) but not \(e\), the two \(d\)-edges force \(p\mid x\) and \(p\mid x+2he\), impossible since \(p\nmid2he\). The same holds with the labels reversed. Thus a nonzero term requires \(d_C=e_C\).

A common core prime makes all four vertices active in one residue. Its local mean is
\[
 c_p^C=\frac{(A\beta_C)^4}{p}\le\frac1p,\qquad\beta_C=(1+A)^{-1}.
\]
A common center prime similarly has local mean
\[
 c_p^Z=\frac{\beta_Z^4(1-\theta/p)^4}{p}
       +(1-1/p)(\theta/p)^4
 \le\frac1{16p}+\frac1{256p^4},\qquad\beta_Z=1/2.
\]
For a center prime dividing exactly one label, the four vertices occupy two distinct residue classes, with multiplicity two each. On either active class the magnitude of the two relevant edge factors, including normalization, is
\(\theta^2(1-\theta/p)/p\); elsewhere it is \(\theta^2/p^2\). Therefore its exact local absolute mean is
\[
 u_p=\frac{3\theta^2}{p^2}
     -\frac{2\theta^3+2\theta^2}{p^3}
 \le\frac{3}{16p^2}. \tag{R2.5}
\]
The identity \(\beta_Z^2=\theta\) has been used here. This is why retaining the normalization materially improves the calculation.

Since \(d\ne e\) are in the same multiplicative interval of ratio less than two and all their primes exceed two, neither can divide the other. Together with \(d_C=e_C\), this forces at least one center prime in each of \(d\setminus e\) and \(e\setminus d\). Now enlarge the sum to all squarefree prime assignments subject only to these two nonemptiness conditions. The exact enlarged Euler expression is
\[
 \prod_{p\in\mathcal C}(1+c_p^C)
 \left\{\prod_{p\in\mathcal Z}(1+c_p^Z+2u_p)
 -2\prod_{p\in\mathcal Z}(1+c_p^Z+u_p)
 +\prod_{p\in\mathcal Z}(1+c_p^Z)\right\}. \tag{R2.6}
\]
The bracket is nonnegative. Equivalently normalize the four choices at each center prime (absent, common, left-only, right-only) by \(1+c_p^Z+2u_p\). The probability of having both a left-only and a right-only prime is at most the expected product of their counts, hence at most \((\sum_pu_p)^2\). Consequently (R2.6) is at most
\[
 \exp(v_C+v_Z/16+O(\sum_{p>P_0}p^{-2}))
 \left(\frac3{16}\sum_{p>P_0}p^{-2}\right)^2
 \ll B^{\eta+(\epsilon-\eta)/16+o(1)}P_0^{-2},
\]
using \(\sum_{n>P_0}n^{-2}\ll P_0^{-1}\). This proves the assertion. ∎

In particular the all-full-divisibility version vanishes identically for \(d\ne e\): it would require \(d\mid e\) and \(e\mid d\). For \(d=e\), the midpoint product is identically one because both midpoint values occur twice. Thus the suggested symmetric four-cycle has no new unresolved Liouville contribution: the diagonal is untwisted and the off-diagonal has (R2.4).

**Scope.** This is a new bound established in this review for a restricted family of graph walks, not a new Liouville correlation theorem or a demonstrated new-to-literature theorem. General fourth-moment additive-label cycles are not covered. Nor does a fixed fourth moment control the required \(\ell\asymp B\) trace. In particular the right side of (R2.4), although smaller than any fixed power of \(B^{-1}\), is not itself as small as \(B^{-(1+c_*)\ell}\). An insertion into a long walk requires bounds for the rest of that walk and its combinatorial multiplicity.

## 5. Why the naive upstream substitution into A2 actually fails

**Proposition R2-N (large-entry obstruction).** Choose the smooth analytic cutoffs, take a bin with
\(\sum_{d\in\mathcal D}A^{\omega_C(d)}/d\ge cL_0/B\) for fixed \(c>0\), and put \(a_d=A^{\omega_C(d)}\) in the scout's raw sum. Put the undeleted upstream \(g_d\) in its unweighted matrix \(K_N\), including the \(\lambda(d)\lambda(x+hd)\) signs. Then, as \(B\to\infty\),
\[
 \liminf_{N\to\infty}\frac{H\|K_N\|}{V}
 \ge B^{A\eta(\frac12\log A-1)-(\epsilon-\eta)+o(1)}
 \longrightarrow\infty. \tag{R2.7}
\]
Here \(V=\sum_{d\in\mathcal D}a_d\). The claim concerns this explicit undeleted choice only.

**Proof.** Under the full divisor probability law \(A^{\omega_C(d)}/(dL_0)\), the core-prime inclusions are independent with probabilities \(A/(p+A)\). Their mean is
\(\mu=A v_C+o(1)=(A\eta+o(1))\log B\), since \(A\) is fixed before \(B\to\infty\). The elementary Bernoulli Chernoff bound gives
\(\Pr(\omega_C(d)<\mu/2)\le e^{-\mu/8}\).
For clarity, applying Markov to \(e^{-(\log2)\omega_C(d)}\) bounds this probability by \(\exp(-(1-\log2)\mu/2)\le e^{-\mu/8}\).
Because \(A\eta/8>1\), this is \(o(B^{-1})\). A family of probability at least \(c/B\) therefore contains a divisor with \(\omega_C(d)\ge\mu/2\).

For this \(d\), CRT supplies arbitrarily large \(x\) with \(d\mid x\) and both analytic cutoffs equal to one. Indeed, among core primes outside \(d\), prescribe \(r\) residues dividing \(x\) and \(r\) disjoint residues dividing \(x+2hd\), with \(r\) the nearest integer to \(v_C\); prescribe all other core residues to avoid both sites. This is possible since these primes do not divide \(2hd\), exceed two, and there are more than \(2r\) of them. The two standardized counts approach zero, so the smooth cutoffs equal one. At primes of \(d\) prescribe \(x=0\). Hence
\[
 |K_N(x,x+2hd)|=A^{\omega_C(d)}
 \prod_{p\mid d,\ p\in\mathcal Z}(1-\theta/p)
 \ge\tfrac12 A^{\mu/2}
\]
for all sufficiently large \(B\) and, for a fixed such \(x\), all sufficiently large \(N\). Every matrix norm is at least the magnitude of an entry. Also
\[
 V/H\le\tau\sum_{d\in\mathcal D}a_d/d\le\tau L_0,
 \qquad L_0=B^{A\eta+\epsilon-\eta+o(1)}.
\]
These inequalities imply (R2.7). ∎

The upstream proof handles precisely the distinction between rare bad configurations and averaged weighted control: it uses entries \(g_d/\sqrt{W(x)W(y)}\), deletes vertices, and discards an exponentially small fraction of bad blocks in weighted average. It does not assert that rare large unweighted entries disappear. A2 must therefore be implemented with additional justified truncation or replaced by the actual weighted localization argument; it is not an immediate reading of `prop:graph-estimate`.

## 6. What the extra variables and uniformity literature do provide

Primary literature inspected online and saved with response hashes in [the round-two source manifest](../sources/arithmetic_r2/arithmetic_r2_manifest.json):

- Matomäki–Radziwiłł–Tao–Teräväinen–Ziegler, [arXiv:2007.15644v3](https://arxiv.org/html/2007.15644v3), Theorem 1.5/Corollary 1.6: averaged short-interval Gowers uniformity for Liouville at every fixed order on lengths at least \(X^\delta\), fixed \(\delta>0\). Theorem 1.10 gives an absolute average of polynomial correlations over \([X^\delta]^r\) when all polynomial differences are nonconstant. It applies to the four displayed midpoint polynomials on such unrestricted growing boxes. Theorem 1.8's subpower-length statement concerns polynomial-phase/weak uniformity; it should not be silently promoted to arbitrary higher Gowers uniformity.
- Pilatte, [arXiv:2604.26564v1](https://arxiv.org/html/2604.26564v1), Theorem 1.2: the Fourier supremum **inside** the short-interval average is small for lengths at least \(\exp((\log X)^{2/5+\delta})\), fixed \(\delta>0\). Theorem 1.3 states a quantitative inverse formulation with threshold proportional to \((\log\log X)^{-1/2}\). The introduction explicitly discusses higher-order divisor-graph decoupling as a separate missing ingredient. This is an April 2026 primary source, stronger for linear phases than the older \(5/8\) threshold. Its background statement about open binary Chowla is not used against the accepted pinned result.

Three distinctions prevent direct application here.

**Thinness and weights.** A bounded dense-box correlation estimate \(o(XD^2)\) is on the ambient counting scale. Even if a set of label pairs has density \(\delta_D^2\), restricting an absolute-average estimate loses \(\delta_D^{-2}\). There is no inference to \(o(X|\mathcal D|^2)\) without the corresponding rate. Our graph further contains prime divisibility conditions in \(x\), large core weights, and vertex denominators. For trace length \(\ell\), these losses and function systems change with \(\ell\). A fixed-dimensional qualitative \(o(1)\) cannot simply be summed over all these terms. Relative majorants could in principle address this, but none with the required joint residue, bin and midpoint tests has been established here.

**Long-interval uniformity does not control these short boxes.** There is an exact bounded-sign obstruction to any parameter-free replacement of local by global \(U^2\). Partition \(\mathbb Z/(MR)\mathbb Z\) into \(M\) consecutive blocks of length \(R\), assign independent fair signs to blocks, and let \(f\) be the resulting sign function. The expectation of \(\|f\|_{U^2}^4\) is at most \(6/M\): a random parallelogram contributes mean zero unless two of its four vertices lie in the same block, and each pair lies in the same block with probability \(1/M\). Thus some assignment has \(\|f\|_{U^2}^4\le6/M\).
For every assignment, if \(1\le d,e\le D\) and \(4hD<R\), all four midpoint positions lie in a single block outside a proportion at most \(4hD/R\) of starting points. Consequently their local fourfold average is at least
\[
 1-8hD/R.
\]
Let \(M\to\infty\) and \(R/D\to\infty\). Global \(U^2\) tends to zero while the thin-box correlation tends to one. This is not a multiplicative counterexample; it pinpoints the false norm implication. Local uniformity at the actual step scale is indispensable.

**Fixed versus adaptive frequency.** The upstream MRT input controls
\(\sup_\alpha\int |\sum_{n\in I_x}\lambda(n)e(\alpha n)|dx\).
A local \(U^2\) or midpoint-operator estimate generally selects a frequency depending on \(x\), and needs the reverse placement \(\int\sup_\alpha\). The new Pilatte theorem addresses this stronger quantity, but only at the lengths just stated. The upstream fixed-frequency theorem cannot be exchanged for it at fixed \(B\).

## 7. Can the scales be changed while preserving the available estimates?

The qualitative proof alone does not license \(B=B(X)\) in its long-limit statements. Its literal complete-period averaging has
\[
 \log Q_B=(1+o(1))e^B
\]
by the prime number theorem. Requiring even \(Q_B\ll X\) restricts this elementary implementation to \(B\lesssim\log\log X\). Thus \(D_0\le\exp(C_0B+O(\log B))\) is at most a fixed power of \(\log X\), far below the available adaptive-Fourier range. This is a limitation of that implementation, not a theorem that larger \(B\) is impossible.

The quantitative proof does avoid the full period. Its actual parameters are
\[
 L=(\log X)^{1/A_q},\quad A_q\ge1000,\quad A_q>C_1+20,
\]
\[
 J=\left\lfloor\frac{0.005\log L}{6W_q}\right\rfloor,
 \quad \eta_q=e^{-J},\quad K=e^{4J},\quad
 \log(dq)\le100L+1.
\]
Here \(A_q,W_q\) are quantitative constants, distinct from the qualitative \(A,W(x)\). Each label contains one prime from each centered supply \(P_i\), plus a padding divisor \(q\) from disjoint prime supports, weighted by \(4^{\omega(q)}\); the bins have logarithmic width \(\eta_q\), and there are \(O(L/\eta_q)\) of them. The block length is \(M=\lceil e^{103L}\rceil\), and the moment uses \(k=\lfloor L\rfloor\). This is a different construction, not an unrestricted set of all steps below \(M\).

The finite-law theorem requires integer-origin intervals of length at least \(\exp(L^{A_q}/2)\); its scalar extension controls specified residue circuits and coefficient budgets, not arbitrary functions of Liouville midpoints. Increasing \(L\) to \((\log X)^\alpha\) with \(\alpha>2/5\) violates that length hypothesis at origins \(X\exp(O(L))\), since \(\alpha A_q>1\). Keeping the actual \(A_q\ge1000\) gives \(\log M=O((\log X)^{0.001})\), again below the Fourier theorem's threshold. Decreasing \(A_q\) to approximately \(5/2\) would abandon, rather than preserve, the proved finite-law input.

There is a further high-moment budget: summing the quantitative word expansions costs \(\exp(O(L^2\log L))\), and the qualitative target has size \(\exp(-\Theta(B\log B))\). A bare qualitative local-uniformity error, even at an admissible interval length, cannot be multiplied by such costs without proof of a compatible quantitative estimate. Enlarging blocks while keeping short steps leaves a thin diagonal band; the global/local counterexample above explains why that maneuver alone does not solve the problem.

A diagonal choice of \(B(X)\) in qualitative limits can grow arbitrarily slowly. It does not guarantee the lower bound on \(B(X)\) required for adaptive-Fourier uniformity. No overlap of the *stated* scale contracts was found. A new finite-origin comparison or a much shorter-interval adaptive-Fourier result would be a substantive additional theorem, not parameter tuning.

## 8. Cubic centering: an exact simplification and the remaining analytic loss

There is useful Liouville-specific algebra beyond the scout's single-prime illustration. Use the canonical coefficients \(\lambda(d)\), set \(d=uw\) when expanding the center constants, and substitute \(x=uz\). Since \(u,w\) are coprime and squarefree,
\[
 \lambda(uw)\lambda(u)^3(-\theta)^{\omega(w)}
 =\lambda(w)(-\theta)^{\omega(w)}
 =\theta^{\omega(w)}. \tag{R2.8}
\]
Thus the non-raw terms in the centered cubic sum have **nonnegative arithmetic coefficients** after multiplicative rescaling. Up to their endpoint cutoffs, they are
\[
 A^{\omega_C(u)}\frac{\theta^{\omega(w)}}w
 \sum_{z\le X/u}\lambda(z)\lambda(z+hw)\lambda(z+2hw),
 \quad w>1,\quad uw\in\mathcal D. \tag{R2.9}
\]
The cutoffs are evaluated at \(uz\) and \(u(z+2hw)\); all core factors of \(d\) lie in \(u\). In particular it would be unnecessarily pessimistic to insist that these particular coefficients are arbitrary adversarial phases. Their positivity does not control the signs of the triple correlations, however. A1 still needs an estimate on (R2.9) at the terminal scale.

I also checked the literal two-frequency extension of the upstream analytic-overlap calculation. For three local Fourier transforms \(A_y,B_y,C_y\) at interval length \(D\asymp_h H/u\), the multiplier is evaluated at a linear combination of two frequencies, and the integrand has the shape
\[
 Q(\alpha+2\beta)A_y(-\alpha-\beta)B_y(\alpha)C_y(\beta).
\]
The binary small-multiplier estimate uses an \(L^2\)-\(L^2\) product of size \(D\). Here the elementary bound is
\[
 \iint |A_y(-\alpha-\beta)B_y(\alpha)C_y(\beta)|\,d\alpha d\beta
 \le \|A_y\|_2\|B_y\|_2\|C_y\|_1\le D^{3/2},
\]
up to fixed interval-length constants. Dividing by the overlap length leaves a loss \(\sqrt D\). The upstream threshold \(B^{-1-\epsilon}\) and rough-multiplier fourth-moment estimate do not absorb this exponentially large loss. This identifies a failed estimate in the attempted proof, not a lower bound saying every trilinear argument must lose \(\sqrt D\).

For entirely arbitrary shift weights, a further warning is exact: the four forms \(z,z+w,z+2w,w\) admit the quadratic identity
\(z^2-2(z+w)^2+(z+2w)^2-2w^2=0\). Quadratic phases on the first three forms and their cancelling shift weight give no cancellation despite small linear Fourier coefficients. The full weighted system cannot be controlled by unrestricted \(U^2\) alone. This does not refute a bound for the special positive weights (R2.8); it explains why an arbitrary-coefficient generalization of the binary proof is stronger than the task actually requires.

## 9. The unresolved high-trace step, stated precisely

For any closed walk in which each unoriented edge occurs an even number of times, its Liouville-midpoint product is exactly one. Its outside \(\lambda(d_i)\) factors also cancel. These walks retain their upstream contributions. Section 4 additionally controls the specified distinct-label parallelograms without any midpoint cancellation.

The remaining unpaired walks cannot be treated by deleting the midpoint factors inside a signed CRT expectation. At a qualitative good singleton prime, the upstream proof balances a lit residue contribution of order \(\theta/p\) against the unlit residues and obtains order \(\ell/p^2\), using \(\theta=\beta_Z^2\). The midpoint factor depends on the actual integers, so it is neither an independent residue coordinate nor one of the allowed core cutoffs. In the quantitative proof the same issue is the exact identity
\[
 \mathbb E[(1_{Z=a}-1/p)F(Z)]
 =p^{-1}\mathbb E[F(a)-F(Z)].
\]
Originally \(F\) is a controlled deletion predicate; its mixed differences are estimated by rare prohibited paths. With midpoint factors inserted, differences of Liouville products appear as well. The trivial difference bound is two per singleton; it removes the cancellation the proof needs. The finite-law theorem does not compare these new tests.

This failure is algebraic: even with no deletion predicate, taking \(F(a)=1\) and \(F(z)=-1\) otherwise makes the displayed expectation \(2(1-1/p)/p\), rather than zero. It shows why preserving the marginal residue law is insufficient; a joint estimate with the inserted factors is needed. It is not evidence that Liouville realizes this adversarial function. Averaging over numerical prime labels might prove the required joint estimate, but those labels are products, satisfy closure relations and short-bin restrictions, and enter \(\ell\asymp B\) midpoint arguments. Neither the fixed-dimensional dense-box results nor the upstream binary theorem supplies that estimate.

The practical conclusion is narrower and more useful than “four-point Chowla is unknown”: the initially proposed two-label four-cycle is already harmless, raw A2 is misnormalized for the upstream kernel, and the remaining arithmetic work lies in general additive-label cycles and singleton-prime dependence, together with the specific positive-weight centering sum (R2.9).

## 10. Validation and status

Run:

```
python openai-proof-research/frontier/experiments/arithmetic_r2_checks.py
```

[Exact output](../sources/arithmetic_r2/arithmetic_r2_validation.json) verifies local common/unique-prime factors at primes 5, 7, 11, 17, 31 and two shifts; the Euler-product sum and its nonnested-label refinement; both midpoint ranks and the directed fiber; all two-label directed fourth cycles; the cubic sign identity; and the first scout's character, renewal and dilation checks. Rational arithmetic is used. The asymptotic propositions above have proofs independent of these finite checks.

**Proved in this round:** a restricted divisor-graph four-cycle bound using actual upstream normalization; failure of the explicit undeleted implementation of A2; corrected trace geometry and centering signs; an exact obstruction to replacing local by global uniformity.

**Not proved:** A1, a useful midpoint analogue of the full upstream high-trace/localization theorem, ordinary three-point Chowla for any fixed nonzero shift, or any new named MathDB result. No novelty priority or MathDB ranking is claimed. The four-cycle estimate is structural arithmetic progress within the attempted graph analysis, not new cancellation for Liouville itself.

Only this review, `arithmetic_r2_checks.py`, and uniquely named files in `frontier/sources/arithmetic_r2/` were written. No shared index, original scout, pinned source, or original experiment was edited; no staging, commit, or further delegation was performed.
