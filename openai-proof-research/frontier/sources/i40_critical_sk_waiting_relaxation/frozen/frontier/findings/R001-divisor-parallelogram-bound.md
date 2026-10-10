# R001: a restricted divisor-graph parallelogram bound

**Status: proved technical lemma within an incomplete Chowla approach. No new Liouville correlation case or named conjecture is solved, and literature priority is not established.** This corrects the first scout's suggestion that this particular four-cycle necessarily requires an unknown four-point estimate. It is a symmetric-walk bound, not the entire directed singular-value trace theorem.

## Exact setting

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


## Statement and proof


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


## Source and validation

The accepted source is family 007 at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`: [graph setup](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/graph-setup.tex), [analytic transfer](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/analytic-transfer.tex). Full context and limitations: [round-two report](../reviews/arithmetic-bridge-r2.md).

The parent independently checked the proof against the displayed source kernel and reran `python openai-proof-research/frontier/experiments/arithmetic_r2_checks.py`; all exact checks passed. These checks validate finite algebra, not an asymptotic conclusion by themselves. No proof-assistant verification or human peer review was performed.
