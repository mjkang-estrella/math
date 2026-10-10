# R002: the undeleted unweighted kernel fails the proposed norm target

**Status: proved obstruction to one specific attempted proof, not a disproof of Chowla, the accepted upstream theorem, or the abstract A1+A2 criterion. Literature priority is not claimed.** The obstacle is a mismatch between a global unweighted matrix norm and upstream weighted localization with deletions.

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


For each fixed scale, let `K_N` be the matrix of the first scout's A2: its row/column index set is `1,...,floor(HN)+2h max(D)` and its entries for `x<=floor(HN)` are

\[
K_N(x,x+2hd)=\lambda(d)g_d(x,x+2hd)\lambda(x+hd),
\]

with all other entries zero. A2 would require `H ||K_N|| / V` to become arbitrarily small in the prescribed order of limits, where `V=sum_d A^{omega_C(d)}`. The proposition below instead shows divergence for the stated undeleted kernel.

## Statement and proof


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


## Source and validation

The accepted source is family 007 at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`: [graph setup](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/graph-setup.tex), [analytic transfer](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/analytic-transfer.tex). Full context and limitations: [round-two report](../reviews/arithmetic-bridge-r2.md).

The parent independently checked the proof against the displayed source kernel and reran `python openai-proof-research/frontier/experiments/arithmetic_r2_checks.py`; all exact checks passed. These checks validate finite algebra, not an asymptotic conclusion by themselves. No proof-assistant verification or human peer review was performed.
