# R009 — Weighted capacity for four-state reconstruction with arbitrary edge channels

Date: 2026-10-08. **Accepted as the third substantial deduction under the stipulated pinned corpus.** The [complete proof](../iterations/i08-variable-channel-capacity.md) passes the [independent proof audit](../reviews/i08-variable-capacity-r2.md). The separate [final prior-art and significance review](../reviews/i08-variable-capacity-novelty-r3.md) recommends acceptance of the uniform sufficiency argument. The parent read both reviews in full and reproduced their checks. Worldwide priority is not established.

The accepted scope includes **all locally finite trees**, with no common bound on the numbers of children. The [locally finite strengthening](../iterations/i11-locally-finite-capacity.md), its degree-independent quantitative bounds and zero-edge pruning pass a separate [proof review](../reviews/i11-locally-finite-capacity-r4.md). The parent read that review and reproduced its five source identities and 17 artifact hashes. These are extensions of the same finding, not another count.

## Exact theorem

Let T be a deterministic rooted locally finite tree: every vertex has finitely many children, without a common upper bound. Finite trees and zero or one child are allowed. Independently along edges conditional on parent spins, broadcast a uniform four-state root through the known channels

\[
 P_e(j\mid i)=\lambda_e\mathbf1_{i=j}+(1-\lambda_e)/4,
 \qquad 0<\lambda_e\le1.
\]

No uniform lower bound on the positive parameters, or upper bound below one, is assumed. Let a_n be the expected total-variation distance from uniform of the root posterior given all depth-n spins. Put

\[
 r_e=\lambda_e^2,\qquad R_\rho=1,\qquad
 R_v=\prod_{e\in[\rho,v]}r_e.
\]

For a nonnegative conserved flow theta of finite mass from the root to infinity, define

\[
 V(\theta)=\sup_{\xi\in\partial T}
  \sum_{e=(v,w)\in\xi}(1-r_e^2)
       \left(\frac{\theta(e)}{R_w}\right)^2,
 \qquad
 C(T)=\sup\{|\theta|:V(\theta)\le1\}.
\]

Then

\[
 \lim_{n\to\infty}a_n>0\quad\Longleftrightarrow\quad C(T)>0.
\]

The information limit exists by data processing. Capacity may be infinite, for example on a perfect ray. Its positivity is equivalently the existence of a positive finite-mass flow with finite potential. The theorem concerns the observed deterministic tree and parameters, ferromagnetic symmetric four-state channels, and ordinary level reconstruction. No asymmetric, antiferromagnetic, or other-alphabet conclusion is asserted.

Writing `m_infty=lim_n E|Lp_root^(n)|^2`, the extension also proves

\[
 \frac{1}{20000}\frac{C(T)}{\sqrt{1+C(T)^2}}
 \le m_\infty\le\min\{3,C(T)/\sqrt\kappa\},
 \qquad \kappa=\frac{2/3000}{(1+9/3000)^3}.
\]

The fraction tends to one at infinite capacity. Zero-channel edges are allowed by deleting them and computing capacity on the root's positive-edge component. The entire collection of removed observations is jointly independent of the root and retained observations, by independent refresh variables at the first zero edges. A finite root component has capacity and limiting information zero.

## Proof dependencies and additional argument

All corpus premises are accepted at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The exact input is the preserved posterior class in *A Capacity Criterion for Four-State Potts Reconstruction on Trees*, `build/main.tex`, `prop:companion` / `eq:moment-saving`, citing the threshold companion's Proposition 3.2. It contains revealing and uninformative laws, is closed under every channel parameter in `[0,1]` and finite conditionally independent products, and gives, with `c=1/1000`,

\[
 m(\mu\star\nu)\le m(\mu)+m(\nu)
 -c\{E_\mu[A^2]m(\nu)+m(\mu)E_\nu[A^2]\}.
\]

Here `x=Lp` uses the source's tetrahedral coordinates, `A=|x|^2`, `m=E A`, and `h=|E x_1x_2x_3|`. The source's global capacity theorem fixes one common parameter strictly between zero and one. Its converse uses channel smoothing and a geometrically summable bound that is not uniform near perfect transmission.

The full proof linked above supplies the following new argument; this description is not a substitute for it.

1. Feasible posterior coordinates satisfy `Z=1+x.y` in `[0,4]` and `|N_i|<=Z` in the Bayes product. They give uniform unsmoothed bounds
   `m_product>=a+b-7(h_mu b+a h_nu)` and `h_product<=h_mu+h_nu+460ab`, including zero-normalizer pairs. The weighted integrands, rather than the posterior vector itself, extend continuously at `Z=0`.
2. A scaled capacity flow gives profiles `X_v=epsilon theta(v)/R_v` bounded by `epsilon sqrt(1+|theta|^2)`. Independent terminal channels produce exactly the prescribed small quadratic information. The local deficit retains the splitting factors `t_vw(1-t_vw)` and vanishes at unary vertices.
3. On a flow-sampled ray, with `alpha_i=1-t_(i+1)`, the weighted energy controls `E sum alpha_i X_i^2`. The kernel `K_ij=product_(i<k<=j) sqrt(t_k)` has alpha-weighted row and column sums at most two. The identity `X_i X_j product lambda_k=X_i^(3/2)X_j^(1/2)K_ij`, followed by Young's inequality, bounds accumulated loss without geometric channel decay. A depth-independent choice of terminal noise leaves positive root information.
4. Necessity adapts the source's cubic change of information variable to construct a conserved flow. The extension uses the binary inequality `g(m_product)<=g(a)+g(b)` with `g(t)=t+t^3/3000`, iterated over every finite child set. Its potential telescopes with precisely the factor `1-r_e^2`. The finite-depth class argument is passed to numerical moment limits; membership of a limiting posterior law is not assumed.

## Significance and prior-art limits

The contribution is the uniform comparison between **actual four-state boundary experiments** and weighted nonlinear capacity when channels can approach or equal perfect transmission. The capacity formalism itself, series laws, and near-perfect obstruction are not new.

The final review reads Pemantle–Peres's variable-interaction Ising capacity results, the binary electrical criterion, homogeneous Potts threshold work, entropy-contraction criteria, robust reconstruction, and older inhomogeneous Potts extremality results. It distinguishes Ising free-boundary information from plus-boundary magnetization, and worst-ray energy from electrical energy. It also tests common-channel subdivision, capping and rounding channels, contraction of perfect clusters, moving noise to terminals, binary encodings, and revealing copy/refresh flags. None supplies the full four-state comparison. In particular finite-depth continuity does not permit interchanging a channel approximation with the infinite-depth information limit.

Variable channels uniformly bounded above by a fixed constant below one admit a routine adaptation of the old proof; that range alone would not merit this finding. A ray with `lambda_j=1-1/(j+1)^2` has limiting advantage `3/8` and weighted unit-flow potential `15`, while the unweighted substituted potential diverges. This checks the weighting but is not the novelty claim: the analogous near-perfect defect was recognized in earlier Ising work.

For named-problem context, the parent inspected [MathDB 317819, Mezard–Montanari's Kesten–Stigum conjecture](https://mathdb.com/p/317819/mezard-montanari-s-kesten-stigum-conjecture-for-the-potts-mo). It concerns homogeneous regular trees and relates root information to `d lambda_2^2>1`. That four-state homogeneous scope is already addressed by the stipulated corpus. R009 advances the heterogeneous tree problem beyond that baseline; it is not advertised as another solution of the already-assumed homogeneous theorem or as a stochastic-block-model algorithm. The page gives no numerical significance score or featured designation for this work, and none is claimed. Its unrefreshed status is not evidence against or in favor of our premises.

The qualitative locally finite extension also follows from the new bounded-child result by replacing each finite child set with a finite binary routing tree of perfect-copy edges. Capacity is unchanged; the original and encoded separating observations are cofinal and have the same limiting information. This is a routine corollary of R009, not of the old fixed-channel theorem, which excludes perfect edges. The earlier bounded-degree fixed-channel gadget obstruction must not be generalized to arbitrarily large finite gadgets. The direct proof adds universal quantitative constants within the same finding.

Local finiteness cannot be removed: a root with one perfect finite chain of each positive length has a revealing vertex at every depth, but every conserved countably additive flow is zero and there is no infinite ray.

## Validation and acceptance boundary

The proof audit independently checks the polynomial identities, 144 ordered posterior-law pairs including 370 zero-normalizer atom pairs, four asymmetric finite flow trees, actual finite channel products, and exact ray telescopes. The parent reproduced these checks and their source/artifact verification in commit `5a9d256`.

The separate contribution audit verifies 41 pinned source files against the complete Git tree, retains 11 primary PDFs, and seals 101 artifacts. Parent reruns of its `check.py` and `verify.py` pass, including exact channel composition, subdivision, noise-placement and kernel diagnostics. These finite tests are supporting checks; the infinite theorem rests on the written proof and its independent review. The reviewed candidate and proof-review hashes are unchanged.

**Parent decision:** accept one substantial, nonroutine deduction under the pinned corpus, with novelty confined to the uniform four-state sufficiency argument. The project has no independent proof of the corpus premises, worldwide-priority certificate, human peer review, or formal proof certification for this deduction. No publication or external submission has been made. The original proof artifact is preserved, including its historical pre-acceptance status line; this finding record and the ten-finding ledger govern current acceptance.
