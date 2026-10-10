# Iteration 07: parent probability and quantum-information screen

Date: 2026-10-08. Status: **research checkpoint; no additional accepted finding**. This screen is independent of the arithmetic, geometric-analysis and structural-mathematics tasks. All pinned premises use `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Candidate decisions

| Candidate | Evidence and decision |
|---|---|
| Four-state reconstruction on arbitrary bounded-degree trees | Already exactly covered by the capacity companion in family 229. Reject as a new result. |
| Four-state reconstruction with nonconstant edge channels approaching noiseless transmission | The fixed-channel theorem does not cover this. A naive capacity extension is false. A weighted necessary condition below survives, but sufficiency remains open in this investigation. Retain as a possible future substantive bridge; do not count the necessary condition alone. |
| Three-state reconstruction on general trees | The inspected three-state proof uses identical fixed-point laws and regular/Poisson factorial moments. Its mixed-message negative-channel inequalities are useful, but they do not supply an arbitrary-tree capacity comparison. No complete bridge supplied; defer. |
| Strong converse for generalized amplitude damping | The current primary preprint has the exact same result, including its exponent, in Theorem 1. Reject this proposed target rather than treating an older search snippet as current prior art. |
| EPnI with quantum conditional entropies | The straightforward extension is false, even when the relevant conditional entropies are positive. The established conditional-EPI optimality theorem supplies a strict obstruction below. Reject this target. |

The amplitude-damping source itself already includes arbitrary-partner Holevo, minimum-output-entropy and classical-capacity additivity. The EPnI source already includes constrained entropy minima for identical thermal attenuators and a two-receiver broadcast region. These direct applications do not offer new countable findings.

## Exact corpus interfaces

The [retrieval manifest](../sources/i07_parent_screen/retrieval-manifest.json) contains 32 TeX files, each verified against its Git blob in the complete preprint tree. The [retrieval script](../experiments/i07_parent_screen/retrieve.py) is reproducible. Catalogue prose is not used in place of the following actual statements.

1. **A Capacity Criterion for Four-State Potts Reconstruction on Trees**, `build/main.tex`, `thm:main`: deterministic tree, at most B children, one fixed parameter 0<λ<1, reconstruction iff its L³ capacity with resistance λ^(−2 depth) is positive. The proof treats zero- and one-child vertices too.
2. The same manuscript, `prop:companion` / `eq:moment-saving`: the preserved posterior-law class contains revealing and uninformative experiments, is closed under channels with *any* parameter in [0,1] and conditionally independent products, and satisfies
   m(μ⋆ν) ≤ m(μ)+m(ν)−c(Eμ[A²]m(ν)+m(μ)Eν[A²]), c=1/1000.
   This precise closure permits the nonconstant-edge necessity argument below. The companion input is an accepted premise, not independently re-proved here.
3. The same manuscript, `lem:local-moments`: quadratic-information lower bound has constant 7, while the third-moment upper bound is stated with C(λ). Its proof uses a denominator bounded below by 1−λ. In sufficiency, `eq:uniform-loss-bound` uses the summable kernel λ^(j−i), with total cost proportional to 1/(1−λ).
4. **The exact reconstruction threshold for the three-state symmetric channel**, `sections/03-positive.tex`: `pos:additive`, `pos:moment-bounds` and `pos:correlation-bound` concern a common limiting fixed-point law with dλ²=1. The coefficient α uses the regular or Poisson factorial moment. Section `04-local.tex`, `loc:pair` permits distinct pair messages, but `loc:gap` subsequently returns to a common fixed-point law. These are not an arbitrary-tree reconstruction criterion.
5. **Classical capacity and entropy inequalities for generalized amplitude damping**, `sections/partners.tex`, proof of `cor:partner-additivity`: all finite-dimensional CPTP partner channels are allowed. Entropy additivity is not by itself a Rényi estimate above order one.
6. **The entropy photon-number inequality**, `sections/00-introduction.tex`, `thm:epni`: independent input ports, arbitrary internal multimode entanglement, finite energy. It does not permit replacing ordinary entropies with conditional entropies of ports sharing quantum memory.

## A variable-edge necessary condition

This is a proved preliminary extension of the source's necessity argument, **not a substantial accepted finding**. Its derivation is close to the source proof, and independent review has not yet been commissioned.

Let T have at most B≥1 children per vertex. Associate to edge e=(v,w) a four-state symmetric ferromagnetic channel parameter 0<λ_e<1, with uniform root. Put

\[
 r_e=\lambda_e^2,\qquad R_\rho=1,\qquad
 R_w=\prod_{e\in[\rho,w]}r_e.
\]

For a nonnegative conserved flow θ to infinity, define

\[
 \mathcal V(\theta)=\sup_{\xi\in\partial T}
 \sum_{e=(v,w)\in\xi}(1-r_e^2)
       \left(\frac{\theta(e)}{R_w}\right)^2,
 \qquad
 \mathcal C(T)=\sup\{|\theta|:\mathcal V(\theta)\le1\}.
\]

**Necessary condition.** If level observations reconstruct the root, then C(T)>0. No uniform separation of λ_e from one or zero is assumed.

**Proof.** Let m_v be the limiting quadratic information about the spin at v from levels of its descendant subtree. Data processing gives the limit in [0,3]; reconstruction gives m_ρ>0. For the finitely many children w of v write b_w=r_(v,w)m_w, S=Σb_w and

\[
 D=\max_{w\ne w'}b_wb_{w'}(b_w+b_{w'}),
\]

with D=0 if fewer than two children exist. At finite depth, combine the maximizing pair first and use the accepted moment-saving inequality and Jensen. Combine other children by subadditivity and pass to the limit. This proves m_v≤S−cD. As in the source, S³≤Σb_w³+B³D: each mixed monomial is bounded by D and there are at most B³ ordered triples.

Choose K=c/B³ and let y_v=m_v+Km_v³. Then

\[
 y_v\le S-cD+KS^3\le S+K\sum_w b_w^3
 =\sum_w r_e y_w-K\sum_w r_e(1-r_e^2)m_w^3.
\]

Since y_w≤(1+9K)m_w, set a=2K/(1+9K)³ to obtain

\[
 y_v\le\sum_w r_e y_w
       \left(1-\frac a2(1-r_e^2)y_w^2\right)
 \le\sum_w\frac{r_e y_w}
                   {\sqrt{1+a(1-r_e^2)y_w^2}}.
\]

The last inequality follows from (1+2t)^(−1/2)≥1−t for t≥0. Select coefficients d_e between zero and the displayed coefficient r_e/√(1+a(1−r_e²)y_w²) so that y_v=Σd_e y_w; multiply all upper-bound coefficients by a common ratio when necessary. Set ℓ_ρ=1, ℓ_w=ℓ_vd_e, and θ(e)=ℓ_wy_w. This is a conserved flow of mass y_ρ. With g_v=ℓ_v/R_v,

\[
 a(1-r_e^2)\left(\frac{\theta(e)}{R_w}\right)^2
 \le g_v^2-g_w^2.
\]

Telescoping along each ray gives aV(θ)≤1. Thus √a θ is admissible for C(T) and has positive mass √a y_ρ. All finite subtrees use the preserved posterior-law class; the argument does not require membership of a limiting law in that class. ∎

### Why the weight matters: an exact ray example

On a single infinite ray let λ_n=1−1/(n+1)² for edge n≥1. The product through depth n is

\[
 P_n=\prod_{j=1}^n\lambda_j=\frac{n+2}{2(n+1)}\longrightarrow\frac12.
\]

Symmetric channels compose by multiplying their parameters. The posterior given the endpoint is therefore a four-state channel row with parameter P_n. Its total-variation distance from uniform is 3P_n/4, tending to 3/8. Reconstruction holds.

The naive replacement of λ^(−2 depth) by R_n^(−1)=P_n^(−2) in the *unweighted* capacity has zero capacity: every nonzero ray flow is constant, and ΣP_n^(−4) diverges. In contrast,

\[
 \sum_{j=1}^n(1-\lambda_j^4)P_j^{-4}
 =P_n^{-4}-1\longrightarrow15.
\]

The weighted capacity is exactly 1/√15 on this ray. The example invalidates the naive extension, without challenging any accepted fixed-channel theorem.

### Remaining substantive step

It is not established here that C(T)>0 is sufficient for reconstruction on every bounded-degree variable-channel tree. Copying the fixed-channel proof is insufficient: its third-moment constant and geometric path-kernel bound deteriorate as λ approaches one, and weighted capacity alone does not bound the unweighted sum of profile squares on a ray. A new estimate must respect the factors 1−λ_e⁴ or use an appropriate coarse-graining argument without silently losing the bounded-degree hypotheses. The ray example tests a proposed criterion; it does not prove its sufficiency.

## Two quantum-information exclusions

**Current prior art for amplitude damping.** [Kun Fang, arXiv:2609.14621v2](https://arxiv.org/pdf/2609.14621v2), Theorem 1, states the exact strong-converse exponent for every damping and thermal parameter, using additive sandwiched Rényi Holevo information for all orders above one. The version history reports revision on 6 October 2026. Earlier indexed descriptions concerned only a capacity bound. The exact proposed extension is therefore already claimed with a full proof in this current primary manuscript; it is not pursued as a new result. This screen is not an independent audit of that external proof.

**Quantum-memory EPnI obstruction.** [De Palma–Trevisan, arXiv:1706.00440](https://arxiv.org/pdf/1706.00440), Theorem 7, gives Gaussian sequences conditionally independent over quantum memory that asymptotically attain the conditional entropy-power bound for prescribed input conditional entropies. Apply it at equal mixing, with limiting input entropies g(1) and g(3). The limiting output entropy power is

\[
 \tfrac12 e^{g(1)}+\tfrac12 e^{g(3)}
 =\tfrac12(4+256/27)=182/27.
\]

A conditional EPnI would instead require a limiting output entropy at least g(2), whose exponential is 27/4. The ratio is 729/728>1. By continuity, sufficiently late finite-energy states in that sequence violate the proposed conditional EPnI. Both input conditional entropies are positive eventually. This is a direct consequence of established optimality, not a new countable finding.

## Validation and next action

The [exact checker](../experiments/i07_parent_screen/check_ray.py) verifies 1,000 finite telescoping/product identities and the exact entropy-power ratio; [output](../sources/i07_parent_screen/exact-checks.json) is retained. These checks do not prove the general necessary condition or the missing converse. The [literature manifest](../sources/i07_parent_screen/literature-manifest.json) records two successful PDF downloads and the failed Pemantle–Peres download (HTTP 403); no uninspected assertion from that failed download is used above. The conditional-EPI download is recorded by content hash rather than a version-specific URL.

Keep the variable-channel sufficiency problem as an unproved research option. Do not increase the 2/10 accepted count. The three delegated discovery tasks remain responsible for independent candidate development; no additional agent was launched by this screen.
