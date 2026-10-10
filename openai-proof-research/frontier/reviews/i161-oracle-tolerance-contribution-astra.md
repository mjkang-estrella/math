# I161 — Independent contribution gate for the full R154 theorem

**Recommendation: TECHNICAL ONLY under the project's operation-based substantiality standard. Preserve I159's PASS without substantive repairs for the unchanged original R154 proof.** I found no new mathematical objection. This is not an exact-duplicate finding, a formal proof certificate, or a claim of worldwide priority or absence. Eight accepted findings remain eight; no acceptance edits are made.

The decisive positive evidence is the source's *proof* of fixed-seed stability (`implementation.tex`, lines 523–565), together with the constant final row sums in `numerics.tex`, lines 627–644. The source already uses routine-height induction, small coefficient feedback, anchor propagation, and oracle-independent seed maps. Removing its allowed polylogarithmic slack requires tracking constants in that same induction, not a new stability mechanism. Once that is done, the causal perturbation is handled by Gaussian mixture entropy and a common conditional-state kernel; the last-window regularization is precisely existing shifted composition. Sections 3–6 below give the full reduction, including the actual compiler, adaptivity, intrinsic errors, unnoising, finite dimensions, and every-execution costs.

## 1. Scope, standard, and preserved history

The statement reviewed is exactly

$$
\forall\epsilon>0\ \exists c_\epsilon,C_\epsilon>0,\mathcal A_\epsilon\
\forall d\ge2,\ V,\ \text{admissible causal strategies}:
\quad Q\le C_\epsilon d^\epsilon\ \text{on every run},\qquad
\operatorname{TV}(\mathcal L(X),\pi_V)\le1/10.
$$

Here $V\in C^2(\mathbb R^d)$, its supplied minimizer is $0$, $V(0)=0$, and $I\preceq\nabla^2V\preceq2I$. Value errors have absolute size at most $c_\epsilon$; gradient errors have **Euclidean** norm at most $c_\epsilon$. Replies can be biased, discontinuous, inconsistent and stateful, depending measurably on current/past queries and replies, but not future private algorithm draws. Computation between real queries is unrestricted.

This does not assert a common positive tolerance for all $\epsilon$, finite-bit complexity, arbitrary-accuracy sampling, or just expected query cost. No consistent approximate potential is substituted. The entire statement, not a Gaussian subcase or a Wasserstein error floor, is the subject of the recommendation.

All OpenAI theorems **and lower proof operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. I do not audit their truth or use contradiction/ex-falso. External papers are ordinary evidence. The project's standard, including its I30 and I36 dispositions, permits TECHNICAL ONLY without a printed duplicate when a concrete full-scope reduction pays the claimed bridge. A longer proof, stronger conclusion, or historically unresolved target is not alone sufficient for SUBSTANTIAL.

Original R154 SHA-256: `1878b68a5482aba8807f4d910465f83b43d86d401af1a53d038cfebc40b08be1`.
Original I159 review SHA-256: `02b8127f7a0d42a1b3585378cf056e7deda247a5f9d94c2c63fcfa030226a87c`.
Mandatory I159 task SHA-256: `e74c8efdd407ed4eca67669101b00aa573e0feeb517e0ae0d3a0d8b0b415a116`.
Original I160 task SHA-256: `c48357e7f6b7984633649ccb4616eaebc3fac046053f0b04d1ec6a7cf52b397d`.

I160 stopped at a provider usage limit, not a mathematical verdict. Its unfinished preparation is preserved, not executed or promoted to a completed gate. Historical I157 remains **INCOMPLETE**, with its original unresolved verdict. Its unrelated torus/decoder/weighted-bin/PDE obligations are not prerequisites newly imposed here. I159's R154-only scope was a parent-selected assignment under continuing user authorization, not a new direct user mathematical instruction; its contrary wording is not adopted. The blanket internal-reserve independence claim from I152 remains **FAIL**. Earlier parked branches and failures are unchanged.

## 2. What the strongest source operations already supply

All eight upper-bound files were freshly read through their endings in this I161 session: `introduction.tex`, `preliminaries.tex`, `jets.tex`, `divergence.tex`, `centering.tex`, `numerics.tex`, `implementation.tex`, and `sampling.tex`. They are in

`preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/build/sections/`.

The owned read log gives LF line ranges and passage hashes; the flat map binds the original Git blobs. The complete dependency closure includes the analytic estimates that pay intrinsic approximation. No external Picard theorem is silently made a premise of those stipulated source operations.

| R154 component | Available operation and residual work |
|---|---|
| Small feedback at every reachable call | Source numerical row sums and compiler label/scale descent; already uniform in centers and seeds |
| Constant fixed-seed Lipschitz bounds | Source `lem:compiler-lipschitz` proof; replace allowed polylog slack by finitely many height constants |
| Inconsistent-error propagation | Same scalar induction with an additive forcing term; compare exact children at moved centers, never differentiate noisy replies |
| Entropy per noisy step | Untouched **standalone** final reserve, Gaussian translation identity, mixture convexity |
| Arbitrary causal memory | Replace visible marginal and retain the same conditional next-state kernel; KL chain rule under actual prefixes |
| Fixed-time regularization | Shifted Composition I, Theorem 3.2/Remark 3.4; also the zero-local-error case of III's §3.1 |
| Warm-up, intrinsic error, final target | Source proximal contraction, ideal-prefix moments, variance-halving descent and mode-Gaussian termination |
| Every-run cost and all dimensions | Source prescribed circuits/loops and capped rejection, with the finite minimum of permissible tolerances |

This is an operation-level reduction, **not** a claim that the source's printed exact-oracle main theorem alone entails noisy-oracle robustness.

## 3. Strongest plausible residual: dimension-uniform compiler robustness

The strongest case for substantiality is that inverse-power tolerance was known in I152, while fixed tolerance with arbitrary nonconservative errors remained unpaid. A polylogarithmic error factor cannot simply be called a constant; one-step Gaussian smoothing also loses $h^{-1/2}$. It is therefore necessary to establish the two improvements, not cite general numerical stability.

Here the first improvement is already structurally contained in the source proof. Write $\lambda\le\delta=d^{-e}$, $0<r\le1$. The terminal formulas (`implementation`, 228–236) are

$$
M=g(x+rZ)+\sigma G,\qquad
S_{\rm pre}=Z-rg(x+rZ)+(\sqrt3s/2)G_1.
$$

Their center sensitivities are $\lambda,r\lambda$; their response perturbations are $u,ru$. In every nonterminal call the direct centers are $x+r(\ell y+mG)$ with $|\ell|,|m|\le1$, child scales are $r\tau\le r$, and the absolute row sums satisfy

$$
A_M=C_1(1+\log d)^{C_1}[(r/\sigma)\delta^{-4t-10w}+r^2],
\quad A_S=C_1r^2,\quad A_{f,M}=C_1,\quad A_{f,S}=C_1r.
$$

The M final direct term is independent of its position anchor; the S anchor is a fixed Gaussian seed. Requested child noises, residual square roots, and seed transformations depend only on scalar parameters, not responses or centers. They cancel in a fixed-seed comparison, including transformed arrays. Declared positive row bounds cover zero-coefficient/no-term cases.

The compiler proves $\lambda A\le B_d\delta^{1/3}$ uniformly at reachable labels and scales (`implementation`, 469–521). Its routine height $H$ is fixed. This is different from expression depth $D_0=3N^2+1$. Uncached duplicated center subtrees are still direct children of the same parent routine, so the row-sum bound applies at each acyclic expression tier. Neither the number of queries nor the number of duplicated nodes becomes the induction height.

Take $C\ge\max(2,C_1)$ covering the direct coefficients and set

$$
L_0=P_0=1,\qquad
L_k=8C^2L_{k-1}(1+L_{k-1}),\qquad
P_k=8C^2P_{k-1}(1+L_{k-1}).
$$

Fix these finitely many constants **before** choosing a dimension threshold with $L_k\lambda A\le1/2$ for all reachable calls. Let $L=L_{k-1}$, $P=P_{k-1}$. At fixed anchors the source's exact-center recursion becomes

$$
E_i\le v+L\lambda A\max_{j<i}E_j,\qquad
v=|\Delta x|+Cr|\Delta a|.
$$

Thus $E_i\le2v$. Final rows cost at most $2A_fL\lambda v$. The M anchor is supplied by a lower-height S call; its additional sensitivity is at most $2C^2L^2\lambda^2r^2$. Since $\lambda r^2\le1$, the stated $L_k$ dominates this and the direct sensitivity. This is exactly the structure of source lines 536–564, now without unused polylog slack.

For arbitrary erroneous replies, insert the exact child at the erroneous center. The same recursion has additive forcing:

$$
E_i\le Cr|\Delta a|+APu+L\lambda A\max_{j<i}E_j.
$$

The final error is at most

$$
A_fPu+2A_fL\lambda(Cr|\Delta a|+APu).
$$

For S, $\Delta a=0$, giving at most $2CrPu$. For M, $|\Delta a|\le Pr u$, giving at most $CP(2+2CL)u$. Both fit $P_k$. Consequently

$$
|\widehat M-M|\le P_Hu,\qquad
|\widehat S_{\rm pre}-S_{\rm pre}|\le P_Hru. \tag{A}
$$

This deterministic argument covers discontinuous errors at nearby points, different replies to duplicate queries, adversarial sign alignment, and extreme seeds. In particular an error row can align with the signs of all coefficients; the proof pays its **absolute sum**, not cancellation. Moved terminal physical queries pay the true gradient's Lipschitz bound. No Gaussian absorption or score differentiation is applied to erroneous replies.

**Contribution assessment of this residual:** no new coefficient cancellation, probabilistic independence, depth reduction, or geometric mechanism is required. The only unbounded scalar factor occurs inside the already-small $\lambda A$. The final sums and direct coefficients are constants, and there are finitely many routine heights. Replacing homogeneous sensitivity by an inhomogeneous error recurrence is ordinary perturbation of the source's very same proof. A lower bound on tolerable $c$ uniform in $\epsilon$, or a growing-height construction, would be different. Neither is claimed.

## 4. Causal entropy, retained state, and existing regularization

### 4.1 Entropy does not compare full oracle transcripts

Internal transformed seeds have covariance $I-vv^\top/(4D_s^2)$. An internal reserve and a query-affecting coordinate can have covariance $-v_iv_j/(4D_s^2)\ne0$. Delaying that coordinate does not make it independent. The original failure is preserved.

The source's **standalone top sampling call** has a separate final $sG/2$ slot unused by every query (`implementation`, 714–726). Draw only that slot after the call's query block. A causal adversary cannot see it. All earlier correlated seeds retain their stipulated joint law.

For common latent variable $W$ and Gaussian output variance $vI$, retaining $W$, using the Gaussian translation identity, and projecting gives

$$
D_{\rm KL}(\mathcal L(a(W)+\sqrt vG)\|
             \mathcal L(b(W)+\sqrt vG))
\le \frac{\mathbb E|a(W)-b(W)|^2}{2v}.
$$

For $h=\delta/2$, the normalized gradient is $g_y(z)=\sqrt h\nabla V(y+\sqrt h z)$ and its error is $u=\sqrt h\eta$. At top scale, (A) gives physical pre-reserve displacement $P_Hh\eta$ and variance $h/4$. Therefore the conditional divergence is at most

$$
2P_H^2h\eta^2 \tag{B}
$$

from the noisy compiler to the **exact compiler**, not to the ideal proximal kernel.

Represent causal strategies by measurable reply kernels on finite real histories. These are standard Borel spaces even if a strategy is informally described as having arbitrary memory. At an incoming enlarged state $s$, disintegrate the actual transition as $K_s(dz,ds')=k_s(dz)L_s(z,ds')$. For a replacement visible law $e_s$, use $E_s=e_sL_s$. Direct integration and projection give

$$
D_{\rm KL}(K_s\|E_s)=D_{\rm KL}(k_s\|e_s),\qquad
\operatorname{TV}(K_s,E_s)=\operatorname{TV}(k_s,e_s). \tag{C}
$$

The KL equality requires $k_s\ll e_s$; TV does not. In this application Gaussian mixtures have positive finite densities. An all-history conditional kernel can be written by weighting the latent law by $\phi_v(z-a_s(w))/k_s(z)$ and reconstructing the carried state. On other null sets take any measurable probability extension; globally admissible reply extensions can use exact replies as an analytical device. This grants the algorithm no additional oracle access.

With exact-compiler visible marginals in $E_s$, its visible transition conditioned on the entire **past** is the exact compiler kernel, despite its synthetic state. It need not be a possible physical exact-oracle transcript. Starting at the identical warm-up joint law, chain rule in the direction actual-to-replacement sums (B) under actual prefixes. For $m$ calls,

$$
D_{\rm KL}(\text{actual path}\|\text{replacement path})
\le2P_H^2mh\eta^2,\qquad
\operatorname{TV}(\text{endpoints})\le P_H\eta\sqrt{mh}. \tag{D}
$$

This resolves adaptivity by an explicit common-kernel identity, not by assuming independent errors or Markov noisy visible dynamics. I152 already used the TV version of this state-retention construction. The KL version is its Radon–Nikodym chain-rule analogue, with zero conditional-state contribution. I find technical bookkeeping, not a new composition theorem, in this step.

### 4.2 The missing one-step factor is paid by an existing operation

The source's ideal noised proximal kernel is $P_h(y)=\kappa_y*N(0,hI)$, with invariant $\widetilde\pi=\pi_V*N(0,hI)$, and $W_2(\kappa_y,\kappa_z)\le q|y-z|$, $q=(1+h)^{-1}$. Thus Gaussian mixture entropy gives

$$
D_{\rm KL}(P_h(y)\|P_h(z))\le q^2|y-z|^2/(2h).
$$

Shifted Composition I's Theorem 3.2 and KL/W2 Remark 3.4 apply with contraction $q$ and regularity constant $q^2/(2h)$. A sufficient, nonoptimized schedule is explicit: put $\mu_j=\mu P_h^j$, $\rho_0=\nu$, optimally couple $X\sim\mu_j,Y\sim\rho_j$, shift $Z=Y+(X-Y)/(m-j)$, and set $\rho_{j+1}=\mathcal L(Z)P_h$. Then

$$
a_j:=W_2(\mu_j,\rho_j)\le q^j(m-j)a_0/m,\qquad \rho_m=\mu_m.
$$

The joint KL chain rule for $\rho_j(dy)\mathbb E[P_h(Z)\mid Y=y]$ versus $\nu P_h^j(dy)P_h(y)$ adds at most $q^2a_j^2/[2h(m-j)^2]$. Summing from zero initial KL gives

$$
D_{\rm KL}(\mu P_h^m\|\nu P_h^m)\le \frac{W_2(\mu,\nu)^2}{2hm},
\quad
\operatorname{TV}(\mu P_h^m,\nu P_h^m)\le\frac{W_2(\mu,\nu)}{2\sqrt{hm}}. \tag{E}
$$

Only finitely many deterministic pairs of laws are coupled. No implementable optimal-transport oracle, global measurable selection, diffusion simulation, or score identity for noisy replies is needed. Finite moments follow from the proximal moment bounds. Positive transition densities and finite integrated costs pay absolute continuity. With $m=\lceil1/h\rceil$, $hm\ge1$ removes the unwanted one-step loss.

Shifted Composition III, both the preprint and June 11, 2026 journal §3.1, offers the stronger different-kernel framework. Its regularity, Wasserstein and **cross-regularity** assumptions must be checked; a small Wasserstein error alone is not a KL error. I do not assert noisy-to-ideal cross-regularity. Instead (D) and (E) are combined with a separate exact-to-ideal TV comparison. The journal's explicit permission to recouple auxiliary variables after specifying their marginals agrees with the construction above. Neither the general-$L$ optimization appendix nor the full weak-error theorem is needed.

## 5. Complete algorithmic reduction, including every error and cap

Fix $0<e<\min(1,\epsilon/2)$, then $K_0>2+1/e$. Choose the source's small $t$, Picard depths and height, then $w$ and interpolation orders in its prescribed order, with $e(1+t)<\epsilon$. Fix the constants of §3 afterwards, before the uniform dimension threshold. Write $B_d$ for a fixed polylogarithm, allowed to increase finitely many times.

**Warm-up.** Start at supplied mode $0$, run $T=\lceil Ch^{-1}\log d\rceil$ noisy compiled transitions. From (A), source intrinsic accuracy and proximal contraction,

$$
a_{j+1}\le(q+2hB_d\delta^{K_0})a_j
+C\sqrt hB_d\delta^{K_0}\sqrt d+P_Hh\eta,
\quad a_j=W_2(\mu_j,\widetilde\pi).
$$

The coefficient is at most $1-c_0h$ for large $d$. Conditional couplings apply with the state retained; $\|Y_j\|_2\le a_j+C\sqrt d$ closes the moment bound. Thus

$$
a_T\le C\sqrt d\,e^{-c_0hT}
+Ch^{-1/2}B_d\delta^{K_0}\sqrt d+C_*\eta=o(1)+C_*\eta.
$$

**Window.** Append $m=\lceil1/h\rceil$ noisy calls. Equation (D) costs $O(\eta)$ since $mh\le1+h$. The source exact-compiler/ideal interface is

$$
\operatorname{TV}(\widehat P_h(y),P_h(y))
\le B_d\delta^{K_0}(\sqrt d+2\sqrt h|y|).
$$

Use hybrids with ideal prefix and exact-compiler suffix. Ideal-prefix contraction from the warm-up law bounds RMS centers by $C\sqrt d+C_*\eta+o(1)$. The intrinsic window cost is at most $B_d\delta^{K_0-1}(C\sqrt d+C_*\eta)=o(1)$. Apply (E) between the warm-up law and invariant $\widetilde\pi$. The window endpoint is within $C_*\eta+o(1)$ in TV of $\widetilde\pi$. No triangle inequality for KL is asserted.

**Descent and unnoising.** Replace the incoming visible marginal by $\widetilde\pi$ using (C), retaining its conditional state. Use the source fixed $J=\lceil C_1\log d\rceil$ conditional descent at $r_j=2^{-j/2}$, with fresh standalone calls. The extra noisy cost is at most $C r_j\sqrt h\eta$ at level $j$, hence $O(\sqrt h\eta)$ in total. The exact-to-ideal cost is evaluated under ideal prefixes, where the source gives $\mathbb E|g_y(x_j)|^2\le Cd$. Its sum is $CJ B_d\delta^{K_0}\sqrt d=o(1)$. State retention ensures these visible ideal laws hold conditional on the whole preceding state.

At the terminal mode iteration, the difference from the true contraction obeys $b_{k+1}\le\delta r_J^2b_k+r_J\sqrt h\eta$. The extra center displacement is at most $r_J\sqrt h\eta/(1-\delta r_J^2)$, paid by the final independent standard Gaussian. The source's exact base remainders are

$$
C\delta2^{-J}\sqrt d+
\frac{C(\delta2^{-J})^{m_0}2^{-J/2}\sqrt d}{1-\delta2^{-J}},
\qquad m_0=\lceil C_2\log d\rceil.
$$

Both vanish. Its conditional identity $x_j+r_jZ_j=x_{j+1}+r_{j+1}Z_{j+1}$ shows that ideal descent returns $\kappa_y$; averaging over $y\sim\widetilde\pi$ returns **$\pi_V$**, not the smoothed target. Data processing through the final affine output pays the comparisons.

Collecting terms gives $\operatorname{TV}(\mathcal L(X),\pi_V)\le C_e\eta+R(d)$ uniformly over the full allowed class and $\eta\le1$, where $R(d)\to0$ consists of the two warm-up terms, $B_d\delta^{K_0-1}(\sqrt d+1)$, $CJ B_d\delta^{K_0}\sqrt d$, and the two displayed terminal terms. In particular $e(K_0-1)>1/2$. Uniformity is essential: choose provisional $c\le1$ with $C_ec\le1/40$, then a single $d_0$ making all source entrances hold and $R(d)\le1/40$. Reducing $c$ later does not alter $d_0$.

**Finite-dimensional fallback.** For $2\le d<d_0$, take $L_d=\lceil4\,2^{d/2}\rceil$ independent standard Gaussian proposals and acceptance

$$
\widehat a(x)=\exp(-\widehat V(x)+|x|^2/2-c).
$$

Then $e^{-2c}a(x)\le\widehat a(x)\le a(x)\le1$ for the exact acceptance $a$. Expose the acceptance uniform only after the value reply. Coupling to the exact capped sampler until first disagreement gives

$$
\operatorname{TV}(\text{noisy capped output},\pi_V)\le e^{-4}+2L_dc.
$$

Here $e^{-4}$ is the **exact comparison's** failure bound, not a claim about the noisy accepted law. Decrease $c$ to at most $1/(80\max_{2\le d<d_0}L_d)$ when this set is nonempty. This is positive and gives TV below $1/10$. The main algorithm uses gradients; values are needed only for this fallback.

**Every execution.** Each top primitive has at most $B_d\delta^{-t}$ queries. Warm-up plus window has $O(\delta^{-1}\log d)$ calls; descent and mode iteration have prescribed logarithmic lengths. Their total is at most $B_d\delta^{-(1+t)}\le C_\epsilon d^\epsilon$. Increase $C_\epsilon$ for the finitely many rejection caps. Circuits and loop counts are fixed before replies; extreme seeds and bounded but inconsistent histories do not introduce exceptions. No expected-only bound, success-conditioned stopping, or bit-model assertion enters this reduction.

## 6. Primary comparisons and strongest contrary argument

| Primary source, checked version | What is actually compared |
|---|---|
| Dalalyan–Karagulyan, `1710.00095v4`, February 23, 2024 | Condition N and Theorem 4 permit biased, temporally dependent errors with fresh independent Gaussian updates. Their coupling gives a bias floor, not the source's subpolynomial discretization. With dimension $d$, take their bias/noise parameters at most $\eta/\sqrt d$; the Euler term still contains $\sqrt{hd}$. |
| Chen–Chewi–Lu–Zhang, Picard `2609.06906v2`, September 29, 2026 | Exact unsmoothed gradient interface; Appendix D handles approximate proximal centers, not arbitrary erroneous gradients. Appendix E's exact-smoothed-gradient proof already uses small absolute row sums and depth stability. Main guarantees retain positive dimension exponents. |
| Chen–Chewi–Daskalakis–Rakhlin, PMLR 336:1341–1372 (2026) | Assumptions 2.1–2.2 require iid unbiased oracle samples. The FORS construction and Theorem 3.3 proof use conditional mean zero and a fixed estimator law. Arbitrary bounded causal bias does not satisfy these hypotheses. |
| Gaussian cloud correction, `2609.38710v1`, September 30, 2026 | Theorem 1.1 uses exact gradients, a supplied reference point, and expected $\widetilde O(\kappa d^{1/5})$ work. The supplied mode meets its reference-point condition after scaling; that condition is **not** a mismatch. Its oracle interface and positive exponent do not give the present full theorem. |
| Altschuler–Chewi, Shifted Composition I `2311.14520v1`; III `2412.17997v1` and journal DOI `10.1007/s10208-026-09753-x` | The actual multistep regularization mechanism is already paid. III's additional different-kernel comparison requires cross-regularity and cannot silently replace the separate intrinsic-TV budget. |

Expected work is **not by itself an obstruction** at fixed TV error: a uniform expected bound $Q$ can be capped at $Q/\alpha$, losing at most $\alpha$ in TV by Markov's inequality. Picard's introduction says so explicitly. This leaves its dimension exponent and oracle assumptions unchanged. Likewise, continuum drift entropy alone gives no finite-query implementation; here the stipulated compiler supplies that implementation.

Newly read operative proof ranges, not entire papers, are claimed. In inaccurate-gradient LMC these include the fundamental coupling, Theorem 4, and required lemma endings. In Picard they include Appendices D/E, the second-order Gaussian estimate and its proof ending, and the main Theorem 1.1 assembly; the entire companion dependency chain was not reread or imported. In the PMLR paper the oracle definitions, FORS construction, and Theorem 3.3 proof through its ending were read; all later technical/proximal proofs were **not** newly read. For Gaussian cloud, the complete Theorem 1.1 statement and introduction were read, **not** its likelihood-correction proof. These narrower nonapplicability comparisons do not require those unread proofs.

A further lead, Paulin–Whalley `2604.24632v2`, was found in primary search results, but its complete primary theorem/proof was not obtained here. Picard's actual Remark 4.12 compares its Theorems 2.1/2.7 as Gaussian convolution estimates for centered perturbations independent of the smoothing Gaussian. I do not infer the absence of a stronger result from a failed keyword search, nor use that unexamined paper as a premise. The positive full reduction above does not depend on ruling out all closer literature.

The strongest objection to TECHNICAL ONLY is valid as far as it goes: no listed external sampler states the complete causal inconsistent-oracle theorem, and obtaining constant rather than inverse-power tolerance is a genuine strengthening. However, the question is whether a nonroutine operation remains after **all stipulated lower operations** are credited. Sections 3–5 show none: the only constant sharpening follows the source's explicit induction; the state construction is common-kernel cancellation; and the regularization is a direct existing specialization. The integration needs careful hypotheses, orientation and error accounting, but no additional analytic estimate beyond those displayed. The meaningful strengthened conclusion is therefore retained as validated technical research, not counted as a ninth substantial mechanism.

## 7. Corpus/project search and evidence limits

One fresh flat preparation traversal checked the complete pinned map: **13,223 tree entries, 749 manuscripts, 10,373 original blob positions**, including 9,340 corpus-text bindings, 776 PDF/text bindings and 257 other-byte bindings. It verified SHA-256 bytes and Git blob IDs and recorded every matching line and codepoint span for three search expressions: robust/noisy/inexact/adversarial sampling (68 lines), entropy/shifted composition (833), and compiler operations (630). These are overlapping lexical categories, not counts of independent results and not semantic reading of the corpus.

Actual companion inspection included the full information/density and hybrid sections of *Replacing Gaussian observations in memory-constrained inference*, including their proof endings. They concern finite-message spherical-signal experiments and conditioned actual/fresh rows, not this sampler. Selected actual model/statement passages in *Localization costs and information growth for exact Gaussian observations*, *Conditional information under deterministic coordinate sweeps*, and the dimension-free log-Sobolev manuscript distinguish bit-state exact observations, permutation sweeps, and an LSI/transport inequality from a noisy query algorithm. No unread companion proof is invoked to certify an absence result. The full sampling upper-bound closure is the relevant positive source, not the number of search misses.

A separate bounded historical-report search covers 210 numbered reports below I160, excluding the active I158 artifacts. Its 23 matching lines are in I152/R154/I157/I159, all read directly here. Earlier contribution dispositions were checked in the ledger, notably the operation-based I30/I36 decisions. Lexical search does not certify absence from all previous work or literature.

The owned evidence distinguishes actual fresh reads, inherited preparation, and live metadata checks. Read-log lines use UTF-8 **LF** separation; corpus search uses Python `splitlines`, which treats PDF form feeds differently. They must not be interchanged. The original I160/I159 briefs, including embedded original reports and finalized parent responses, were read fully in bounded displays; all other JSON fields were read separately. Hashing an older recursive record does not constitute a fresh semantic read of it. No unrelated recursive audit is claimed complete.

Unproductive broad web searches, missing-path attempts, truncated ledger displays and their recoveries are retained in `attempts.json`. The live journal page was truncated/subscription-marked; the separately bound existing journal PDF/text supplies the newly read §3.1 proof. Live metadata is recorded as selected factual observations, not purported exact HTTP response bytes. Existing PDF/text artifacts are reused without conversion. Historical four-ledger snapshots are bound read-only; mutable live ledgers are not immutable dependencies.

Owned evidence is under `frontier/sources/i161_oracle_tolerance_contribution_astra/`; the verifier is under `frontier/experiments/i161_oracle_tolerance_contribution_astra/`. One canonical inventory is prevalidated before one exclusive-create seal. Replay checks immutable bytes, the original-position domain/Git blobs, lexical occurrences, read passages and decoded briefs **before** new finite diagnostics. Its audit hook denies writes, network and process creation; bytecode is disabled. No ancestor verifier, diagnostic or preparation program is executed. No shared index, I162 artifact, staging area, commit or external publication is changed.

Run from the project root:

```sh
python3 -B frontier/experiments/i161_oracle_tolerance_contribution_astra/verify.py
```

Evidence/finite-diagnostic PASS means reproducibility only, not a universal proof or contribution certificate. The contribution recommendation rests on the explicit reduction above. No in-scope mathematical interface remains unpaid for this recommendation. Worldwide priority, a common tolerance for all $\epsilon$, and the unrelated historical audits remain unestablished or incomplete as stated. **TECHNICAL ONLY; original proof PASS preserved; eight accepted, two remain.**
