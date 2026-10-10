# I157 — ORIGINAL R154 correctness review, round 2

**Original-proof gate: UNRESOLVED. Required review coverage is incomplete. This is not a correctness PASS, a mathematical counterexample, or an acceptance decision.**

I independently checked the original R154 equations (1)–(19) against the complete numerical interface, compiler, preliminaries, centering, and final sampling/descent sections. The checks below did not identify a substantive mathematical repair to those equations. However, I did **not** complete the required semantic reading of the entire recursively inherited task/report/response/objection chain or every required companion/comparator proof. In particular, immutable verification of the 7,800-line inherited decoded stream is not a new reading of it. Therefore this round cannot deliver the requested complete independent gate. The unmet obligations are listed below and in `review-status.json`; no inherited author PASS is promoted to a new reviewer PASS merely by reproducing its evidence.

The original report is `frontier/iterations/i154-dimension-independent-oracle-tolerance.md`, SHA-256 `1878b68a5482aba8807f4d910465f83b43d86d401af1a53d038cfebc40b08be1`. The mandatory original task matches `0fa43c233f6032d38f3b905cac2253321303e3a300342112ae8716e504897d97`; the I152 task matches `f13a8eb19fe9ee8cdd1a6fbeb6618529a48c0599f08a84272be5b68570bf7379`. Original bytes and verdict history were preserved. All OpenAI theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` were treated as premises. No truth audit, contradiction inference, ex-falso, child agent, shared edit, staging, commit, or publication was used. I155/I156 are not dependencies. W152/H152/C145 remain parked. Eight accepted, two remain.

## 1. Scope and original I152 verdict history

The target examined is exactly

\[
\forall\epsilon>0\ \exists c_\epsilon,C_\epsilon>0\ \exists\mathcal A_\epsilon\
\forall d\ge2\ \forall V\ \forall\text{admissible causal strategies}:
\quad Q\le C_\epsilon d^\epsilon\text{ on every run},\quad
\operatorname{TV}(\mathcal L(X),\pi_V)\le1/10.
\]

Here (V\in C^2\), its supplied minimizer is 0, (V(0)=0\), and (I\preceq\nabla^2V\preceq2I\). Errors are uniform absolute value errors and Euclidean gradient errors, each at most (c_\epsilon\). The algorithm is a real-query algorithm with unrestricted intervening computation. Nothing here proves one positive tolerance for all epsilon, finite-bit complexity, or arbitrary-accuracy amplification. These distinctions are unchanged.

The I154 audit's historical verdicts remain exactly scoped:

* Restricted A148 and the conditional probability-limit entropy assertion were reported PASS; no unconditional C145 conclusion or invariant prelimit lift was claimed. This round has not completed their recursive re-audit.
* The conventional numerator/denominator weighted-normalizer lower bound excludes that output encoding. It does not exclude a compact exponent/log answer or a sampler. The unchanged-bin obstruction is a method obstruction. Full source-dependent re-audit remains incomplete here.
* The rank-bit result is for known, predetermined independent channels after deletion, with fixed uncorrupted channel metadata and bounded whole-record replacements, at the positive-deletion efficient-decoder interface. It is not a noisy-bit use of the special (p=1\) one-trace branch. Full decoder/lower-bound reading remains incomplete here.
* The Huber statement concerns iid mixture contamination of actual trace laws, not an identical sharp deterministic replacement-budget threshold. The max-density construction itself is valid: its required mass is ((1-\alpha)(1+\operatorname{TV}(P,Q))\le1\).
* The literal claim that **every internal reserve is independent after the queries remains FAIL**. This is independently supported by the actual compiler, as explained below.
* Standalone R2, its R3/R4 uses, and the final descent use fresh top-level calls. Their displayed numerical bounds do not require repairing the internal reserve law. Restricting the blanket sentence is nevertheless a genuine restriction of that sentence; its historical failure is not erased.
* The consistent-potential calculation is a scoped interpolation argument. A bounded rotational perturbation has nonzero antisymmetric derivative at 0 and excludes that potential representation; it is not a sampling impossibility.
* Original dimension-independent R152 was unresolved. Original I133 I.5, I124 arbitrary-Q cutoff, I112 standalone G112 with a closed component, and I112 equal-zero-lambda scale fixing retain their literal failures and separate corrections.

The elementary weighted sum is ((4^{N+1}-1)/3\); a positive rational (a/b\) within relative error (1/4\), with (b\ge1\), has (a\ge3Z/4\). For independent rank flips the debiased bit is ((Y-e)/(1-2e)\); absent ranks must be zeroed before products. A statistic has range ([-A,A]\), (A=a^{-D}\), so the stated Hoeffding exponent is (M\zeta^2/(512A^2)\), and record replacement plus rounding gives (\zeta/16+\zeta/32+\zeta/64=7\zeta/64<\zeta/8\). These direct checks do not substitute for the outstanding decoder and source-interface audit.

## 2. Actual compiler and equations (1)–(4)

Source locations below are within the pinned sampling manuscript's `build/sections/` directory. Complete new readings are recorded for `implementation.tex` 1–729, `numerics.tex` 1–779, `preliminaries.tex` 1–275, `centering.tex` 1–414, and `sampling.tex` 1–435, through their respective endings. This is an interface/application review, not a truth audit of the stipulated analytic operations.

The numerical interface, `numerics.tex` 598–644 and its proof 667–771, supplies

\[
b_i=x+r(\ell_i y+m_iG),\quad |\ell_i|,|m_i|\le1,\quad
r_i=r\tau_i,\quad R/\sqrt5\le\tau_i\le1,
\]
\[
A_M=C_1(1+\log d)^{C_1}[(r/\sigma)\delta^{-4t-10w}+r^2],\quad
A_S=C_1r^2,\quad A_{f,M}=C_1,\quad A_{f,S}=C_1r.
\]

The final mean direct term is (\sigma G/2\), with no position-anchor dependence. The sampling direct term is (y/\rho_e\), with (\rho_e\ge2/\sqrt5\), and its Gaussian anchor is center independent. Final mean terms have scale exactly (rR\). The scalar construction never uses centers, replies, or seed values to select coefficients or labels.

The terminal formulas are exactly those in R154. For fixed seeds, they give mean sensitivity (\lambda\), sampling sensitivity (r\lambda\), and oracle perturbations (u,ru\). In `implementation.tex` 252–286, residual noises, requested child noises, and matrices (P_i\) are fixed by scalar parameters. They cancel in same-seed comparisons, even for correlated seed arrays.

Routine labels are ((b+t,p)\) for mean-final children, ((b,p)\) for sampling-final children, and ((b-10t,p-1/4)\) otherwise, including the mean's sampling anchor. The bounded routine-height proof uses the finite number of decreasing transitions; neutral transitions require returning through a decreasing transition. This is distinct from the expression depth (D_0=3N^2+1\). Expanding an uncached expression duplicates entire center-supplying subtrees, but each occurrence still invokes a child of the same routine. Fixed routine height, not query count, indexes the simultaneous induction.

For nonfinal terms, (\sigma_i=r\tau_{\rm prev}/(4D_sA)\). The source's size descent gives (b>1/2\), (c_1w<t\), and (\lambda A\le B_d\delta^{b-4t-c_1w}\le B_d\delta^{1/3}\) in mean parents; sampling parents have (\lambda A=C_1\lambda r^2\). These estimates hold at every reachable scale and label. In particular there is no lower-bound requirement on the input center or the top descent radius.

Here is an independent domination check of the original induction. Set (L=L_{k-1}\), (P=P_{k-1}\), and (\alpha=L\lambda A\le1/2\). At fixed anchors and a fixed routine level, each supplied-center discrepancy obeys

\[
E_i\le v+\alpha\max_{j<i}E_j,\qquad
v=|\Delta x|+Cr|\Delta a|.
\]

Induction on the acyclic ordering gives (E_i\le2v\). This is a deterministic maximum of finitely many discrepancies, not an expectation of the maximum of Gaussian seeds. Multiplying each row by its absolute coefficient sum already accounts for every duplicated occurrence. No additional node count or maximum-of-random-variables estimate is involved.

Consequently the fixed-anchor mean output has center sensitivity at most (2CL\lambda\) and position-anchor sensitivity at most (2C^2L\lambda r\). Its anchor is (b_*S(x,r,R/b_*)\), whose center sensitivity is at most (Lr\lambda\). The extra contribution is at most (2C^2L^2\lambda^2r^2\), exactly with (r^2\). Since (\lambda r^2\le1\), the total is bounded by (L_k\lambda\) with the original (L_k=8C^2L(1+L)\). Sampling gives (2CLr\lambda\le L_kr\lambda\).

For erroneous runs, split a child into its erroneous and exact evaluations at the **erroneous** center, followed by exact evaluations at the two centers. This uses no continuity of the error. The center recurrence is

\[
E_i\le Cr|\Delta a|+APu+\alpha\max_{j<i}E_j.
\]

Thus the final error is the original (3). Sampling has (\Delta a=0\), so the error is at most (2CrPu\). In a mean routine, ( |\Delta a|\le Pr u\), so its error is at most

\[
CP[2+2CL\lambda r^2]u\le CP(2+2CL)u
\le8C^2P(1+L)u.
\]

This proves the stated domination by (P_k\). The gradient at a moved physical query contributes (\lambda\) times that query's movement in the exact comparison, already included in this induction. Different bounded errors at repeated points or different duplicated occurrences cause no exception. Seed magnitudes do not enter any constant. After the scalar parameters and (H\) are fixed, one uniform dimension threshold makes all finitely many height constants satisfy the absorption condition. No Gaussian absorption identity is applied to erroneous replies.

## 3. Reserves, causal state, and equations (5)–(8)

The failure of internal independence is concrete. `implementation.tex` 300–314 shifts a mean routine's anchor-sampler reserved coordinate by (-2R/b_*\); a query-affecting coordinate also has nonzero shift coefficient. When a parent supplies (PG\) with covariance (I-vv^T/(4D_s^2)\), these two slots have covariance (-v_iv_j/(4D_s^2)\), generally nonzero. Postponing the draw must use the conditional Gaussian law if one is to preserve that correlated law; it does not produce a new independent reserve.

The top standalone sampling call has a different interface: its final (sG/2\) is untouched by a parent transformation and unused in every query. Draw it only after the finite query block. All other seed slots retain their original joint law, including correlated internal blocks. This preserves the standalone law against a causal strategy depending on its permitted observations; no earlier query or reply uses the postponed reserve. Exact and erroneous pre-reserve outputs can therefore share the entire earlier seed array and a randomization of the adversary kernels. The exact comparison ignores the latter randomization.

For common latent law (\zeta(dw)\), retain (w\) in the two laws with Gaussian conditional centers (a(w),b(w)\). Their KL is

\[
\int \frac{|a(w)-b(w)|^2}{2v}\,\zeta(dw),
\]

and projection gives (5). This does not equate erroneous and exact query transcripts. The two physical factors (\sqrt h\), one in the gradient error and one in the output scaling, give displacement (C_*h\eta\), while the independent variance is (h/4\). Hence (6) is (2C_*^2h\eta^2\), to the exact **compiler** marginal only.

For (7), a finite union of finite real history spaces is standard Borel. Private randomization can be represented by independent uniform seeds for its measurable reply kernels; alternatively a standard-Borel private state can be carried. This does not require assuming a nonstandard hidden state space admits a disintegration. One uses its causal reply kernels on the real history space, the model explicitly stated in R154. At impossible histories an admissible extension is, for example, the exact reply. Such an extension is an analysis construction, not a computational query available for free to the algorithm.

Parameterized disintegration gives a jointly measurable (L_s(z,ds')\) for the actual joint transition. On a (k_s\)-null set choose a measurable probability extension. For (K_s=k_sL_s\) and (E_s=e_sL_s\), the derivative is (dk_s/de_s\) at (z\) whenever (k_s\ll e_s\). Integration gives the KL equality. For TV, integration against the same conditional kernel gives the upper bound, and projection onto (z\) gives the reverse bound, even without absolute continuity. The next-state kernel need not be the one generated by physically running the exact compiler.

In the Gaussian case there is also an explicit version: represent all randomness before the reserve by (w\) with law (\zeta_s\), and actual pre-reserve center (a_s(w)\). Then

\[
k_s(z)=\int\varphi_v(z-a_s(w))\,\zeta_s(dw)>0.
\]

Weight (\zeta_s(dw)\) by (\varphi_v(z-a_s(w))/k_s(z)\) and reconstruct the reserve from (z-a_s(w)\) to obtain the conditional next-state kernel. This supplies a measurable version for every (s,z\). Exact compiler Gaussian mixtures are also everywhere positive. No all-history exceptional set with positive replacement mass is being ignored in this application.

Use identical initial joint law after warm-up. At each incoming state choose the replacement output marginal to be the exact compiler at the visible center, retaining the same (L_s\). Integration over (s'\) equals that specified marginal; conditional on the entire preceding history the visible transition is therefore the exact compiler transition. This statement does not condition on future states or future success. Chain rule in the direction **actual to replacement** sums the conditional costs under the actual prefix, where (6) is uniform, giving (2C_*^2mh\eta^2\). Endpoint projection and Pinsker give (8). This is a comparison to a synthetic state-retaining process, not to an exact-oracle transcript process.

## 4. Finite-time regularization: equations (9)–(12)

The source invariant law is the noised target (\widetilde\pi=\pi_V*N(0,hI)\). Under (\pi_V(dx)N(x,hI)(dy)\), the conditional (x\)-law is (\kappa_y\); redrawing (x\), then (y\), proves invariance. Its conditional (W_2\) contraction has factor (q=(1+h)^{-1}\). An optimal coupling of (\kappa_y,\kappa_z\), followed by common Gaussian smoothing, gives (9) by the common-latent KL calculation.

For each (j\), the optimal coupling of (\mu_j\) and (\rho_j\) exists in Euclidean (\mathcal P_2\). Its disintegration need only be selected for these finitely many deterministic pairs of laws, not as a globally measurable family of all optimal transports. Let (Z=(1-\theta_j)Y+\theta_jX\), (\theta_j=1/(m-j)\). Finite second moments propagate by the proximal moment bounds and this convex interpolation. Coupling (X,Z\) gives

\[
a_{j+1}\le q(1-\theta_j)a_j,
\quad a_j\le q^j(m-j)a_0/m.
\]

The endpoint is exact: (\theta_{m-1}=1\) implies (Z=X\), hence (\rho_m=\mu_m\). Initially (\rho_0=\nu_0=\nu\), so the initial KL is zero, regardless of whether (\mu\) and (\nu\) themselves are singular.

With (K_j(y)=\mathbb E[P_h(Z)\mid Y=y]\), apply chain rule to (\rho_j(dy)K_j(y,dz)\) against (\nu_j(dy)P_h(y,dz)\). Conditional mixture convexity uses the orientation (P_h(Z)\Vert P_h(y)\) and costs at most (q^2\theta_j^2a_j^2/(2h)\) after integration. A finite total bound inductively gives (\rho_j\ll\nu_j\). Positive Gaussian-mixture densities also imply conditional absolute continuity at each step. Null-set extensions of (K_j\) do not change its integral under (\rho_j\).

Summing produces

\[
\mathrm{KL}(\mu P_h^m\Vert\nu P_h^m)
\le \frac{q^2a_0^2}{2hm^2}\sum_{j=0}^{m-1}q^{2j}
\le\frac{a_0^2}{2hm}.
\]

Pinsker has factor (1/2\) under the square root, giving (a_0/(2\sqrt{hm})\). These are the original equations, with no replacement by a different ideal kernel. This is the KL/W2 specialization of existing shifted composition, not new regularization. Theorem 3.2, Remark 3.4, its proof, and the convexity extension in [Shifted Composition I](https://arxiv.org/abs/2311.14520) were newly read through their endings. The standalone derivation above supplies the needed hypotheses and orientation without importing an unread stronger theorem.

## 5. Warm-up, entropy window, descent, and uniformity

For warm-up, condition first on the actual enlarged state, couple noisy and exact compilers pathwise, and use the exact source local (W_2\) bound. If (a_j=W_2(\mu_j,\widetilde\pi)\), Minkowski gives (\|Y_j\|_2\le a_j+C\sqrt d\). Thus the intrinsic center term contributes (2hB_d\delta^{K_0}a_j\) and the oracle contributes (C_*h\eta\), exactly (13). Bounded errors plus the fixed finite affine/Lipschitz exact computation propagate finite moments, even for discontinuous stateful replies. For large (d\), the contraction factor is at most (1-c_0h\), yielding (14).

The exponent checks are stronger than necessary: (K_0>2+1/e\) gives (e(K_0-1)>e+1>1/2\). Therefore (B_d\delta^{K_0-1}\sqrt d\to0\); the intrinsic warm-up term divided by (\sqrt h\) tends to zero. Choosing the fixed warm-up time constant large enough also makes (\sqrt d\,e^{-c_0hT}=o(\sqrt h)\).

For the window, (8) has (mh\le1+h\). The exact/ideal TV comparison is separate. The telescoping order is (\mu P_h^j\widehat P_h^{m-j}\): at the replaced step the prefix is ideal. Contraction from the actual warm-up law gives (\|Y\|_2\le C\sqrt d+C_*'\eta+o(1)\) along every such prefix. Consequently (15) sums to (16), (B_d\delta^{K_0-1}(C\sqrt d+C_*'\eta)=o(1)\), uniformly for (0\le\eta\le1\). The regularization bound is applied to (\mu\) and the invariant (\widetilde\pi\), with this same orientation; it yields (17). There is no noisy-to-ideal KL substitution.

In descent, disintegrate the actual incoming joint law given (y\) and replace only its marginal by (\widetilde\pi\), retaining that conditional state law. At each subsequent comparison, integrate (7) at the current incoming state and use an ideal visible prefix. For the level-(j\) error, the noisy/exact term is uniform in state and bounded by (C_*r_j\sqrt h\eta\); the exact/ideal intrinsic term has the source (D(x_j)\) dependence. This permits one hybrid with local cost equal to their sum, avoiding any need for actual-history moments after an incoming TV replacement.

Under the ideal visible prefix, the source recurrence is

\[
b_{j+1}\le(1+C\delta r_j^2)b_j+C\delta r_j\sqrt d,
\quad b_j=\|g_y(x_j)\|_2.
\]

Both geometric sums are bounded. Thus (b_j\le C\sqrt d\), intrinsic error sums to (CJ B_d\delta^{K_0}\sqrt d=o(1)\), and the oracle cost is (C\sqrt h\eta\sum_jr_j\), with no (J\) multiplier.

For the terminal iteration let (l=\delta r_J^2\). Comparing noisy and exact iterates at the same starting point gives (d_{k+1}\le ld_k+r_J\sqrt h\eta\), (d_0=0\). Hence the finite-iteration difference is at most ((1-l^{m_0})r_J\sqrt h\eta/(1-l)\), bounded by (18). The source mode residual and mode-centered Gaussian error are then charged under the ideal prefix. A fresh standard Gaussian converts center displacement to TV. The final affine return and the backwards conditional identity give **unnoised** (\pi_V\), not its convolution.

One can collect all non-oracle terms into a deterministic envelope (R(d)\to0\) valid simultaneously for (\eta\le1\): warm-up intrinsic and transient terms, (B_d\delta^{K_0-1}(\sqrt d+1)\), (JB_d\delta^{K_0}\sqrt d\), and the two source terminal remainders. The remaining coefficients of (\eta\) are bounded constants since (mh\le1+h\), (\sum r_j<\infty\), and (1-l\) is bounded away from zero. This verifies the required order in (19): first fix scalar parameters and (C_e\), then a provisional (c\le1\) with (C_ec\le1/40\), then a threshold with (R(d)\le1/40\). Later decreasing (c\) cannot invalidate that threshold.

For each smaller dimension, downward slack gives (e^{-2c}a(X)\le\widehat a(X)\le a(X)\le1\). Couple proposals and accept/reject uniforms to the exact capped sampler until the first discrepancy. Conditional on any common prefix, discrepancy probability is at most (1-e^{-2c}\le2c\). Thus

\[
\operatorname{TV}(\widehat\pi_{\rm cap},\pi_V)
\le (1-p_d)^{L_d}+2L_dc
\le e^{-4}+2L_dc,
\quad p_d\ge2^{-d/2}.
\]

The (e^{-4}\) term belongs to the exact capped comparison. No assertion that state-dependent noisy acceptance leaves the conditional accepted law equal to (\pi_V\) is needed. Taking (c\le1/(80\max_{d<d_0}L_d)\) pays the stated fallback budget without a circular threshold choice.

The source fixes (K_0,t\), then Picard counts/depth and routine height, then (w\), then interpolation orders. The shift construction and all loops are determined before responses. The additional (\lceil1/h\rceil\) calls fit (B_d\delta^{-(1+t)}\), whose exponent (e(1+t)<\epsilon\). Gaussian extreme seeds cannot change the count or cause an adaptive numerical stopping exception. These conclusions concern query counts only.

## 6. Corrections and contribution boundary

No substantive correction of the inspected R154 equations is proposed. A separate `clarifications.md` records the exact capped-rejection interpretation and the synthetic nature of the state replacement. It is not substituted into the original and does not turn this incomplete review into PASS. The older internal-independence failure remains a failure.

Concrete overlap for the later contribution gate is substantial: the source already supplies fixed-seed compiler stability, scalar row sums, small (\lambda A\), finite routine height, exact-score-only Gaussian absorption, top-call Gaussian reserve, ideal-prefix descent, and fixed caps. The new constant induction tightens the source's allowed polylogarithmic stability bound. Gaussian-mixture entropy and chain rule are standard, and the multistep regularization is existing shifted composition. Whether their integration establishes a substantial contribution is not decided here.

[Inaccurate-gradient LMC](https://arxiv.org/abs/1710.00095v4), Condition N/Theorem 4, allows biased and temporally dependent errors with fresh independent update noise. Its proof and the required recursion/lemma endings were inspected. A Euclidean bound (\eta\) gives conditional bias RMS at most (\eta\) and residual variance at most (\eta^2\); the theorem's Euler term still scales as (\sqrt{hd}\). It does not provide the required subpolynomial every-run cost. [Picard v2](https://arxiv.org/abs/2609.06906v2), Appendix D, explicitly gives approximate proximal-center stability while its gradient evaluations remain exact; its stopping certificate has center-dependent work and its aggregate bound is expected work. Appendix E uses the exact smoothed gradient and already exploits absolute row sums at arbitrary fixed Picard depth. These appendices were read through their endings here, but their full chains of companion lemmas were not independently reread; no stronger literature theorem is imported as a premise for R154.

## 7. Evidence, outstanding work, and replay

The evidence has one completed flat preparation traversal over all 13,223 entries, 749 manuscripts, 10,373 original blob positions, and 776 PDF/text bindings, including Git blob IDs and exact inherited lexical multisets/positions. It contains no corpus copies or inherited PDF re-extractions, and no ancestor verifier, diagnostic, or converter execution. All inherited immutable references are flattened; current four ledgers have separate immutable snapshots. No active I155/I156 artifact is bound.

The mandatory I154 task's ordinary decoded field stream was displayed in full, with its one truncated passage recovered. Nested decoded occurrences, including embedded JSON, are retained with structured paths and offsets. The original I154 report and original-audit report were newly read completely; the full finalized parent response was supplied in the brief and its local bytes are bound. **These facts do not amount to completing the recursively required I152/I148/older semantic readings.**

Outstanding obligations preventing a complete gate are:

1. Read the inherited 7,800-line unique decoded stream and the required recursive original records through their endings, crediting exact occurrences rather than inherited reading claims; finish the independent original-I152/I148 and older source-interface audits.
2. Finish the full weighted-bin/efficient-decoder/actual hard-pair and torus source/primary entrance reviews required by that recursive scope. The limited direct calculations in section 1 are not replacements.
3. Finish required comparator and companion dependencies beyond the explicitly recorded ranges, including the complete relevant stochastic-oracle comparison and the remaining Shifted Composition III/journal comparison. The failed live journal retrieval is recorded; an inherited journal text is available but was not newly semantically read here.

`read-log.json` is an actual new-display log, not an inherited full-read claim. `review-status.json` explicitly says task INCOMPLETE and original-proof verdict unresolved. The verifier checks immutable bytes and exact context/lexical bindings before any new finite diagnostics. Its audit hook denies writes, network, subprocesses and bytecode mutation; it cannot repair or reseal. The canonical owned inventory is prevalidated before one exclusive-create seal. Evidence PASS and finite diagnostic PASS do not establish universal correctness, completed reading, contribution, or acceptance.

Replay from the project root:

```sh
python3 -B frontier/experiments/i157_dimension_independent_oracle_tolerance_r2/verify.py
```

This record leaves the original R154 proof unrepaired and the requested full independent correctness gate unresolved.
