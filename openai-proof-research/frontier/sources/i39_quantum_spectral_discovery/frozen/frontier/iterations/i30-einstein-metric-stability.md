# I30: a candidate power estimate for the original almost-Einstein metric

**Disposition: complete source-relative proof candidate, submitted for independent proof and significance review.** Under the stipulated pinned corpus, the argument below gives universal constants `ε,C>0` such that

\[
 \min_{h\in\mathscr H}d_{GH}((M,d_g),(M_h,d_h))\le C\mathcal D(g)^{1/16},
 \qquad \mathscr H=\{S^4_1,(\mathbb {CP}^2,h_{FS}),S^2_{1/\sqrt3}\times S^2_{1/\sqrt3}\}.
 \tag{1}
\]

Here `M` is smooth, closed, connected, simply connected, four-dimensional; `sec_g≥0`, `Vol_g(M)^{-1}∫R_g=12`, and `D(g)=∫|Ric_g−R_g g/4|²<ε`. Every model has `Ric_h=3h`; `h_FS` is twice the metric induced by the unit Hopf sphere. The conclusion concerns the **original distance**. Neither optimality of the exponent nor dynamical attraction under volume-normalized Ricci flow is asserted.

The proposed bridge is a two-metric estimate using a one-sided distance bound and **square-root volume control on every material subset**. Its proof is given below, not assumed. It applies without an initial injectivity-radius bound or pointwise Einstein-error bound. The volume-packing mechanism has a direct antecedent in Tian–Wang, Lemma 4.4 and Theorem 4.1; the present L² material-set estimate changes the error budget. A significance reviewer could judge this combination technical. This report makes no substantial-count, priority, or acceptance claim.

## 1. Frozen scope and dependencies

The controlling task and prior objections are frozen in [task-brief.txt](../sources/i30_einstein_metric_stability/task-brief.txt). The entire original I27 brief and report, current ledger (five accepted including R011), instructions, upstream revision, and complete preprint tree are frozen by [input-manifest.json](../sources/i30_einstein_metric_stability/input-manifest.json). The current argument does not reuse I27's varifold proposal or the concurrent I28/I29 work.

All corpus proofs at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises. The 34 selected EG/E0/E+ files are reused from I27, without copying the 9,340-file cache. Their pinned raw URLs, Git blob identities, SHA-256 and local paths are in [source-manifest.json](../sources/i30_einstein_metric_stability/source-manifest.json). The verifier checks these files against the complete tree, not the truncated root cache. [Contracts and read passages](../sources/i30_einstein_metric_stability/contracts.json) identify exactly what was read and used; retention is not represented as full semantic reading of every retained source.

* **EG**: *An L2 Einstein Gap for Nonnegatively Curved Four-Manifolds*, October 5, 2026, `build/source/main.tex`, read in full. Theorem `thm:gap` gives diffeomorphism types, not (1). Proposition `prop:limit` gives smooth positive-time convergence after time-independent diffeomorphisms.
* **E0**: *Zero-Plane Rigidity for Einstein Four-Manifolds*, October 4, 2026. `thm:main` and `cor:nonnegative-classification` include the product boundary. The actual curvature-block, coupling, equality and parallel-splitting arguments were consulted. They use exactly Einstein differential identities and do not give an approximate-metric theorem.
* **E+**: *Positively curved Einstein four-manifolds*, September 23, 2026. Its classification proof, including one-block reduction, exceptional harmonic-count exclusion, model scaling and global continuation, was consulted. It applies to strict sectional positivity and cannot replace E0 at the product.

EG already proves initial volume/diameter/Sobolev bounds, propagation of the high-curvature tail, common lifespan, noncollapse, `|Rm(t)|≤A/t`, small evolving Einstein defect, and an integral negative-sectional bound. Those are existing machinery. All estimates below begin after importing these inputs, with their quantitative dependence retained.

## 2. Primary comparison, before the construction

Fresh primary metadata and versioned PDFs are retained in [literature/manifest.json](../sources/i30_einstein_metric_stability/literature/manifest.json); query responses and version histories are separate artifacts. The decisive comparison is with actual proof operations, not keyword absence.

1. **[Tian–Wang, 1202.2912v1](https://arxiv.org/abs/1202.2912v1), Theorem 3.1, Lemmas 4.2–4.4, Theorem 4.1.** They study `∂_t g=−Ric+λ₀g`, `|λ₀|≤1`. The local theorem assumes `Ric(g(0))≥−(m−1)δ₀` and the **almost Euclidean** lower bound `Vol B_0(x,1)≥(1−δ₀)ω_m`. For `E=∫₀^{2δ₀}∫_Ω|R−mλ₀|`, their distance theorem has lower error `CE^{1/[2(m+3)]}` and upper relative error `CE^{1/[3m(m+3)]}`, with the stated smallness relative to the initial pair distance. Crucially, their proof already uses a missing-ball argument and packing along an initial geodesic to obtain the expansion bound. We do not claim that mechanism is new. Our proof below supplies a global two-metric version using EG's bounded geometry at a fixed time and a localized L² volume-change bound; it does not assume or silently infer their initial almost Euclidean volume hypothesis.
2. **[Chan–Chen–Lee, 2102.12840v3](https://arxiv.org/abs/2102.12840v3), Theorem 1.2 and §5.** Initial uniform Ricci lower bound, local entropy and small local full `L^{n/2}` curvature give smoothing with a small `Cε/t` coefficient. Their §5 also provides distance-topology comparisons via Huang–Kong–Rong–Xu; it is stronger than a bare existence theorem. The global Einstein defect is not their full-curvature smallness assumption. EG's tail plus a fixed small scale can supply that concentration assumption, but no model-distance rate follows just from stating their compactness theorem.
3. **[Huang–Kong–Rong–Xu, 1808.03774v1](https://arxiv.org/abs/1808.03774v1), Lemma 1.11; [Huang–Wang, 2008.09956v2](https://arxiv.org/abs/2008.09956v2), Appendix A.** These include time-zero distance comparisons, with pseudolocality/Reifenberg inputs or initial scalar lower bound, doubling/Poincaré control and a sufficiently small `α/t` Ricci bound. Hölder comparison constants are not a defect power tending to the identity. The published HKRX numbering cited by CCL is Lemma 2.4; only the retained arXiv version was read here, where the relevant lemma is numbered 1.11. Publisher-PDF retrieval was blocked by HTTP 403, which is recorded rather than treated as a read source.
4. **[Ma–Wang, 2109.02449v1](https://arxiv.org/abs/2109.02449v1), Lemma 5.1 and Theorems 5.2–5.4.** Their distance proof explicitly reuses Tian–Wang's packing. The short-range theorem assumes `p>m/2`, small negative-Ricci `L^p` norm at the indicated scale, and almost maximal initial ball volume. In our setting the negative Ricci part initially vanishes, but the volume input still needs justification. Their main round-sphere theorem has a prescribed sphere volume; it is not an all-three-model theorem from the critical Einstein defect.
5. **[Martens, 2408.11115v2](https://arxiv.org/abs/2408.11115v2), Theorems 1.1–1.2 and Remark 1.3.** The metric-measure compactness conclusion under volume-ratio, entropy and critical-curvature hypotheses explicitly does not guarantee distance convergence back to the limiting initial metric. The ineffective Ricci lower bound there is weaker than our initial nonnegative Ricci bound. This remark does not establish an impossibility in the present more restricted class.
6. **[Koiso, 1982](https://ir.library.osaka-u.ac.jp/repo/ouka/all/8420/ojm19_03_09.pdf), Lemma 2.4, Proposition 2.5, Theorem 5.7; [Gursky–Viaclovsky, 1105.4648v2](https://arxiv.org/abs/1105.4648v2), Proposition 7.7 and Proposition 7.9.** These supply the infinitesimal Einstein-rigidity and spectral inputs used at the fixed smooth slice. For CP² with `Ric=6g`, the TT `−Δ_L` bottom is **32**, hence **16** after normalization to `Ric=3g`. For the equal sphere product with factors of curvature one, the TT spectrum has a one-dimensional zero eigenspace and the next eigenvalue is at least four; after scaling to factor curvature three the next eigenvalue is at least twelve. The fixed-constant Einstein operator subtracts six. Thus product instability does not create a kernel of that operator.
7. **[Kröncke, 1312.2224v2](https://arxiv.org/abs/1312.2224v2), §8.** The positive-Einstein dynamical theorem has additional variational and spectral conditions. Its entropy-gradient inequality is not automatically a metric-distance-to-Einstein estimate. We use a local elliptic slice estimate, not an attracting-flow assertion.

These are bounded primary comparisons. No claim that the target or the material-volume refinement is absent from the literature is made. The explicit antecedent in item 1 is the main significance issue for this candidate.

## 3. Route A: direct segment comparison, and where it stops

Let `η=√D` and `H=|Ric−3g|`. EG gives `∥H∥₂≤√5η`, `v₀≤Vol≤V₀`, `diam≤D₀`. Initial `Ric≥0` and Bishop–Gromov give a lower bound `Vol B(x,r)≥c r⁴` for `0<r≤r₀`, with universal constants; the same comparison gives the upper bound `ω₄r⁴`.

For arbitrary endpoints `p,q`, use the initial segment inequality on `A=B(p,r)`, `B=B(q,r)`. Dividing by `Vol A Vol B` and using Cauchy–Schwarz gives

\[
 \fint_{A\times B}\int_{\gamma_{xy}}H\,ds\le C\eta r^{-4}.
 \tag{2}
\]

For a finite collection of endpoint-ball pairs, Markov's inequality bounds the fraction of bad pairs for each specified segment; one must not turn this into simultaneous control of all geodesics through a fixed point. In particular there exist perturbed endpoints within `r` of `p,q` whose segment has the right side of (2). Balancing `r` and `ηr^{-4}` suggests a scale `η^{1/5}` for this particular error budget.

This is genuine initial-metric information but does not identify a model. Even zero `H` does not determine the normal Jacobi matrix from its trace: round, Fubini–Study and product models have the same Ricci tensor but different sectional tensors. The algebraic inequality `|Rm|≤C R` prevents unbounded curvature at a point with bounded scalar, but the L² scalar-error estimate does not give that pointwise boundedness. An elliptic repair would need uniformly controlled coordinates before using `Ric−3g` as the forcing. Small critical full-curvature concentration at a fixed scale, obtained from `∫_B|Rm|²≤C(r⁴+η²)`, is not by itself the missing pointwise harmonic-coordinate estimate.

A direct attempt to perturb E0 also stops at a specific place: its divergence-free Weyl blocks and derivative identities use `∇Ric=0`. In the approximate setting the extra terms involve derivatives of `E`; `∥E∥₂` alone does not control them. Integration by parts would require an independently established derivative bound for the Weyl test tensors. We do not assume one. Thus (2), initial noncollapse and the exact classification do not constitute a direct proof of (1). This route is investigated but not completed; Route B below avoids that elliptic starting-scale problem.

## 4. Route B, step 1: uniform analytic inputs and the correct normalization

All constants in this section are chosen **before** the metric or any sequence index. Tracking EG's proofs fixes dimensional `K₀`, a small tail threshold, `v₀,V₀,D₀,S,A`, and `0<T<1/6` so that for sufficiently small universal `η` the smooth unnormalized flow exists on `[0,T]` and

\[
 |Rm(g(t))|\le A/t,\quad R(g(t))\ge0,\quad
 \|f\|_4^2\le S(\|\nabla f\|_2^2+\|f\|_2^2),
 \quad \|L(t)\|_2\le C\eta,
 \quad L(t)=Ric_{g(t)}-\frac3{1-6t}g(t).
 \tag{3}
\]

The last bound is quantitative: EG's energy absorption gives `Y'≤CY`, and `Y(0)≤5η²`. EG also supplies uniform volume noncollapse at every positive time. Its proof of the common lifespan precedes the compactness argument, so there is no assumed common interval.

Fix `τ=T/2` and put

\[
 c(t)=1-6t,\qquad \bar g(t)=c(t)^{-1}g(t),\qquad k=\bar g(\tau).
 \tag{4}
\]

This is an explicitly rescaled **finite-time** flow, not volume-normalized Ricci flow. On `0≤t≤τ`, `c` stays uniformly positive. At `τ`, (3), Shi estimates and EG's noncollapse give uniform curvature, derivative and injectivity-radius bounds for `k`. In particular, for a universal `r₀>0`,

\[
 \mu_k(B_k(x,r))\ge\omega_4 r^4(1-Cr^2)\ge c_*r^4
 \quad(0<r\le r_0).
 \tag{5}
\]

The first estimate follows in normal coordinates below the uniform injectivity radius, from the sectional bound and the radial Jacobian comparison. No initial injectivity radius or preservation of sectional nonnegativity is used.

### Smoothing the small tensor, rather than assuming a pointwise critical bound

EG gives the homogeneous equation `∂_t L=ΔL+2Rm(L)+2λL` in its moving frame. Kato therefore gives

\[
 (\partial_t-\Delta)|L|\le C(|Rm|+1)|L|.
\]

On each slab `[s/2,s]`, the potential is at most `C/s`. The global parabolic mean-value estimate using (3) gives

\[
 \|L(s)\|_\infty
 \le C s^{-3/2}\left(\int_{s/2}^s\int |L|^2\right)^{1/2}
 \le C\eta/s,\quad 0<s\le\tau.
 \tag{6}
\]

For clarity about uniformity, the energy calculation for `|L|^{p/2}` with a time cutoff gives a gradient term and an error `C(p/s+|χ'|)∫|L|^p`. The volume derivative contributes `−R|L|^p≤0`. The four-dimensional Sobolev inequality gives spacetime exponent `3p/2`; iteration with `p_j=2(3/2)^j` and nested time intervals gives the displayed `s^{-3/2}` spacetime factor. The product of iteration constants is finite because `∑1/p_j=3/2` and `∑j/p_j<∞`. Starting at `s/2` needs no initial derivatives. This proves (6) from the critical norm and smoothing, not at time zero.

### One-sided distance control with a nonzero stopping time

The global shrinking-distance estimate from the index form and `Ric≤C/t` gives

\[
 d_{g(s)}(x,y)\ge d_g(x,y)-C\sqrt s.
 \tag{7}
\]

Indeed an endpoint cutoff of length `√t` on a minimizing geodesic bounds its Ricci integral by `C/√t`; short geodesics satisfy the same lower barrier by the direct curvature bound. Integrate the resulting lower distance derivative. For each individual smooth flow its initial distances converge as `t↓0`, and the integrable bound has constants independent of that flow. This passage does not integrate (6) to zero.

Differentiating (4) gives `∂_t\bar g=−2L/c`, hence
`|∂_t\bar g|_{\bar g}≤Cη/t`. For `0<s≤τ`,

\[
 d_k\ge e^{-C\eta\log(\tau/s)}d_{\bar g(s)}
 \ge e^{-C\eta\log(\tau/s)}(d_g-C\sqrt s).
\]

Take **`s=η²`**, after decreasing the threshold so `η²<τ`. Using `diam(g)≤D₀` yields the uniform all-pair estimate

\[
 d_k(x,y)\ge d_g(x,y)-a_\eta,
 \qquad a_\eta=C\eta(1+|\log\eta|).
 \tag{8}
\]

The logarithm is harmless at this chosen stopping time. Sending `s` to zero in (6) remains invalid and is not done.

### Square-root volume control on every fixed subset

For a measurable subset `U⊂M` keep the subset fixed in the original manifold, and write `V_t(U)=Vol_{\bar g(t)}(U)`. Direct differentiation gives

\[
 \partial_t d\mu_{\bar g(t)}=-\operatorname{tr}_{g(t)}L(t)\,d\mu_{\bar g(t)}.
\]

In dimension four, changing the measure to `\bar g(t)` and using (3) shows `∥tr_g L∥_{L²(\bar g)}≤Cη`. Thus

\[
 |V_t'(U)|\le C\eta V_t(U)^{1/2},\qquad
 \big|V_t(U)^{1/2}-V_0(U)^{1/2}\big|\le C\eta t.
 \tag{9}
\]

All smooth volume densities are mutually absolutely continuous. For positive-measure `U`, divide by `2√V_t`; for null `U` the statement is immediate. Approximation or dominated differentiation on the compact manifold justifies arbitrary measurable sets. In particular,

\[
 \left|\sqrt{\mu_k(U)}-\sqrt{\mu_g(U)}\right|\le b\eta
 \quad\text{for every measurable }U.
 \tag{10}
\]

This is stronger for small sets than the global `O(η)` volume error. For an initial ball of radius `r`, Bishop comparison and (10) give

\[
 \mu_k(B_g(x,r))\le\omega_4r^4+C\eta r^2+C\eta^2.
 \tag{11}
\]

Only the original metric needs nonnegative Ricci curvature in (11).

## 5. The two-metric bridge, with complete packing argument

We now prove directly from (5), (8), (10), initial Bishop comparison and `diam(g)≤D₀` that

\[
 \sup_{x,y\in M}|d_k(x,y)-d_g(x,y)|\le C\eta^{1/8}.
 \tag{12}
\]

The constants depend only on the uniform data already fixed. Write `a=a_η` and `bη` for the error in (10). From (8),

\[
 B_k(z,\rho)\subset B_g(z,\rho+a).
 \tag{13}
\]

### A coarse comparison for nearby points

Let `L=d_g(x,y)` and `q=max{L,a,√η}`. Suppose `q` is below a fixed small fraction of `r₀`. Take a minimizing `g`-geodesic from `x` to `y`. Choose a maximal collection of points on its image separated by at least `q` in `d_k`. Their `k`-balls of radius `q/2` are disjoint, their balls of radius slightly more than `q` cover the connected curve, and each center has initial distance at most `L` from `x`.

By (13), all the disjoint balls lie in `B_g(x,3q)`. Formula (10) and initial Bishop comparison give

\[
 N c_* (q/2)^4\le\mu_k(B_g(x,3q))
 \le (\sqrt{\omega_4}(3q)^2+b\eta)^2\le Cq^4.
\]

Hence `N≤C`. The intersection graph of the covering balls along the connected curve is connected after discarding unused components. A chain between the balls containing the endpoints has at most `N` members. The triangle inequality gives

\[
 d_k(x,y)\le Cq\le C(d_g(x,y)+a+\sqrt\eta).
 \tag{14}
\]

One need not assume that the original geodesic has controlled `k`-length. The finite ball chain, rather than that length, is the argument. Compactness of the smooth curve justifies a finite maximal collection.

### No large hole in the inner later ball

Fix `r≤r₀/10`, with `a≪r`, and points with `d_g(x,y)=r`. The later ball `B_k(x,r−a)` is contained in `B_g(x,r)`. By (5) and (11),

\[
 \mu_k\big(B_g(x,r)\setminus B_k(x,r-a)\big)
 \le C\{r^6+ar^3+\eta r^2+\eta^2\}=:C H_r.
 \tag{15}
\]

For any initial ball `B_g(z,R)` contained in this difference, (13) places `B_k(z,R−a)` inside it. If `R>2a`, (5) then gives `cR⁴≤CH_r`. Choose

\[
 R=2a+C_1 H_r^{1/4}
 \tag{16}
\]

with `C₁` larger than the constants just obtained. **No** initial ball of radius `R` contained in `B_g(x,r)` can be disjoint from `B_k(x,r−a)`. Boundaries may be handled with open balls and a strictly larger `C₁`.

Suppose `R<r/4`. On an initial minimizing geodesic from `x` to `y`, take the point `w` at distance `r−2R` from `x`. Then `B_g(w,R)⊂B_g(x,r)` and every point in this ball is within initial distance `3R` of `y`. By the preceding conclusion there is

\[
 z\in B_g(w,R)\cap B_k(x,r-a).
\]

The choice (16) ensures `R≥2a` and `R≥c√η`; increasing `C₁` makes the latter constant at least one. Apply (14) to `y,z`; all radii are within its permitted range after decreasing the smallness threshold. We obtain

\[
 d_k(x,y)\le d_k(x,z)+d_k(z,y)\le r+CR.
 \tag{17}
\]

### Choice of scale and all-pair conclusion

Put `r=η^{1/4}`. The same estimates hold uniformly if the pair length lies in `[r,2r]`. Because `a=Cη(1+|logη|)`,

\[
 r^6=\eta^{3/2},\quad ar^3=O(\eta^{7/4}(1+|\log\eta|)),
 \quad\eta r^2=\eta^{3/2},\quad\eta^2\le\eta^{3/2}.
\]

Consequently `R≤Cη^{3/8}`, `R/r≤Cη^{1/8}→0`; this verifies every smallness condition above. Partition any initial minimizing geodesic of length `L≥r` into `N=floor(L/r)` equal pieces, each of length in `[r,2r]`. Summing (17) gives

\[
 d_k(x,y)\le L+C(L/r)\eta^{3/8}\le d_g(x,y)+CD_0\eta^{1/8}.
\]

For `L<r`, (14) instead gives `d_k(x,y)≤C(r+a+√η)≤Cη^{1/4}`, which is smaller than the required additive error. The lower bound (8) is also smaller than `Cη^{1/8}`. This proves (12). The identity correspondence, surjective on the same underlying set, gives `d_GH((M,g),(M,k))≤Cη^{1/8}`.

The proof never presupposes that the original metric is GH-close to the smoothed one, never transports a minimizing geodesic by an unproved gauge bound, and never invokes `sec≥0` at positive times. Formula (10) applies to the particular subsets in the packing argument even though those subsets are selected using both metrics: once selected, they are fixed subsets in the evolution calculation.

## 6. Converting the fixed smooth slice to a model, with a uniform rate

It remains to avoid replacing a quantitative conclusion by an unquantified positive-time compactness assertion. Fix small `C^{2,α}` slice neighborhoods of the three normalized models. EG `prop:limit`, E0 and E+ imply that, for a sufficiently small universal threshold on `η`, **every** `k` in (4) lies in one of these neighborhoods modulo diffeomorphism. Otherwise take a sequence with `η→0` outside their union, and apply the already proved positive-time convergence at the fixed `τ`. This contradiction establishes the threshold. It does not identify the original distance; (12) has independently done that.

On a model `(N,h)`, use the local divergence-free slice to choose a diffeomorphism with

\[
 \phi^*k=h+u,\qquad \delta_hu=0,\qquad\|u\|_{C^{2,\alpha}(h)}<\rho.
 \tag{18}
\]

The slice is obtained by solving the diffeomorphism gauge equation orthogonally to the Killing fields; its linearization in the vector field is `δ_h\mathcal L_Xh`, elliptic with kernel precisely the Killing fields. The implicit function theorem on their orthogonal complement supplies (18), with uniform bounds on this fixed neighborhood. The neighborhoods and constants are chosen for finitely many models. No time-dependent gauges near zero are used.

Set `F_h(q)=Ric_q−3q` and `P_h=DF_h|_h`. The overdetermined pair `(P_h,δ_h)` is elliptic, and on the divergence-free slice one has the estimate

\[
 \|u\|_{H^2(h)}\le C\|P_hu\|_{L^2(h)}.
 \tag{19}
\]

Here is the kernel check needed for (19), including the product. If `δ_hu=0` and `P_hu=0`, taking the trace is the scalar-variation equation
`(Δ_+−3)tr_hu=0`, where `Δ_+=−Δ`. The first nonzero scalar eigenvalue is at least four by the Ricci lower bound; constants also do not solve this equation. Hence `tr_hu=0`. On TT tensors, `2P_h=∇*∇−2\mathring{Rm}=−Δ_L−6` in the convention of Gursky–Viaclovsky.

* On the unit round sphere this is `∇*∇+2`, with no kernel.
* On normalized CP², Proposition 7.7 gives TT `−Δ_L≥16`, so subtracting six leaves a positive gap.
* On the normalized equal product, Proposition 7.9 gives TT spectrum `{0}∪[12,∞)` for `−Δ_L`. Subtraction of six has a **negative** eigenvalue on the relative-scale direction but no zero eigenvalue. Invertibility, not positivity, is what (19) requires.

The usual elliptic estimate initially has an added `∥u∥₂` term. If (19) failed, normalize a sequence in `H²`, use compactness in `L²`, pass to a kernel element, and apply the estimate again to obtain a contradiction. Thus (19) follows from the explicit kernel check, not from an assumption of flow stability.

The Taylor remainder satisfies

\[
 \|F_h(h+u)-P_hu\|_2\le C\rho\|u\|_{H^2}.
\]

Indeed its terms have the form `u*∇²u`, `∇u*∇u` and lower-order terms; bound one factor by `Cρ`. Absorb with (19) after fixing `ρ` sufficiently small. Pullback and equivalence of the nearby metric norms give

\[
 \|u\|_{H^2(h)}\le C\|Ric_k-3k\|_{L^2(k)}\le C\eta.
 \tag{20}
\]

The last inequality is (3): `Ric_k−3k=L(τ)` as a covariant tensor, and the L² norm of a covariant two-tensor is invariant under constant metric rescaling in dimension four.

We do **not** use the false critical embedding `H²→C⁰` in four dimensions. Instead (18) supplies a uniform `C¹` bound. If `m=max|u|`, a fixed-background ball of radius proportional to `m` has `|u|≥m/2`, unless `m=0`; its volume is bounded below by `cm⁴`. Therefore `∥u∥₂²≥cm⁶`, and (20) implies

\[
 \|u\|_{C^0}\le C\eta^{1/3},\qquad
 d_{GH}((M,k),(N,h))\le C\eta^{1/3}.
 \tag{21}
\]

The latter uses the identity after (18), uniform positive definiteness and bounded model diameter. Combining (12) and (21), and writing `η=√D`, proves (1). At `D=0`, almost-Schur gives `R=12`, so `Ric=3g` and the exact classification gives zero distance directly.

## 7. Limiting order, adversarial checks, and contribution boundary

The order is: fix EG constants and lifespan; fix `τ`; derive (6) on each positive slab; for each `η>0` stop at `s=η²`; derive the all-subset estimate (10) on `[0,τ]`; choose the **spatial** scale `r=η^{1/4}`; prove (12); only then use positive-time compactness to enter fixed elliptic neighborhoods and obtain (20). No interchange of `η→0` and an unbounded integral to time zero occurs. The constants may be ineffective because the neighborhood-entry threshold is obtained by compactness, but are universal. No explicit numerical value of `ε` is claimed.

The previously recorded unequal-product family remains a useful genuine geometric test. With unit factor metrics,

\[
 a=[3(1+u)]^{-1},\quad b=[3(1-u)]^{-1},\quad
 R=12,\quad D=64\pi^2u^2/(1-u^2).
\]

It is smooth, closed, simply connected and nonnegatively curved. Its identity comparison with the equal product gives `d_GH≤C|u|` for `|u|≤1/2`, consistent with the much weaker exponent in (1). Volume-normalized flow satisfies `a'=a/b−1`, `b'=b/a−1`; `ab` is constant and `|a−b|` increases, leading to finite-time collapse for unequal factors. Our finite-time rescaling (4) and elliptic inversion do not assert otherwise. The negative mode in §6 explicitly retains this instability.

The material-volume improvement matters to the exponent: replacing (10) by the cruder global error `|μ_k(U)−μ_g(U)|≤Cη` gives a hole budget `r⁶+ar³+η`. The same argument then chooses `r=η^{1/6}` and yields `η^{1/12}=D^{1/24}` instead. Thus the existence of *some* power has a particularly close relationship to the older Tian–Wang method; the L² refinement yields the stated `1/16`. Neither exponent is asserted optimal. This comparison must be retained in significance review; an affirmative metric theorem alone does not certify a substantial discovery under the I14/I15/I17 standard.

There is no slow-GH counterfamily in this report because the candidate argument is affirmative. Scalar spike functions or abstract curvature tensors have not been passed off as smooth `sec≥0` counterexamples. Critical norm smallness has nowhere been promoted directly to pointwise initial curvature control.

## 8. Reproduction and handoff

From the project root:

```sh
python frontier/experiments/i30_einstein_metric_stability/diagnostics.py
python frontier/experiments/i30_einstein_metric_stability/verify.py
python frontier/experiments/i30_einstein_metric_stability/seal.py --verify
```

The first checks exact volume-polynomial inequalities, scale/exponent budgets, normalization and product-flow identities, and the tensor-scaling rules. These are deterministic diagnostics of the written proof, not tests proving a geometric theorem. The verifier checks frozen inputs, all selected pinned sources and Git identities, primary retained bytes, exact read-passage hashes and scope. The seal covers the report and designated artifacts, excluding itself and derived verification outputs. Live shared-ledger drift is reported separately from frozen mathematical-premise changes. `fetch_primary.py` is a network retrieval script, not a retained-byte verifier.

Initial reproduction passes **20,698 exact diagnostic cases**, **11 frozen inputs**, **34 pinned source files**, **17 primary retrieval artifacts**, **7 contracts**, **21 read passages**, and **57 sealed artifacts**. The only live-input drift is the shared ledger: frozen SHA-256 `96eacd4b46a060066fc2255398dd0bedeb95a8eb2fc29c97b899e5af1ab53f94`, observed live SHA-256 `6f9cc44d3e77fb8083f5049f35b40125c501a9d66e7142f755cd137b9f907910`. The frozen ledger controls this report. Two publisher PDF attempts returned HTTP 403; the corresponding retained arXiv texts, rather than uninspected publisher versions, control their comparisons.

**Independent review targets:** the parabolic `L²→L∞` estimate with uniform evolving Sobolev data; the material-subset square-root volume estimate; the packing/hole lemma with its chosen scales; the divergence-free elliptic slice estimate including the product negative mode; and, separately, whether adaptation of Tian–Wang plus EG and standard rigidity clears the substantial-contribution gate. The author proof is complete as written, but is not an independent proof verdict. No shared index, staging area, commit, public repository or other project was changed; no agents were started.
