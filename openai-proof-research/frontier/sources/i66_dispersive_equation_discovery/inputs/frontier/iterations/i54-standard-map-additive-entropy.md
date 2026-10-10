# I54 — constant additive entropy loss for the exact standard map

2026-10-09. **Author-level proof of H under the stipulated pinned proof operations; independent analytic review pending.** No acceptance, priority, explicit numerical constant, or proof-assistant certification is claimed. The projective construction below also proves a uniform small-ball estimate on a precisely defined backward-fast set. It does not prove a full invariant conditional-density bound.

The decisive additional step is a quantitative *initial scale*, followed by a relative first crossing. I52's fixed-length initialization only established a vanishing normalized deficit. Its independently checked finite-time estimate actually supplies a growing initialization scale with deficit `O(1/log K)`. If the eventual deficit were an unbounded multiple of this, a crossing between the two deficits would satisfy **all** of the source's selected-scale limits. The source's fixed-test contradiction then rules this out. There is no need to apply its bridge theorem at a moving observation threshold, or to bound its strict terminal loss uniformly over different limiting measures.

## 1. Statement, scope, and independent I52 audit

Let

`f_k(x,y)=(x+y+k sin(2πx), y+k sin(2πx)) mod 1`,

and let `m` be normalized area. All logarithms in the conclusion are natural.

**Theorem H (deduction from accepted pinned operations).** There are absolute finite `C,K₀` such that for every real `K≥K₀`,

`h_m(f_{K/(2π)}) ≥ log(K/2)−C`.

The proof concerns the exact sine map, all sufficiently large parameters, and area entropy. It uses no perturbation, noise, parameter deletion, ergodicity of area, or pointwise expansion hypothesis. The constants are existential; this proof does not compute them. It does not establish the sharper conjecture `h≥log(K/2)` or a vanishing additive remainder.

The accepted source is *Positive Metric Entropy for the Standard Map at Large Parameters*, at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Both its statements and lower-level operations are premises, as instructed. The proof below audits where each operation is applied, rather than re-auditing its truth. Actual source passages, including the entire relevant sections, are bound in [source-contracts.json](../sources/i54_standard_map_additive_entropy/source-contracts.json) and [passages.json](../sources/i54_standard_map_additive_entropy/passages.json).

The full I52 report, verifier, original brief, objections, passage records, pinned manifest, seal, and parent replay record were read or bound directly. None was edited. The parent replay establishes provenance and finite checks, not analytic correctness.

**Audit S: PASS ORIGINAL WITHOUT REPAIRS, within its claimed scope.** Failure of relative asymptotics supplies a fixed positive eventual deficit. The same selected-scale limits and downstream contradiction apply. S alone has no modulus and is not the reason H holds. H uses the quantitative seed from F, which S's argument did not use. The statement that S is consistent with a `sqrt(log K)` additive loss remains correct when referring to S alone; that loss is incompatible with S's full source machinery **together with F**, as proved here.

**Audit F: PASS ORIGINAL WITHOUT REPAIRS.** For `K≥16`, `2≤b≤K/4`, and `n≥1`,

`a_n ≥ log(K/2)−2nb log(K+4)/K−2/[b(b−1)]`.  (1)

To check the signed bad-set subtraction explicitly, on the all-good set `G={|v(q_i)|≥b, 0≤i<n}`, the continuant from `(u₀,u₋₁)=(1,0)` obeys `|u_{i+1}/u_i|≥b−1`. Since `1/(b(b−1))≤1/2`, summing `log(1−z)≥−2z` gives the asserted growth error. The arcsine density of `v=2+K cos(2πq)` is at most `2/(πK)` on `[-b,b]`, so `m(Gᶜ)≤2nb/K`. Everywhere `log||T||≥0`; the sum of signed scalar logarithms on `Gᶜ` is bounded *above* by `n log M·1_{Gᶜ}`. Subtracting this upper bound is valid even where some scalar logarithms are negative. Jensen's circle factorization with two unit-circle roots gives `∫log|v|=log(K/2)`. No independence across orbit times is used.

**Audit U: PASS ORIGINAL WITHOUT REPAIRS.** The exact one-step norm satisfies `log||A(t)||=asinh(|t|/2)`. For `D(t)=asinh(|t|/2)−log|t|`, one has `D≥0`, `D(t)≤t⁻²`, and `∫ℝD=4`. Splitting at `|t|=K/2` gives `a₁−log(K/2)≤8/(πK)+4/K²≤4/K`. Thus `h≤a₁≤log(K/2)+4/K`. This is an upper estimate; it is not reversed below.

**Audit invariant lift and conditional P: PASS ORIGINAL WITHOUT REPAIRS as a conditional statement; hypothesis GAP.** The continuous projective integrand is bounded by `log M` in absolute value at each fixed K. Angular averaging, Oseledets, and bounded convergence identify every Cesàro weak limit's integral with h. Under the proposed conditional q-density bound, the cosine sublevel estimate gives the claimed slope tail and integrability, including absence of vertical mass. The original proof correctly separates the two potentially unbounded logarithms only after proving those tails. No deterministic verification of its full conditional-density premise was found. H below does not use it.

## 2. Exact source interface and a usable contradiction principle

In area-preserving transfer coordinates `(q,p)=(x,x−y)`, set

`F(q,p)=(φ(q)−p,q)`, `φ(q)=2q+k sin(2πq)`,

`A(q)=[[v(q),−1],[1,0]]`, `v=2+K cos(2πq)`, `M=K+4`, `ℓ=log M`.

Write `g(i,j)=log_M||T_{i,j}||`, `a_n=n⁻¹∫log||T_{0,n}||dm`, and `e_n=1−a_n/ℓ`. Determinant one, stationarity and the source Oseledets/Pesin interface give

`0≤e_n≤1`, `d(K):=lim_n e_n=1−h/ℓ`,

`e_n≤e_{2n}≤D e_n+D/n`  (2)

for an absolute `D≥1` and all sufficiently large K. A finite lower bound on `a_n` is never substituted for a lower bound on h.

The following is an explicit interface extracted from the actual source proofs, not a new axiom.

**Selected-scale impossibility SC.** There is no sequence `K_j→∞`, dyadic integers `n₀(j)<N(j)`, and `ε_j=e_{N(j)}(K_j)>0` for which

`n₀→∞`, `ε→0`, `ε n₀→∞`,

`e_{2^m n₀}=o(ε)` and `e_{2^m N}=O_m(ε)` for every fixed integer m.  (3)

All expressions with negative m are used only once the lengths are integers.

Here is the complete downstream applicability check. The source's zero-exponent assumption occurs at `scales.tex:scale:long-deficit`, to ensure a first crossing exists. Inspection of the proofs after `scale:selection` shows that (3), stationarity, and the already accepted matrix/cancellation/bridge operations are their inputs. The rate `e_n→1` does not reappear in those arguments.

* Put `μ_j=ε⁻¹ Σ_{n₀≤n<N, dyadic} Law(g_n)`, `ν_j=ε⁻¹ Law(g_N)`, and `ξ_j=ε⁻¹ Law(g_{n₀})`, using the source floor convention. Telescoping `J(I)` and the second-moment inequality for `V(I)` give the source local test bounds. In particular the initial tests have mass `o(1)` and each terminal shifted test has mass `O_I(1)`. The finite-test cover and compact-array topology yield locally finite vague limits away from affine arrays. The normalized four-point error tends to zero. This is `scale:local-mass` through `scale:limits`.
* `Sg_n=g_{2n}` exactly, so `S_*μ=μ+ν`, and positivity yields `μ=μ∞+Σ_{j≥1}(S⁻ʲ)_*ν`. All required local finiteness and translation invariance come from those same tests, not ergodicity. This is `scale:decomposition`.
* A fixed forbidden cancellation has mass at most `C ε⁻¹e^{−γt n₀}→0`. A fixed fast bridge with endpoint weight `W=J(I)+V(I)` and event `H=h(I′)>η` has weighted mass bounded by `C_{I,I′,η} ε[O_I(1)+ε⁻¹Σ M^{−σrn}]→0`. Here r and η are fixed and positive. These are precisely the hypotheses in `shape:exclusions`. The fast-bridge indicator is retained. The shape classification and cross-loss bound therefore apply unchanged.
* The source cap Φ is chosen once, from its fixed `c_b,δ`. Its slope α near zero satisfies `10C_*α<1`; `c_Φu≤Φ(u)≤C_Φu`. Terminal normalization yields `H_Φ=lim∫Φ(h₁)dν_j∈[c_Φ,C_Φ]`. The initial capped integral is `o(1)` because of (3).
* The exact balance `∫Gdμ=H_Φ` retains all weighted mass. At affine speeds ≤`c_b`, cap derivatives vanish. At every speed strictly between `c_b` and 1, the proof chooses a fixed rational bridge threshold; there is no threshold depending on K. At unit speed, for each **fixed** dyadic q, truncation gives `λ_J(U_q)≤q+O((εn₀)⁻¹)`. First take the weak limit, then let q decrease. This is `end:balance`.
* The terminal series is absolutely convergent because `Σ∫|G(S⁻ʲd)|dν≤∫|G|dμ<∞`. If `ν=0`, its contribution is zero and `H_Φ≥c_Φ>0`. Otherwise the nonempty slow interiors, their countable dyadic cover, and translation invariance give `Δ_ν:=∫liminf_m Φ(h_{2⁻ᵐ}(0))dν>0`. Thus its contribution is at most `H_Φ−Δ_ν`. This is `end:terminal`; Δ is a strictly positive number for the one extracted limit, not a claimed uniform numerical constant.
* The invariant remainder contributes ≤0 by `end:remainder`. On the two-ray band its bound is `−(1−2αC_*)I₀≤−(4/5)I₀`; one-ray mass vanishes by finite endpoint intensity and translation/dilation invariance; entirely slow arrays contribute zero. Consequently `∫Gdμ<H_Φ`, contradicting the exact balance. This proves SC under the accepted operations.

**Observation complexity and quantifier check.** W uses three shortfalls: `J=h(I)−(h(I_l)+h(I_r))/2` has maximum-norm Lipschitz constant ≤2, and `V=(h(I_l)−h(I_r))²` has constant ≤4. Thus W has `(R,L,B)=(3,6,2)` as a safe bound; H has `(1,1,1)`. These bounds never grow with K, N, or the number of dyadic scales. Each endpoint window is fixed after choosing its test; alignment holds because `n₀→∞` through powers of two. The threshold η in this paragraph is distinct from the crossing threshold θ below. The latter is **not** fed to `bridge:theorem`.

SC is stronger than S as an interface: it forbids a sufficiently separated amplification from a small growing-scale seed. A useful general formulation is that for any prescribed dyadic `n₀(K)→∞` with `u(K):=e_{n₀}(K)+1/n₀→0`, the ratio `d(K)/u(K)` is eventually bounded. If not, along a sequence with this ratio tending to infinity choose `θ=√(d u)` and use (2). Then `u=o(θ)`, `θ≤√u→0`, and `θn₀≥√(d/u)→∞`, reproducing (3). This is a relative compactness argument with a supplied quantitative seed; it does not claim a modulus for an unspecified seed.

## 3. Construction A: the quantitative seed closes H

Choose, for all sufficiently large K,

`n₀(K)=2^{floor(log₂(K^{1/4}))}`, `b(K)=K^{1/8}`.

Thus `K^{1/4}/2<n₀≤K^{1/4}` and `2≤b≤K/4`. By (1),

`a_{n₀}≥log(K/2)−R_K`,

`0≤R_K≤2 K^{−5/8}ℓ+4K^{−1/4}→0`.  (4)

In particular

`e_{n₀}≤[log(2+8/K)+R_K]/ℓ=O(1/ℓ)`,

`1/n₀=o(1/ℓ)`.  (5)

This is a proved rate, at a growing horizon, with no numerical trajectory input.

Suppose H is false. Equivalently, `B(K):=ℓ−h=d(K)ℓ` is unbounded as `K→∞`, because `ℓ−log(K/2)=log(2+8/K)` is bounded. Choose `K_j→∞` with `B_j→∞`. This choice follows from the negation of the existential uniform C,K₀ conclusion. Set

`θ_j=√(d(K_j)/ℓ_j)=√B_j/ℓ_j`.

The following quantitative separations are crucial:

`θ≤ℓ^{-1/2}→0`, `d/θ=√B→∞`,

`(e_{n₀}+1/n₀)/θ=O(B^{-1/2})→0`,

`θn₀≥K^{1/4}√B/(2ℓ)→∞`.  (6)

For large j, `e_{n₀}<θ<d`. Since the dyadic deficits increase to d, there is a first dyadic `N>n₀` with `e_N>θ`. Put `ε=e_N`. Its predecessor satisfies `e_{N/2}≤θ`, and (2) gives

`θ<ε≤Dθ+2D/n₀=O(θ)→0`.

Therefore `εn₀→∞`. For each fixed nonnegative m, iterating (2) gives

`e_{2^m n₀}≤D_m(e_{n₀}+1/n₀)=O_m(1/ℓ)=o(ε)`,

`e_{2^m N}≤D_m(ε+1/N)=O_m(ε)`.

For fixed negative m use dyadic monotonicity. These are exactly (3), which SC excludes. Hence B is eventually bounded, proving H. This proof does not require S as an intermediate theorem.

**Why the terminal margin issue is paid.** The argument never tries to compute C from a uniform lower bound for Δ_ν. An unbounded B would produce one limiting system with exact balance and a strictly positive Δ_ν (or ν=0). That one system is impossible. This suffices to prove boundedness of B. Were an explicit numerical C or effective K₀ requested, the present compactness and terminal argument would not supply them. A limit contradiction with a quantitative seed proves a big-O rate even when it does not calculate its constant.

**Actual summable loss conclusion.** For every `n_*≥1` and all sufficiently large K, the exact identity from I52 now yields

`0≤Σ_{j≥0} E L_{2^j n_*}/(2^{j+1}n_*)=a_{n_*}−h≤C+4/K`,  (7)

using `a_{n_*}≤a₁` and U. Thus the dyadic loss budget is uniformly summable. Equation (7) is a consequence of the proof just given, not an independently assumed renewal estimate. Individual summand decay and a constructive renewal-time tail are not established. In particular, the unsummable term in the source's crude mean-cancellation estimate has not been falsely summed.

## 4. Construction B: deterministic coarea for past-fast projective directions

This construction is independent of Construction A up to its final optional use of H. It supplies actual slope geometry, rather than imposing a conditional q-density hypothesis.

Fix the source graph exponent `c=0.98`. For integers `B≥2`, define the closed sets

`E_B={z: ||T_{0,−l}(z)||≥M^{cl} for every 1≤l≤B}`,

and `E∞=⋂_{B≥2}E_B`. All statements below hold for `K≥K₁`, where K₁ and every unspecified constant are absolute. There is no dependence on B or time origin. Real graph charts use the source square side `1/32`, extensions of radius `1/4`, and the exact backward recurrence.

**Proposition G.** On E_B one can measurably select one of the two backward Dirichlet graph tangents `r_B=dp/dq` from `bridge:graphs`, with

`|r_B|≤C M^{-4/5}`,

`m(E_B∩{|v(q)−r_B(z)|<s})≤C min(1,s/K)` for every s>0.  (8)

At Oseledets-regular points of E∞ the unstable slope rᵘ exists, is finite, and

`|r_B−rᵘ|≤C M^{1−c−2cB}`, `|rᵘ|≤C M^{-4/5}`,

`m(E∞∩{|v(q)−rᵘ(z)|<s})≤C min(1,s/K)` for every s>0.  (9)

Moreover, writing `X=log⁺(K/|v−r|)` on either of these restricted laws,

`∫_{X>T}X ≤ C(T+1)e^{-T}`, `T≥0`.  (10)

These are restrictions of area, without normalization by `m(E_B)` or `m(E∞)`. They are not assertions about every invariant projective direction.

**Proof: identification and a new curvature estimate.** Apply `bridge:graphs` to the backward orbit, whose ordered initial variables are `(p,q)`. At each eligible point at least one of the rows `j=B−1,B` satisfies the source row lower bound. Pick the first eligible row, a Borel choice. Its level graph is `p=P(q)`, a past-coordinate level set. The graph slope is `r_B=P′(q)`.

The source proves for its backward positions `\tilde q_a` and variations `U_a=d\tilde q_a/dq` that

`|U_a|≤C M^{-4(a+1)/5}`, `0≤a<j`,

with boundary values `U₋₁=1`, `U_j=0`. Let D be the j-by-j Dirichlet matrix with diagonal `v(\tilde q_a)` and off-diagonal entries −1. Its inverse is the source Green matrix `G_{ab}=t_{min(a,b)}U_{max(a,b)}`, with `t₀=1`. In particular `G_{0a}=U_a`.

Differentiate the variational boundary problem once more along the graph. The boundary second variations vanish, and

`D U′=−(φ″(\tilde q_a)U_a²)_a`.

Consequently the exact identity

`P″(q)=−Σ_{a=0}^{j−1} φ″(\tilde q_a)U_a³`

gives

`|P″|≤C M Σ_{a≥0} M^{-12(a+1)/5}≤C M^{-7/5}`.  (11)

This uses the *varied* Green identity, which holds throughout the extended regular graph; it does not assume neighboring points retain eligibility. The determinant/distortion proof guarantees that D stays invertible there. This curvature estimate is what allows the sublevel event to be transported along an actual tangent graph.

**Proof: coarea with the actual area Jacobian.** For each of the two endpoint choices and each source grid square, label backward graphs by their p-intercept t at a fixed q-coordinate q_c. They are `p=Y(t,q)`. The source's transverse determinant ratio gives

`0<c₁≤|∂_tY|≤C₁`,

and distinct labels have disjoint graph images. The label set has bounded length: each graph remains within `O(M^{-4/5})` of its original square over the fixed chart interval. Local smooth extensions across compact eligible label subsets are supplied exactly as in `bridge:graphs` and the final chart argument in `bridge:theorem`. Thus ordinary change of variables on countably partitioned local charts applies even when eligibility has empty interior.

On a fixed graph the relevant function is `v(q)−∂_qY(t,q)`. For `0<s≤K/4`, membership in its s-sublevel forces `|cos(2πq)|≤1/2` once K is sufficiently large, because `|∂_qY|≤1`. This lies on two fixed arcs where `|v′(q)|≥π√3 K`, of opposite fixed signs. By (11), its derivative has the same sign and absolute value at least K on those arcs. Each arc contributes at most `2s/K` to length. Multiplication by the bounded area Jacobian, integration over a bounded label set, and summation over the finite grid and two row choices give (8). For `s>K/4`, use the trivial bound 1 and enlarge C. Dropping the eligibility restriction on a graph is legitimate for this upper bound. Measurable row selection cannot increase the sum over both choices.

**Proof: passage to infinite history and uniform integrability.** For inverse transfer products, `bridge:direction-step` and the all-prefix inequalities show that their most contracted input lines converge with angular error at most

`Σ_{l≥B} M/(D_lD_{l+1})≤C M^{1−c−2cB}`.

The selected Dirichlet row kernel differs from the B-step contracted line by `O(D_B^{-2})`, by the same row lower bound used in the source. In the swapped coordinates these lines are almost vertical; in `(q,p)` they are almost horizontal. Angular error and slope error are therefore comparable. Oseledets identifies the limiting inverse-contracting line with the forward unstable line. Indeed `lim B⁻¹log||T_{0,−B}||≥cℓ>0` on the Oseledets-regular part of E∞. This proves the slope approximation in (9).

For fixed s, apply (8) on E∞ with sublevel radius `s+C M^{1−c−2cB}` and send B to infinity. This proves (9), including zero resonant mass. The finite restricted measures `(z,r_B(z))_*(m|E_B)` converge weakly to `(z,rᵘ(z))_*(m|E∞)`: `m(E_B\E∞)→0`, slopes converge uniformly on E∞, and the base exceptional Oseledets set is null. Bounds (8)–(9) give `P(X>t)≤Ce^{-t}`. Layer cake, including the boundary term `T P(X>T)`, gives (10). Thus these singular logarithms are uniformly integrable in B and K; weak convergence of their integrals follows by truncation. No finite angular density bound of size `M^{2B}` is used. The slope logarithm is bounded by `C M^{-8/5}` on these sets.

**Where these sets occur: an all-scale mass budget, not an independence assumption.** For each fixed integer L, choose a norm-realizing vector for `T_{0,N}` and follow its logarithmic norms along the N-step segment. Its total base-M shortfall is `N−g(0,N)`. If at time `i∈[L,N]` a backward prefix of length at most L violates the E_L condition, the vector increments across that same interval are less than `c` times its length: the vector growth ratio is bounded by the corresponding operator norm, and inverse/forward norms agree. The source shortfall-count lemma removes at most `4[N−g(0,N)]/(1−c)` such endpoints. Taking expectation and using stationarity gives

`(N−L+1)m(E_Lᶜ)≤4N e_N/(1−c)`.

First send N to infinity at fixed K and L, then L to infinity. Thus

`m(E∞ᶜ)≤min(1,4d(K)/(1−c))`.  (12)

All finite prefixes and the full past are covered. This supplies an average occurrence budget; it does not assert a tail bound for the waiting time to the next eligible state. On a finite fast bridge the source additionally supplies a positive fraction of **two-sided** eligible middle times; those require the bridge event, not (12) alone.

**Payoff and remaining scope of this construction.** For an entropy-realizing invariant projective lift, its restriction over the positive-exponent set is the unstable lift. One justification is recurrence: outside the stable line, forward projective iterates converge to the unstable line; an invariant probability cannot retain mass off both invariant lines there. Its exponent integral equals the top integrated exponent, excluding stable-line mass wherever λ>0. E∞ is in that positive-exponent set modulo null sets.

On E∞, (9)–(10) give a genuine uniform logarithmic lower bound for the numerator in the projective formula; the denominator is bounded by `CM^{-8/5}`. On E∞ᶜ only the bounded continuous *difference* `g≥−ℓ` is used. With `α_K=m(E∞ᶜ)`, this gives

`h≥(1−α_K)log K−C−α_Kℓ`.  (13)

Before Construction A, (12) and S give merely `α_K=o(1)`. Substitution of (12) into (13) does **not** close H: its feedback coefficient `4/(1−c)=200` is too large. After Construction A, (12) becomes `α_K=O(1/ℓ)`, an actual all-time exceptional-mass bound, and (13) is consistent with H. This ordering is essential; (13) is not offered as an independent second proof of H. A full small-ball estimate for ν on E∞ᶜ remains unproved, and bounded entropy loss alone does not establish it.

For comparison, if a full invariant lift with no vertical atom satisfied `ν(|v−r|<s)≤A(s/K)^β`, `0<s≤K`, then invariance would give `ν(|r|>R)≤A(KR)^−β` for `R≥1/K`. Layer cake gives `∫log⁺(K/|v−r|)≤A/β` and `∫½log(1+r²)=O_β(AK^{-min(β,1)})` for `0<β≤1` (at β=1 this bound also holds directly). These prove H. This routine criterion is recorded only to distinguish it from (8)–(12); its full-measure premise has not been proved.

## 5. Primary literature and novelty boundary

The complete pinned tree (13,223 entries, 749 manuscripts) and the full ignored corpus (9,340 files) were used. The `rg --files --no-ignore` inventory and three targeted line-multiset searches are retained. The standard-map hits identify the one relevant master; unrelated uses of the words “standard map” in algebra were excluded by reading their context. No companion additive theorem was found in this corpus search. The 719-manuscript catalogue and truncated root tree were not treated as complete.

Fresh primary retrievals and actual theorem passages were checked before settling the proof. The version history pages observed Knill v2, BXY v1, Blumenthal v1, Buzzi–Crovisier–Sarig v1, Duarte–Klein AP v1, and Duarte–Klein continuity v2. The archived records distinguish arXiv versions from published journal versions; no claim that v1 is the final journal text is made.

* [Knill, math/9908014v2](https://arxiv.org/abs/math/9908014v2), opening notice and Conjecture 1.1: the old lower proof was withdrawn; the explicit additive estimate is conjectural. H does not recover his proposed explicit remainder. His [7–8 October 2026 author response](https://www.quantumcalculus.org/positive-entropy-for-standard-map-by-open-ai/) still distinguishes the large-parameter positivity announcement from the exact `log(K/2)` lower conjecture. This is an author status response, not proof evidence.
* [Blumenthal–Xue–Young, 1701.07583v1](https://arxiv.org/abs/1701.07583v1), Theorems 1–3, Corollary 4 and projective stationary-measure method: the noise lower bounds are positive (`ε≥L^{−C L^{1−β}}`, and under H3 `ε≥L^{−C L^{2−β}}`). They cannot be sent to zero at a fixed L under those hypotheses. The overall good/bad projective integral strategy is credited to this work. The deterministic Dirichlet-tangent estimate above uses the pinned graph operation instead of noise diffusion.
* [Blumenthal, 1710.09058v1](https://arxiv.org/abs/1710.09058v1), Theorem D: its fixed-parameter correlation error deteriorates with n. The long-time theorems require increasing parameters. It supplies neither an all-time area-entropy lower bound nor the fixed-K exceptional return-time estimate missing from Construction B.
* [Buzzi–Crovisier–Sarig, 2103.02400v1](https://arxiv.org/abs/2103.02400v1), Theorem A and Corollary 1.1: smooth convergence of maps, appropriate ergodic measure hypotheses, and entropy convergence govern continuity of exponents. The large-K family has no such compact smooth-map limit. No uniform additive rate follows from this interface; positive entropy already known qualitatively is insufficient to use it in that way.
* [Duarte–Klein, 1507.02967v1](https://arxiv.org/abs/1507.02967v1), Theorem 4.1 and Proposition 4.2, require quantitative singular gaps and consecutive-product alignment. [Their continuity theorem, 1410.0699v2](https://arxiv.org/abs/1410.0699v2), Theorem 1.1 and Definitions 1.5–1.6 require base and uniform fiber large-deviation estimates. None of these unpaid hypotheses is inferred from area stationarity or rare critical visits. These external results are not premises of H.

The accessible [MathDB problem 345911](https://mathdb.com/p/345911/sinais-positive-entropy-conjecture-for-the-standard-map) concerns Sinai's positive-entropy problem; no numerical importance score was observed. H addresses its large-parameter quantitative remainder. The mechanism proving H here is a strengthened use of accepted source operations with an elementary quantitative initialization. Its analytic consequence is distinct from positivity and S, but whether it meets the project's substantial-contribution standard requires the parent's separate judgment. It is not represented as an independent solution without the stipulated corpus, or as a priority claim.

## 6. Adversarial checks, failures retained, and reproducibility

The exact rare-bad-site periodic cocycle from I52 still has exponent zero: if `A(L)^{2m}=[[P,−Q],[Q,−R]]`, then `A(2Q/P)A(L)^{2m}` has trace zero and its square is −I. It is not a standard-map orbit and does not meet the full source cancellation/bridge contract. Nothing in this proof deduces H from visit frequency alone.

The actual fixed points at `k_j=√(j²+π⁻²)` still have transfer matrix `A(0)` and zero exponent. They have zero area and are outside E∞. The law with uniform base and `r=v(q)` still has exact cancellation and is noninvariant. Neither is excluded by pretending all tangent directions are regular. These obstructions were retained, not numerically “repaired.”

The unsuccessful feedback from (12)–(13) is a genuine mathematical limitation of that route. The prior finite-horizon-to-entropy shortcut and attempted summation of `Cℓ e_n` remain invalid. Construction A instead changes the selected-scale initialization and pays the crossing separation in (6). No new trajectory simulation was used as entropy evidence.

The [diagnostics](../experiments/i54_standard_map_additive_entropy/diagnostics.py) check exact rational continuants, trace-zero obstructions, Green inverses, and the new curvature identity by independent matrix algebra. They include exact exponent bookkeeping for (4), (6), and (11), and a deliberately invalid critical Green matrix as a negative control. Floating examples illustrate the threshold ratios for slowly unbounded hypothetical B; they are explicitly synthetic, not standard-map entropy computations. The [output](../experiments/i54_standard_map_additive_entropy/diagnostics.json) labels these categories separately.

All evidence is confined to the authorized I54 directories and this report. The [verbatim brief](../sources/i54_standard_map_additive_entropy/brief.txt), frozen inputs, direct pinned copies, source contracts, primary HTTP responses, extracted passages, searches, and experiment code are covered by [seal.json](../sources/i54_standard_map_additive_entropy/seal.json). No previous archive was recursively copied and no old seal was refreshed. Four shared status ledgers are explicitly mutable. The read-only verifier checks every prior I52 sealed artifact live, all direct pins against the complete tree, every corpus blob, response bodies, PDF extractions, passage ranges, search multisets and diagnostic replay. It reports mutable drift separately.

Run from the repository root:

```bash
python frontier/experiments/i54_standard_map_additive_entropy/verify.py
```

The recorded verifier passes 7,327 exact finite assertions, sixteen successful fresh HTTP responses, six PDF re-extractions, all 9,340 corpus blobs, and all 170 unchanged I52 sealed artifacts. Changes to the four shared ledgers during this run are reported as mutable drift. This is provenance and finite-algebra verification, not independent analytic proof acceptance. The remaining review-sensitive interfaces are the SC extraction after the changed initialization and the restricted projective graph-to-coarea argument, especially its varied Green identity and eligibility complement. Full invariant anti-concentration, an explicit numerical C, and renewal-time tail bounds are not claimed.
