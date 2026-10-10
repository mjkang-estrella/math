# I57 — independent audit of the original I54 standard-map entropy proof

2026-10-09 (America/Los_Angeles). **H: PASS ORIGINAL WITHOUT REPAIRS**, under the stipulated truth of the pinned OpenAI statements **and proof operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. This is an applicability and deduction audit, not an audit of upstream truth. No author text was changed. No finding-count, acceptance, worldwide-priority, or final contribution verdict is assigned.

The original proof establishes absolute, existential constants `C,K₀` such that

`h_m(f_{K/(2π)}) ≥ log(K/2) − C` for **every real `K≥K₀`**,

for the exact sine map and normalized area. Its essential step is valid: a growing seed with normalized deficit `O(1/log K)`, together with the entire accepted selected-scale contradiction, rules out an unbounded additive deficit. This uses one limiting contradiction, not a quantitative terminal margin uniform over all limiting systems. The bridge is always invoked at fixed observation thresholds.

Separate original-proof verdicts:

- **SC and the relative-seed amplification argument: PASS ORIGINAL WITHOUT REPAIRS.** The displayed selected-scale hypotheses suffice for the downstream accepted operations.
- **G, finite-history graph/coarea estimate: PASS ORIGINAL WITHOUT REPAIRS**, including both row choices, the backward coordinate swap, curvature on extended arcs, and bounded area Jacobians on possibly thin eligible sets.
- **G, infinite-history slope estimate and logarithmic tails: PASS ORIGINAL WITHOUT REPAIRS**, for restricted area on `E∞`, with the stated exponent and order of limits.
- **All-prefix exceptional-mass budget: PASS ORIGINAL WITHOUT REPAIRS.** The constant is `4/(1−0.98)=200`; this is an occurrence/mass estimate, not a renewal-tail estimate.
- **I52 S/F/U and the invariant-lift construction: PASS ORIGINAL WITHOUT REPAIRS. Conditional P: PASS ORIGINAL WITHOUT REPAIRS as a conditional theorem.** Its deterministic conditional-density hypothesis remains unpaid.
- **Uniform summable dyadic cancellation budget: PASS ORIGINAL WITHOUT REPAIRS as a consequence of H.** It is not an independent input to H and supplies no individual summand rate.

The full original I54 and I52 reports, briefs, objections, source contracts and evidence were examined. The complete pinned standard-map sections `introduction`, `setup`, `cancellation`, `local-scarcity`, `bridge`, `scales`, and `geometry` were read, including the proofs, rather than only the extracted I54 interface. The relevant files are frozen in [I57 sources](../sources/i57_standard_map_additive_entropy_r2/); [passages.json](../sources/i57_standard_map_additive_entropy_r2/passages.json) binds full sections and the external scope passages.

## 1. Basic interfaces and independently checked I52 deductions

Use `(q,p)=(x,x−y)`, `F(q,p)=(φ(q)−p,q)`, `φ(q)=2q+k sin(2πq)`, `v=φ′=2+K cos(2πq)`, `K=2πk`, and `M=K+4`. Let `ℓ=log M` and `A(q)=[[v(q),−1],[1,0]]`. These are exactly the source's map and transfer coordinates. The fixed coordinate change preserves area and exponents. The source's Pesin interface applies without ergodicity: smoothness, compactness, invariance and bounded derivative/inverse logarithms hold at each fixed K.

Write `a_n=n⁻¹ E log||T_{0,n}||`, `e_n=1−a_n/ℓ`, and `d=1−h/ℓ`. Determinant one gives `0≤e_n≤1`; stationarity and subadditivity give `a_n→h=inf_n a_n`, hence `e_n→d`. Along each dyadic chain,

`e_n ≤ e_{2n} ≤ D e_n + D/n`.

The upper inequality is `scale:doubling`, with absolute D after a single absolute parameter cutoff. Its proof uses cancellation and stationarity, not zero exponents. The lower inequality is subadditivity in the correct direction. In particular a finite lower bound for `a_n` never lower-bounds `h` directly.

**F.** At every orbit time, the scalar `v(q_i)` has density `[π√(K²−(t−2)²)]⁻¹`. On `|t|≤b≤K/4`, `K≥16`, this density is at most `2/(πK)`. Thus the union of the n bad strips has mass at most `2nb/K`, without independence. On the complement, the signed continuant recurrence with initial data `(1,0)` has successive absolute ratios at least `b−1`. The relative perturbation of each scalar coefficient is at most `1/[b(b−1)]≤1/2`, so `log(1−u)≥−2u` yields

`log||T_{0,n}|| ≥ Σ_{i<n}log|v(q_i)| − 2n/[b(b−1)]`.

Outside that complement the left side is nonnegative. The *upper* bound `Σlog|v(q_i)|≤nℓ` on the bad set permits subtracting its integral; no positivity of each scalar logarithm is needed. The circle factorization

`2+K cos(2πq) = (K/(2z))(z²+(4/K)z+1)`, `|z|=1`,

has both roots on the unit circle for K>2. The integrable circle logarithms give mean `log(K/2)`. This proves the original F, with exactly its constants and all n:

`a_n ≥ log(K/2) − 2nbℓ/K − 2/[b(b−1)]`.

**U.** The singular-value calculation gives `log||A(t)||=asinh(|t|/2)`. For `D(t)=asinh(|t|/2)−log|t|`, direct differentiation/integration gives `D≥0`, `D≤t⁻²`, and `∫ℝD=4`. The density bound on `|t|≤K/2` and the complement bound `D≤4/K²` yield `a₁≤log(K/2)+8/(πK)+4/K²≤log(K/2)+4/K`. Thus `h≤a₁`, not the reverse.

**Invariant lift and P.** The projective increment is continuous, including the vertical line, and belongs to `[-ℓ,ℓ]`. Starting from area times angular measure, telescoping and Oseledets give the top exponent for almost every base/direction pair. The stable exceptional line has zero angular mass, and the bound by ℓ permits dominated convergence. Cesàro limits are invariant, project to area, and have increment integral h. This argument makes no uniform angular-density assertion after iteration.

Under P's *additional* conditional q-density bound, cosine sublevels give `ν(|v−r|<s)≤4C₀√(s/K)` for finite r. The preimage of the vertical line is `r=v(q)`; conditional absolute continuity gives it zero mass, so invariance eliminates the vertical atom. Then `ν(|r|>R)≤min(1,4C₀/√(KR))`. Integrating this tail with weight `R/(1+R²)` bounds the denominator logarithm by `CC₀/√K`. A second layer-cake calculation bounds the negative scalar logarithm in the numerator by `8C₀`. The positive part is integrable by the slope tail. Only after these checks may the continuous increment be split into its two logarithms. P therefore passes, but area projection alone supplies none of its conditional regularity.

**S.** If S fails, a fixed η>0 bounds d from below along a parameter sequence. Choose the original slowly growing dyadic seed and threshold `√(e_{n₀}+1/n₀)`; eventually that threshold is below η and there is a crossing. The SC verification below applies. Thus S passes. Its statement alone permits `√log K` loss; the additional quantitative seed and SC eliminate that loss in I54. This does not retroactively turn I52's stated gap report into an additive proof.

## 2. Audit of SC: no remaining use of zero exponents

Assume the SC data from I54: `K_j→∞`, dyadic `n₀<N`, `ε=e_N>0`,

`n₀→∞`, `ε→0`, `εn₀→∞`,

and, for every **fixed integer m**, `e_{2^m n₀}=o(ε)` and `e_{2^m N}=O_m(ε)`. Constants here may depend on m. The source's `scale:long-deficit` is no longer asserted. Its sole necessary role was providing existence of the original crossing. None of the operations below requires it.

### 2.1 Local mass, topology, floors and shifts

On the source's compact array space X, use the exact floor arrays `g_n(s,t)=g(⌊ns⌋,⌊nt⌋)/n`, the affine stratum A, and `U=X\A`. Put

`μ_j=ε⁻¹Σ_{n₀≤n<N, dyadic}Law(g_n)`, `ν_j=ε⁻¹Law(g_N)`, `ξ_j=ε⁻¹Law(g_{n₀})`.

These are not probability measures of bounded total mass. Treating them as such would invalidate SC. For a fixed dyadic-endpoint interval I of power-of-two length p, define the source tests h, J and V. Eventually all its endpoints and half-endpoints align at every scale n≥n₀, including negative endpoints. Stationarity then gives exactly

`E h(I)(g_n)=e_{pn}`, `E J(I)(g_n)=e_{pn}−e_{pn/2}`,

`Σ_n E J(I)(g_n)=e_{pN/2}−e_{pn₀/2}`.

Let `b_q=E(1−g(0,q)/q)²`. The elementary second-moment calculation in `scale:local-mass` gives

`(1/4)Σ_n E V(I)(g_n) ≤ b_{pn₀/2}+2e_{pN/2}`, `0≤b_q≤e_q`.

After division by ε both sums are bounded. At one scale, the expectation of `h+J+V` is bounded by `2e_{pn}+2e_{pn/2}`; dyadic monotonicity bounds these by terminal shifted deficits. At the initial scale they are o(ε). This explicitly uses the negative m hypotheses when p/2<1. No uniform bound in p, and no arbitrary non-dyadic monotonicity, is invoked.

The finite-test cover of every compact subset of U now gives locally bounded mass for μ_j and ν_j and vanishing mass for ξ_j. The source's compact cutoffs and diagonal extraction yield locally finite vague limits μ,ν on U. Its proof applies verbatim with these estimates. There is no loss concealed by a weak probability-limit assertion.

The semimetric error `1/n` and four-point error `(log_M6)/n` tend uniformly to zero over all sampled n. Every fixed strict support violation is eventually absent from every sampled array, so unbounded total mass does not defeat the support argument. On the resulting `X₀`, all arrays extend continuously to real arguments with the source Lipschitz bound.

For any fixed dyadic translation r, `n₀r` is eventually integral and `⌊n(s+r)⌋=⌊ns⌋+nr`. This proves exact prelimit stationarity at that translation. There is no accumulation of floor errors over a possibly huge number of scales. Similarly `Sg_n=g_{2n}` is exact even before alignment. The properness argument `S⁻¹(A)=A` permits passage through vague convergence. Consequently

`S_*μ=μ+ν`, `μ=μ∞+Σ_{j≥1}(S⁻ʲ)_*ν`,

where the series is positive and dominated by μ, and μ∞ is locally finite, translation invariant and dilation invariant. Subtraction is performed on relatively compact sets, not between infinite total masses. Terminal normalization remains `∫h₁ dν_j=e_N/ε=1`; after cutoffs `∫h₁ dν≤1`. All these conclusions have been checked from the actual proofs of `scale:local-mass` through `scale:decomposition`.

### 2.2 Cancellation and fixed bridge observations

For each fixed dyadic forbidden triple of spacing t>0, the normalized cancellation bound is

`(C/ε)Σ_n exp(−γtn) ≤ (C_t/ε)exp(−γtn₀)→0`.

Indeed `ε⁻¹=o(n₀)`. Strict open tests, compact exhaustion of U, and the countable dyadic cover then exclude every real forbidden triple. This uses the accepted cancellation theorem with its fixed δ,γ and cutoff. Its local-scarcity proof makes its own fixed choices before M grows; I54 does not extract an unprinted effective modulus from that proof.

For a fixed bridge and endpoint tests, let `W=J(I)+V(I)≥0`, `H=h(I′)` and fix η>0. A safe realized-range observation bound is `(R,L,B)=(3,6,2)` for W and `(1,1,1)` for H: J has Lipschitz constant at most 2, V at most 4, and both are bounded by 1 on the realized range. Source extension of these functions from their realized range preserves fixed bounds. All indices of each observation lie in its endpoint window after choosing that window once. Both endpoint assignments are allowed by the source; negative orbit times present no restriction.

The individual-test bound and Markov give `sup_n P(H>η/2)=O_{I′,η}(ε)`. The bridge theorem, with its fast indicator retained, therefore bounds the weighted sum by

`C ε [∫W dμ_j + ε⁻¹Σ_n M^(−σrn)]→0`.

Here r>0, η, R,L,B and every window are fixed before j→∞. The geometric sum is at most `2M^(−σrn₀)`, and `ε⁻¹=o(n₀)` pays its normalization. The bridge's parameter and length cutoffs are eventually met. Neither the first-crossing threshold θ nor ε is used as a bridge observation threshold.

This gives `shape:exclusions`. The countable strict-test cover detects every nonaffine point in P and every nonunit point in Q; continuity then extends the inequalities to real arguments. The accepted shape classification and cross-loss argument exhaust the support: entirely slow arrays, one unit ray with a slow half-line, or two unit rays with a slow interval of strictly positive length. There is no missing zero-length slow interval, intermediate exterior speed, or residual affine array in this support. Domination and dilation transfer the exclusions to ν and every component of the positive decomposition.

### 2.3 Exact balance and all affine defects

Choose the source's fixed cap Φ, with `Φ(u)=αu` near zero, `Φ=1` for `u≥1−c_b`, `10C_*α<1`, and `c_Φu≤Φ(u)≤C_Φu`. Set

`G=Φ(h₂(0))−[Φ(h₁(0))+Φ(h₁(1))]/2`.

The source Taylor estimate gives `|G|≤C(J+V)`. In particular G is μ-integrable and the prelimit signed weighted measures have bounded total variation. Terminal normalization gives, after a subsequence,

`H_Φ=lim∫Φ(h₁)dν_j ∈ [c_Φ,C_Φ]`.

The initial capped integral is o(1), by the initial shifted-deficit estimate and the upper linear bound for Φ. Thus prelimit telescoping gives `∫Gdμ_j→H_Φ`. Vague convergence alone is insufficient to pass this total integral; the source's three affine-defect arguments are all needed and all still apply:

1. At affine speeds `0≤w≤c_b`, both cap derivatives vanish. On shrinking neighborhoods `|G|≤ρ(J+V)`, so finite weighted weak limits give zero signed mass there as ρ↓0.
2. At `c_b<w<1`, fix a sufficiently long dyadic bridge R once. Each affine array lies in a fixed open fast-bridge/shortfall event with some rational `0<η<1−w`. The weighted bridge estimate kills its J+V mass. The countable union covers all intermediate speeds. There is no uniform threshold as w↑1.
3. Near w=1, the cap is linear, so `G=αJ`. Fix a dyadic q∈(0,1). On the source neighborhood `U_q`, truncation gives `J≤qJ([1−q,1+q])+A/(2n)`. Its short-interval sum is `(e_{qN}−e_{qn₀})/ε≤1`. The total normalized additive error is `O((εn₀)⁻¹)→0`. Hence the weak limit satisfies `λ_J(U_q)≤q`. **First** take that same extracted weak limit for each fixed q; **then** let q↓0 through inverse powers of two. The atom at the unit-speed array is zero.

These arguments exhaust A and yield the exact identity `∫Gdμ=H_Φ>0`. The integer truncation length qn is eventually integral at all sampled scales. The error sum is geometric in 1/n; it is not multiplied by the number of scales. This is the only delicate normalized additive-error limit, and the supplied `εn₀→∞` pays it.

### 2.4 Strict terminal loss, zero terminal measure, invariant remainder

The positive decomposition and G-integrability imply

`Σ_{j≥1}∫|G(S⁻ʲd)|dν ≤ ∫|G|dμ <∞`.

Thus signed series rearrangements are justified. For `A_m=∫Φ(h_{2⁻ᵐ}(0))dν`, subdivision, stationarity and `∫h₁dν≤1` give `A_m≤C_Φ`. Translation invariance gives each series term `A_{j−1}−A_j`. Absolute convergence implies convergence of A_m. Fatou gives the upper bound

`terminal contribution ≤ H_Φ − Δ_ν`,

where `Δ_ν=∫liminf_m Φ(h_{2⁻ᵐ}(0))dν`.

If ν is nonzero, every supported shape has a slow interior. Its countable dyadic cover supplies a z with a positive-measure set on which `Φ(h_{2⁻ᵐ}(z))=1` eventually. Translation invariance transports this to z=0, so `0<Δ_ν≤C_Φ`. No probability normalization of ν is required; the finite integral bounds suffice. If ν=0, the entire terminal series is zero, still strictly smaller than `H_Φ≥c_Φ`. Loss of all terminal vague mass is therefore already covered, rather than excluded by assumption.

For μ∞, the entirely slow class has G=0. On either one-ray class, bounded interface locations belong to compact subsets of U: a fixed secant on one side has speed 1 and another on the other side has speed at most c_b. The interface pushforward is locally finite. Translation and dilation invariance force its mass on `[0,1)` to equal twice itself, hence zero.

On the two-ray band `1≤L<2`, the same fixed-secant argument gives finite endpoint intensity `I₀`, and dyadic translation invariance rules out endpoint atoms. Absolute G-integrability allows the source's sum over all disjoint dyadic length bands. The fine-scale integral is at least I₀; the cross-loss estimate and the cap's small linear slope bound the coarse integral by `2αC_*I₀`. Its contribution is at most `−(1−2αC_*)I₀≤−(4/5)I₀`. This includes I₀=0. Therefore `∫Gdμ∞≤0`.

Combining the strict terminal bound and this remainder bound contradicts `∫Gdμ=H_Φ`. This proves SC from its displayed assumptions and the accepted operations, without using `e_n→1` downstream. A hypothetical scalar sequence satisfying just doubling can amplify and does not contradict this conclusion: the stationary array laws and geometric bridge/cancellation inputs are indispensable.

## 3. Relative-seed quantifiers and H

For clarity, the general relative statement in I54 has the following quantifiers. Fix any prescribed dyadic seed function n₀(K)→∞ such that `u(K)=e_{n₀}(K)+1/n₀→0`. Then there are finite constants A and K₁, potentially depending on that prescribed seed, such that `d(K)≤A u(K)` for all K≥K₁. This does not assert a precomputed A simultaneous over every seed function.

If this fails, select `K_j→∞` with `d/u→∞`. Set `θ=√(du)`. Eventually `u<θ<d`, `u/θ→0`, `θ≤√u→0`, and

`θn₀ = √(d/u)·u n₀ ≥ √(d/u)→∞`.

The dyadic deficits converge to d, so the first crossing N exists. Its predecessor and doubling give `θ<ε=e_N≤Dθ+D/n₀=O(θ)→0`. For m≥0, iterated doubling gives

`e_{2^m n₀}≤D_m u=o(ε)`, `e_{2^m N}≤D_m(ε+1/N)=O_m(ε)`.

For each fixed negative m, dyadic monotonicity gives the same bounds directly from n₀ and N, and lengths are eventually integral. Also εn₀→∞. Thus SC applies and contradicts the supposed unbounded ratio. In particular, for every fixed positive shift eventually `2^m n₀<N`; a bounded ratio N/n₀ would already contradict the initial shifted estimate and `e_N=ε`. No independent upper bound on the number of selected scales is needed.

For the actual quantitative seed choose exactly I54's

`n₀=2^{⌊log₂(K^{1/4})⌋}`, `b=K^{1/8}`.

F yields an additive remainder at most `R_K=2K^(−5/8)ℓ+4K^(−1/4)→0`. Hence

`e_{n₀}≤[log(2+8/K)+R_K]/ℓ=O(1/ℓ)`, `1/n₀=o(1/ℓ)`.

Thus the general relative conclusion already implies `dℓ=O(1)`. The original proof instead sets `B=dℓ` and, on a hypothetical unbounded-B sequence, `θ=√B/ℓ`. Its explicit inequalities are correct:

`θ≤ℓ^(−1/2)→0`, `d/θ=√B→∞`, `(e_{n₀}+1/n₀)/θ=O(B^(−1/2))→0`,

`θn₀≥K^{1/4}√B/(2ℓ)→∞`.

Negating H indeed supplies such `K_j→∞`: choose both the proposed constant and the proposed cutoff tending to infinity. The difference between B and `log(K/2)−h` is the bounded quantity `log(2+8/K)`. At bounded parameter intervals, h≥0 also prevents spurious unbounded deficits. The ensuing crossing satisfies SC by the preceding argument. Therefore B is bounded eventually, proving H with absolute existential C,K₀ for the fixed sine family.

Only a strictly positive loss in the **one extracted system** is used. Asking for a uniform lower bound for Δ_ν across other possible limits would add an unnecessary requirement. The result is a big-O deduction with a quantitative seed and a noneffective contradiction; it supplies no explicit numerical C or K₀. Neither S nor G is an input to this closure.

For each fixed integer n_*≥1, the nonnegative cancellation losses satisfy the exact telescoping identity

`Σ_{j≥0} E L_{2^j n_*}/(2^{j+1}n_*)=a_{n_*}−h`.

Since `a_{n_*}≤a₁≤log(K/2)+4/K`, H gives `a_{n_*}−h≤C+4/K`, uniformly in n_*. This proves the claimed summable budget after H. It does not sum the unsummable `Cℓ e_n` term of the crude source estimate; no such summation appears in the original proof.

## 4. G: finite coarea with the actual tangent and Jacobian

Fix `c=49/50`. For B≥2, `E_B` is the closed set on which every inverse prefix of length l≤B has norm at least `M^{cl}`. Its dependence on **all** prefixes is essential. Constants below are absolute after one absolute parameter cutoff, uniform in B and the time origin.

### 4.1 Backward indices, row choice and varied Green identity

Let `\tilde q_a=q_{−1−a}`. The initial ordered pair is `(p,q)=(\tilde q₀,\tilde q₋₁)`. The backward recurrence is again `\tilde q_{a+1}=φ(\tilde q_a)−\tilde q_{a−1}`. With the coordinate-swap isometry J, its length-l transfer is `J T_{0,−l} J`. Thus its norm and singular-direction estimates are exactly those required by `bridge:graphs`; no assumption on forward prefixes is being silently added.

The B-step matrix has rows corresponding to `\tilde q_B` and `\tilde q_{B−1}`. At least one j∈{B−1,B} satisfies `|∂\tilde q_j/∂p|≥D_B/3`, `D_B=||T_{0,−B}||`. Choose the first eligible row. These are closed eligibility conditions; the selected pieces are Borel. Both are rows of the **B-step matrix**, including j=B−1. Its kernel is not asserted to be an exact singular line: row norm at least D_B/3 and row value on the contracted unit input at most D_B⁻¹ imply an angular discrepancy `O(D_B⁻²)`.

The selected level `\tilde q_j=constant` is a graph `p=P(q)` through the point. Put `U_a=d\tilde q_a/dq`; the correct boundaries are `U₋₁=1`, `U_j=0`. The source's extended graph estimate gives `|U_a|≤C M^(−4(a+1)/5)` for `0≤a<j` on the whole graph arc. This is not restricted to eligible points of that arc.

At each varied point the j×j Dirichlet matrix D has diagonal `v(\tilde q_a)` and adjacent entries −1. Its invertibility on the entire arc follows from the source's varied boundary problem. The same Wronskian calculation gives `D⁻¹_{ab}=t_min(a,b) U_max(a,b)`, with t₀=1; in particular `D⁻¹_{0a}=U_a`. The source explicitly proves the varied version in its distortion argument. Freezing the inverse at the original point would be insufficient, and is not what I54 does.

Differentiate `U_{a+1}=v(\tilde q_a)U_a−U_{a−1}` once more. Writing `W_a=d²\tilde q_a/dq²` gives

`v_a W_a−W_{a−1}−W_{a+1}=−φ″(\tilde q_a)U_a²`, `W₋₁=W_j=0`.

Since `P″=W₀`, this proves exactly

`P″=−Σ_{a=0}^{j−1}φ″(\tilde q_a)U_a³`.

The sign is negative, the factor is cubic, and the sum ends at j−1 in both row choices. For j=1 this reduces to `P″=−φ″(P)/(φ′(P))³`, a useful boundary check. With `|φ″|≤CM`,

`|P″|≤CMΣ_{a≥0}M^(−12(a+1)/5)≤CM^(−7/5)`.

This estimate holds on the full extended regular arc. Its exponent and domain are exactly those claimed; no weakening or repair is needed.

### 4.2 Eligible labels, area, covering and sublevels

Fix a source grid square of side 1/32 and one j. The backward graph extends a q-distance 1/4 from its eligible starting point; therefore it covers the square's q-interval with a uniform margin. Label it by its p-intercept t at a fixed q_c in that interval and write `p=Y(t,q)`. If two graphs meet, they have the same lifted endpoint value and coincide locally because its p-derivative is nonzero. Open/closed continuation over their common interval makes them the same graph, hence the same label. No count depending on B of different orbit itineraries is needed.

The closed set of eligible points in the square is compact; continuous dependence makes its label image compact. Labels stay in a bounded interval, because `|Y_q|≤CM^(−4/5)` and all starting points lie in the fixed square. In fact their range has length at most the square width plus a small absolute displacement.

If Q denotes the fixed lifted backward endpoint coordinate, implicit differentiation gives

`Y_t(t,q)=Q_p(t,q_c)/Q_p(Y(t,q),q)`.

Both numerator and denominator lie on the same extended graph. The source's determinant distortion makes their absolute ratio bounded above and below uniformly. This is the **area Jacobian** of `(t,q)↦(q,Y(t,q))`; graph arclength alone would not suffice.

The eligible label set need not contain an interval. Each compact regular graph arc has a local smooth continuation for nearby intercepts by the implicit function theorem and finite overlapping charts. These continuations agree with every nearby eligible graph by uniqueness. Countably many such charts can be partitioned into disjoint Borel pieces; ordinary change of variables applies on their measurable subsets. Injectivity prevents accumulation of image multiplicities in this partition. Projection of the fixed bounded lift to the torus has bounded multiplicity. These are explicit operations in the final chart argument of `bridge:theorem`, applicable to this one backward family without assuming two-sided eligibility.

For a fixed label, let `f_t(q)=v(q)−Y_q(t,q)`. If `0<s≤K/4` and `|f_t(q)|<s`, then `|cos(2πq)|≤1/2` for all sufficiently large K, since `|Y_q|≤1`. On each of the two resulting fixed circle arcs, `|v′|≥π√3K` with fixed sign. The new curvature bound gives `f_t′=v′−Y_{qq}` the same sign and magnitude at least K there. Each connected arc segment in the chart contributes length at most `2s/K`. Intersections with a fixed lifted grid interval have an absolute bounded number of components, including circle-boundary charts. Curvature is available on the entire required segment, so gaps in eligibility do not break monotonicity.

Integrate this length bound over the bounded label set with the bounded area Jacobian. Sum over the fixed finite grid and the two row choices. Taking the first eligible row only decreases that sum. This proves

`m(E_B∩{|v−r_B|<s})≤C min(1,s/K)`

for `r_B=Y_q`. For s>K/4 the trivial mass bound covers the rest after enlarging C. Neither chart number, overlap multiplicity, label length, nor distortion depends on B or K. Small graph slope alone would not prove this result; the new curvature identity is doing necessary work.

## 5. Infinite history, tails, mass budget and lift support

### 5.1 Correct direction and metric in the limit

On E∞, apply the direction-step bound to the swapped backward products. Summing the angular increments beyond B gives

`Σ_{l≥B} M/(D_lD_{l+1}) ≤ C M^(1−c−2cB)`.

Adding the row-kernel discrepancy `O(D_B⁻²)≤O(M^(−2cB))` fits within the same stated bound since 1−c>0. The contracted lines are almost vertical in the swapped `(p,q)` order and almost horizontal in `(q,p)`. All selected slopes and the limiting slope belong to one uniformly bounded horizontal chart. The identity

`|sin angle((1,r),(1,s))|=|r−s|/[√(1+r²)√(1+s²)]`

then converts angular error to slope error with an absolute constant. This proves the exact exponent in I54, uniformly over its row selection.

At an Oseledets-regular point in E∞, inverse-product norm growth has limit at least cℓ>0. The limiting input contracting line for inverse evolution is the forward unstable line. Equivalently, the uniform prefix contraction estimate from the source passes to that limit, and Oseledets identifies its negative backward exponent. Thus the limiting line is not the forward stable line or an endpoint output direction. The excluded nonregular base set has zero area.

For fixed K and **fixed s>0**, with `δ_B=CM^(1−c−2cB)`,

`{|v−rᵘ|<s}∩E∞ ⊂ {|v−r_B|<s+δ_B}∩E∞`.

Apply the finite estimate, enlarge E∞ to E_B, and send B→∞. This gives the infinite estimate with the same absolute C; then s↓0 gives zero resonance mass. The finite restricted graph measures converge weakly to the unstable graph measure over E∞ because `m(E_B\E∞)→0` and convergence of slopes on E∞ is uniform. The sets E_B and E∞ themselves are not asserted invariant.

With `X=log⁺(K/|v−r|)`, the restricted sublevel estimate gives `m(X>t)≤Ce^(−t)`. Consequently

`∫_{X>T}X ≤ T m(X>T)+∫_T^∞m(X>t)dt ≤ C(T+1)e^(−T)`.

The boundary term is required and is present. This proves uniform integrability for all B,K in range. At each fixed K, truncation and weak convergence yield convergence of these logarithmic integrals; it does not claim convergence of a K-dependent unbounded function under arbitrary moving-K weak limits. The separate slope logarithm is at most `CM^(−8/5)` on these sets.

### 5.2 All-scale shortfall counting

Fix K and a finite L≥2. For N≥L choose a norm-realizing input vector u for `T_{0,N}` and define `z_i=log_M||T_{0,i}u||`, `0≤i≤N`. Its increments are at most 1 and its total shortfall is exactly `N−g(0,N)`. The counting inequality is pointwise for any maximizing choice; no problematic measurable choice is needed to integrate its resulting bound.

If `F^i z∉E_L`, `L≤i≤N`, some l≤L satisfies `||T_{i,i−l}||<M^{cl}`. By determinant one this norm equals `||T_{i−l,i}||`. The followed vector obeys

`z_i−z_{i−l} ≤ log_M||T_{i−l,i}|| < cl`.

This is the required direction: a small operator norm forces a small growth ratio for this vector. The reverse implication is neither used nor true. Also i−l≥0, so every witnessing interval is inside `[0,N]`. The shortfall lemma therefore bounds the number of bad endpoints by `4[N−g(0,N)]/(1−c)`.

Stationarity gives

`(N−L+1)m(E_Lᶜ) ≤ 4N e_N/(1−c)`.

First take N→∞ at fixed K,L, using `e_N→d`; then L→∞, using the decreasing E_L. This proves

`m(E∞ᶜ)≤min(1,200d)`.

Only ending intervals are counted, so an extra factor for forward intervals is not needed. The source's two-sided middle-time argument is a different application on a fast bridge and is not silently required here. No positive-time waiting distribution or recurrence independence follows from this calculation.

### 5.3 Entropy-realizing lift and the stated payoff

On the positive-exponent Oseledets set, any invariant projective probability projecting to area is supported on the stable and unstable graph sections. One precise justification of the recurrence argument is to use their measurable moving coordinates: for a line off both sections, the ratio of its stable to unstable coefficient tends to zero forward and to infinity backward. Restrict to countably many positive-exponent and bounded-coordinate regions and apply recurrence; an invariant probability cannot give mass to such escaping fiber ratios. This is an invariant-measure statement, not a claim that E∞ is invariant.

The stable and unstable sections have time-averaged increments −λ and +λ. On the zero-exponent set every time-averaged increment is zero. An invariant lift attaining `∫g=h=∫λ dm` must therefore assign zero stable mass where λ>0: its deficit from the top integral is `2∫λ·(stable weight)dm≥0`. Equality forces this integrand to vanish. Hence its restriction over E∞ is indeed the unstable graph lift modulo null sets.

The restricted numerator logarithm is bounded below by `log K−X`, and the denominator is uniformly small there. On E∞ᶜ the continuous full increment satisfies g≥−ℓ. Thus, with `α=m(E∞ᶜ)`,

`h≥(1−α)log K−C−αℓ`.

Before H, the estimate α≤200d only creates a non-closing feedback inequality; S gives α=o(1). After the independent H proof, d=O(1/ℓ) and α=O(1/ℓ). This is the original logical ordering. G supplies neither full invariant small-ball control on the exceptional set nor renewal tails, and neither is certified here.

The optional full-lift criterion in I54 is also correctly scoped. With no vertical atom and a full small-ball bound `A(s/K)^β`, invariance gives a slope tail `A(KR)^−β`. Layer cake bounds the numerator deficit by A/β. For `0<β≤1`, integrating `R/(1+R²)` against that tail gives `O_β(AK^−β)`; at β=1 the integral is bounded without a logarithmic loss. This would imply H, but its full-measure hypothesis has not been proved by G.

## 6. Adversarial checks and contribution boundary

The independent [diagnostics.py](../experiments/i57_standard_map_additive_entropy_r2/diagnostics.py) uses exact rational arithmetic. It compares two independent curvature computations: differentiation by endpoint shooting, and the cubic Green formula. It covers j=1 and both B-step row choices, signed recurrence coefficients, the coordinate-swap identity, and singular/wrong-sign/wrong-power negative controls. Exhaustive shortfall paths include negative increments and both endpoint orientations. Exact floor checks include negative and initially unaligned dyadic arguments. Separate exponent checks retain the original seed and curvature exponents.

The diagnostics retain an arbitrary periodic trace-zero cocycle whose long good runs cancel, and scalar deficit sequences satisfying doubling that amplify. These demonstrate why elementary rare-visit/doubling reasoning alone is inadequate; neither is claimed a standard-map counterexample or a realization of all source hypotheses. The known actual fixed points with v=0 remain zero-area obstructions to universal pointwise expansion. A resonant noninvariant lift with `r=v(q)` still refutes inference of conditional regularity from the base marginal. None refutes the scoped H or G.

The finite output passes **79,968 exact assertions** and five explicitly synthetic rational deficit rows. There are no new floating standard-map trajectories. These computations test algebra and bookkeeping, not the universal analytic claims.

**Contribution flag for the later reviewer:** H's entire non-elementary contradiction mechanism is already in the accepted source operations. I54's additional closure is the elementary growing finite-time seed and relative-crossing quantifier argument. No new quantitative bridge theorem or uniform terminal-loss estimate is proved. G adds a second differentiation of the source's varied Dirichlet problem and applies ordinary coarea and shortfall counting. This analytic PASS must not be presented as a SUBSTANTIAL verdict. The separate contribution assessment remains necessary; absence of a printed additive theorem or a search duplicate does not settle it.

Current primary arXiv version pages were checked and frozen for [BXY](https://arxiv.org/abs/1701.07583), [Knill](https://arxiv.org/abs/math/9908014), and [Blumenthal](https://arxiv.org/abs/1710.09058), displaying v1, v2 and v1 respectively. Their actual archived passages confirm the previously retained scope limits: positive-noise lower bounds, a withdrawn lower proof/conjecture, and a fixed-parameter estimate deteriorating with time. They are not premises of this proof. This limited check does not claim a new literature search or worldwide priority. Existing broader I52/I54 literature records and failures remain sealed unchanged.

## 7. Evidence integrity and reproduction

Only the three authorized I57 paths were written. No shared/prior edits, staging, commits, publication, agents, or recursive archive copies were made. The exact task JSON and verbatim review brief, original reports/briefs/objections, source contracts, prior seals/verifiers, current four mutable ledgers, eleven direct pinned files, full proof passages, searches, HTTP version responses and this review are bound by [seal.json](../sources/i57_standard_map_additive_entropy_r2/seal.json). Prior archive bodies remain in place and are checked against their original seals. The full 13,223-entry/749-manuscript tree and 9,340-file ignored corpus are checked; searches use line **multisets**.

The unchanged I54 verifier replays **PASS**, including its 68 sealed artifacts, 170 unchanged I52 artifacts, 7,327 exact finite assertions and six PDF extractions. Four mutable-ledger differences are informational.

The direct unchanged I52 verifier is **not reported as PASS**: it stops at `AssertionError: search multiset prior-screens`. Its old query scans the growing `frontier/iterations` directory. The old 13-line multiset is preserved intact; the current query has 25 lines, with exactly 12 additions from the later original I54 report and no removals. The [failure record](../experiments/i57_standard_map_additive_entropy_r2/i52-direct-replay-failure.json) preserves the error and complete difference. No previous search snapshot or verifier was refreshed. The separate I52 diagnostic replay still matches its original 97,104 finite assertions. This historical-domain failure does not invalidate a sealed proof input, and the independent I57 verifier explicitly checks its explanation rather than suppressing it.

Run the read-only I57 check from the repository root:

```bash
python -B frontier/experiments/i57_standard_map_additive_entropy_r2/verify.py
```

It checks its own seal, frozen/live immutable inputs, original I52/I54 seals, pinned Git blobs, full corpus, passage hashes, search multisets, retained HTTP bodies/PDF extraction, the exact I52 search delta, and independent diagnostics. Verification output is provenance and finite-algebra evidence; the analytic verdict is the argument in this review. No formal proof certification is claimed.
