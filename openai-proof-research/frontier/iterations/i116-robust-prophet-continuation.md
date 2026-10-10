# I116 — Original-proof audit and robust prophet continuation

Date: 2026-10-10. Independent research review of the **original**, immutable I113 report, SHA-256 `47ad19c1a2989e6ff2038a5eeeb9039be5fbb4f7b913b9064c7448822c71b386`. All statements and lower operations of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises. Their truth is not audited. No children, shared edits, staging, commits or publication.

**Original verdict: PASS without repairs** for P113 (including B113), Q113, N113a/b, the explicitly scoped method obstructions, and G113. The original technical disposition is independently confirmed by the complete operation comparisons below. The new deductions in §§5–6 are author proofs, not independently reviewed theorems.

**Continuation verdict: R113 remains unproved and unrefuted. No substantial finding is nominated.** Route A derives exact posterior rates and cancellations, and exhibits a genuine two-sided instance obstructing a proposed *conditional* one-loss comparison. Route B proves a law-free local filter preserving `1/(2K)` of expected **offline** optimum, and develops sample-greedy calibration. It pays the unconditional rank budget, then identifies its dependence and double-thinning failures exactly. Neither route supplies the required implementable online selection inequality. No finding count is made here.

## 1. Audit scope and source provenance

The audit preceded repairs or use of the I113 partial as a premise. There were no repairs. `original-audit-verdicts.json` records the component verdicts. I read AGENTS.md, the pin, the relevant catalogue families and companions, current ledger status/overlap entries, the original supplied report, its actual implementation argument, and the full source operations used in this review. I do not claim a full semantic reading of the ledgers' unrelated research histories or of all corpus search hits. Current ledger snapshots preserve their context; historical counts in older entries do not override the assignment. I110/I112 working outputs are not bound or used; I109 is not resumed.

The exact inventory, URLs, Git blob positions, SHA-256 identities and reading ranges are machine-readable in the evidence directory. Source notation:

- **P:** `One-Sample-Suffices-for-Matroid-Prophet-Inequalities-against-an-Almighty-Adversary-September-23-2026/build/sections/`. Complete `setup`, `algorithm`, `safety`, `transfer`, `accounting`, `secretary` and introduction contracts. In particular I read the reverse-map, query filtration, heterogeneous transaction proof, full hybrid containment, both marked sequences, all-order rank inequality and telescoping proof through their endings.
- **S:** `Turn-Based-Stochastic-Mean-Payoff-Games-in-Deterministic-Quasipolynomial-Time-October-5-2026/build/build/sections/`. Complete `introduction`, `discount`, `labeling`, `application`, including the entire recursion and arbitrary-behavioral-opponent conclusion.
- **D:** `Deterministic-quasipolynomial-time-mean-payoff-games-September-25-2026/build/source/sections/07-values-and-strategies.tex`, complete, especially separate-player strategy restrictions. Its mean-value edge comparison warning is retained: equal gain at the endpoints alone does not identify an optimal edge.
- **U:** all five sections of `Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/build/source/sections/`. The full finite table, rounding, capped filter, shadow coupling, fallback, restart accounting and bit schedule have been compared. Its explicitly imported distinct-start K interface is accepted; no full reading of K's geometric proof is claimed.
- **MP:** complete arena, strategy, algorithm and complexity sections of `Mean-payoff-parity-games-in-quasipolynomial-time-October-5-2026`. The deterministic uniform prefix and bounded attraction operations are not stochastic equivalents.
- **I22:** §3 and the referenced Iwata–Fleischer–Fujishige (IFF) exact SFM operation, especially Theorems 3.4, 3.5 and 4.2 and its algorithm ending. I22 itself is checked here where used, rather than treated as another accepted-corpus theorem.

The inherited complete corpus domain has 13,223 tree entries, 749 manuscripts, and 10,373 original positions, comprising 9,340 I14 originals and 1,033 further originals; 776 representations are inherited PDF texts. The verifier replays every source-position binding. It also reproduces I113's exact ordered lexical matching-line multisets: scope 399 and robustness 199. These remain lexical evidence, not semantic coverage or an absence/priority certificate. No recursive corpus copy, whole-corpus download or PDF re-extraction was performed.

Current primary version pages for [ABHM](https://arxiv.org/abs/2609.19118), [FSZ](https://arxiv.org/abs/2507.09507), [Fu et al.](https://arxiv.org/abs/2406.12799) and [RWW](https://arxiv.org/abs/1911.07945) were fetched and frozen. The first three still display v1 in the observed pages; RWW's current page is recorded without silently replacing the inherited source versions. The actual full relevant ABHM §5 operation, FSZ spanning-chain/OCRS interface and Fu Appendix C were read from their inherited pinned-version texts, not search snippets. The inaccurate-prior comparison uses the full proofs of Dütting–Kesselheim Theorems 5.1 and 6.1 through the examples in the inherited [EC 2019 primary PDF](https://paulduetting.com/pubs/inaccurate-priors_EC19.pdf). Nothing in this bounded check establishes worldwide novelty.

The named connection is the single-sample matroid prophet problem and its order-oblivious connection to the matroid secretary conjecture, expressly discussed in P and FSZ. That is observed significance evidence, not an assertion that the robustness target has a particular community ranking. No verified matching MathDB page is supplied. R011 matching entropy, I29 common-base entropy and I77 weighted graph-switch results concern distinct entropy/covariance/mixing mechanisms; neither continuation splits those results.

## 2. Original P113/B113 audit, without repairs

Throughout this section `K=2^m`, `B=2^32 K^4`, `κ=2^100 K^8`, `t=2^-140 K^-12`, `s=t/K`, `η=2^-12`, `γ=η/(16K)`. The model is exactly that in I113: finite labelled oracle matroid, nonnegative finite observations, all `2n` variables independent, `K^-1 D_e≤Q_e≤K D_e` as measures, finite expected optimum, and every measurable full-data/full-seed ordering adversary. Arbitrary reals have a measurable-rule claim only; rational observations have the Turing claim.

### 2.1 Actual execution and posterior kernel — PASS without repairs

Both branches sacrifice **the same** `B0=H∪D∪C`. Consequently `p=P(e∈B0)=5/8+3t/8` is independent of the branch and lies in `[5/8,3/4]`. Put `W_e=S_e` on B0 and `V_e` otherwise. Arrival induction identifies the real execution with the fixed-vector execution for every `S,V,R,π`; ignored observations cannot invalidate an infimum over every order.

For `r_e=dQ_e/dD_e∈[1/K,K]` and `Z_e(w)=1-p+p r_e(w)`, the joint density of `(W_e,z_e)` against D is `P_0(z_e) r_e(w)^{1_{z_e≠0}}`. Products across labels and normalization yield I113 (A) exactly. Regular conditional versions exist on these standard Borel spaces, and exceptional coordinate null sets have zero joint probability. Branch, parity and T are independent of W. The branch really remains fair conditional on W.

For **fixed** w the two tilt factors are `1,r_e(w)`, whose ratio is at most K, not K². Restricting to any specified coordinate bits preserves this two-factor bound. Thus all original H, D, C and O bounds follow. Conditioning on H, then D, changes C rates: the proof uses the changed rates. It does not claim posterior mutual independence of H,D,C. Independence is across labels and, conditional on H,D,W, among the remaining C coordinates. This distinction also permits conditioning on the random H-defined group: after W,H are fixed, its label set is fixed, so outside-group exposures do not tilt focal coordinates.

### 2.2 Candidate mass — PASS without repairs

`Y=I*(W)\H` is independent and contained in U deterministically. For fixed W, `P(H_e=0)≥1/(2K)` gives `E u(Y)≥Wopt/(2K)`. The higher-priority span test depends only on other H bits. Conditional on them, the ratio of candidate mass at e to greedy-on-H mass is `(1-q_e)/q_e≤2K`. Summing proves I113 (B). No conditioning on an optimum depending on H is used: I* is fixed before H under this conditional experiment.

### 2.3 Adaptive reverse transcripts and B113 — PASS without repairs

After W,H,D are fixed, each density map and listed group is deterministic. P `eq:departing-query` queries only `G_j∩(S_j\N_j)` after N_j is known from earlier groups. Queries inside a batch have fixed label order. Domains shrink, so no guard is queried twice. Each complete transcript is a cylinder specifying only its queried coordinates, including its predictable labels; the unqueried C coordinates retain their **original conditional**, possibly heterogeneous, rates `c_e`.

Using fresh common uniforms on the entire fixed label set couples all transition laws with these same coordinate rates. The map is increasing in state, auxiliary time and bits. Therefore conditional exit hazards are nondecreasing in reverse time up to exit. There is no equality-of-rates hypothesis in the coupling.

The source `lem:transactions` explicitly permits arbitrary independent Bernoulli rates. Its positive certificates use only positives newly queried in a transaction, while the incoming state is frozen, not recomputed after erasing earlier positives. The argument thus applies to the exact transcript above. The original dyadic sum is `2^-11(14 ln 2+1)<1/2`; finitely many zero-hazard exits have probability zero. Every nonloop exits because the terminal nominal flat is the loop flat. This gives the squared exit mass `≥η/2`.

At one endpoint condition on the **complete ordinary-step transcript**, but on no T bits. Its fixed hybrid partition retains unqueried C at rates c_e and replaces departing coordinates by independent T at rate `s≤c_e`. Hence the hybrid vector is coordinatewise dominated by a fresh C vector. An exit is a decreasing event, so its conditional probability is at least the pre-step hazard. Tower conditioning gives joint ordinary/hybrid exit mass at least `1_present p_b²`. P `eq:hybrid-containment` is a deterministic inclusion for every completed assignment, including future guards in `F_{h-1}(b-2)`; it does not condition on those guards. Its proof is unchanged by the probability inequality.

The same T_e may occur in analyses of many endpoints. This is legitimate: these are separate comparison experiments, not successive revelations added to the reverse filtration. Sum by linearity; ordinary births of a fixed label are disjoint. Likewise the later focal-T thinning conditions on other groups' tests only. Neither step needs independence between different hybrids or different λ_i.

Baseline births cost at most `r(Q_h(L))≤|D_h|/κ`; no birth at `a_h+1` is possible. Fair parity and `P(D_e=1|W,H)≥1/(4K)` give `Eσ_i≥γ|Y_i|-n_i/κ`, including unlisted groups where both sample count and statistic vanish. This verifies B113 and (C)–(D) in the original form.

### 2.4 Residual family and union bound — PASS without repairs

For each birth layer choose an unsacrificed rank basis Z_b over `X_h(b-2)∪K_{h,b}`. Density comparison with its extension charges each safely sampled label outside the residual by κ rank, giving `σ_h≤κz_h+|R_h|` and `R_h⊆O` pointwise. This uses the largest density maximizer and not a random independence assumption.

Fix W,H, parity and all focal-complement D,C,T bits, **without** fixing focal listing. If listed, the focal index h is already one plus the number of listed lower groups. Its incoming path and all lower competition sets are fixed. Focal C does not enter X_h, and focal T does not enter z_h. Focal D can change the nominal path, but the common-generator bound encodes every such path by at most `q=⌊n_i/κ⌋` generators. On the low-rank branch there are at most q witness labels. The first source marked sequence records valid birth/parity; the second, including lower competitors before witnesses and postponed generators, records exclusion from the enlarged preceding flat. Their intersection is exactly R_h. This is the actual two-sequence construction, including its endpoint induction and the old terminal block spanning E.

The source's insertion count already includes positions, orders and marks. Thus

`|Rfamily|≤S_q(n)^2 [4^(2q)S_(2q)(n)]²`,

with no extra time/permutation factor. Its logarithm is at most `(n/κ)(6 ln κ+6+4 ln 2)≤1000 n ln κ/κ`. The source floor estimate applies at `1/κ,2/κ`; `2⌊n/κ⌋≤⌊2n/κ⌋` handles the second floor.

Conditional focal O bits remain independent and have failure probability at least `1/(2K)`. For any *fixed* member R, `P(R⊆O)≤exp(-|R|/(2K))`. For `δ=2^-28 K^-3`, the original inequalities

`1000 ln κ/κ≤δ/(4K)`, `δκ/(4K)≥ln(1/δ)`

hold for every m≥0 using `100+8m≤108·2^m` and `108000<2^70`. The union bound yields probability ≤δ for any residual larger than δn at every n≥κ. Therefore `Ee_i≤2δn_i`; the high-rank and unlisted cases give the same pointwise `σ_i≤κz_i+e_i`. This is a uniform family argument, not independence of the selected residual. It proves the original (E)–(H).

### 2.5 Final paths, minimum over orders and constants — PASS without repairs

P's common generator set `J=C_h∪⋃_{j>h}(C_j∪J_j)` accounts for all times. Its rank difference telescopes along the chosen parity. The incoming sets satisfy `X_h(b-2)⊆A⊆A+S'⊆X_h(b)`, exactly the source hypotheses. Costs are bounded before expectation by all true-group counts, avoiding listing bias. Conditional W,H,C,D, parity and nonfocal T, a fixed rank witness can be intersected with independent focal T, so `Eλ_i≥s E(z_i-c_i)`. Posterior C costs are at most Kt; D counts are trivially at most group size. This gives (I).

For fixed weights and every complete seed, layerwise greedy spans its eligible set. Contracting all lower tested competitors only lowers the rank bound. Hence the source inequality `N_≥i(π)≥λ_i` holds for **every** π, and cumulative geometric weights give `min_π u(A_main)≥½Σ_i B^i λ_i`. All expectation-taking occurs after that pointwise minimum. Full-seed order and unused-data dependence cause no additional conditioning.

The total coefficient is

`ε=1/κ+2δ+Ktκ+(1+Ktκ)/(B-1)≤2^-25 K^-3≤γ/(16K²)`.

In the main case `m*≤Wopt/(8Kκ)`, the small-group loss `<2κm*` and candidate estimates give analyzed Y mass at least Wopt/(4K) in expectation and U mass at most 2K Wopt. Thus the bracket is at least `γ Wopt/(8K)` and main reward at least `sγ Wopt/(16Kκ)`.

In the maximum case, the posterior sacrifices of the highest and second-highest positive nonloops are independent across labels. The event top unobserved/second observed has probability at least `p(1-p)/K²≥1/(8K²)` and selects the top for every order. A single nonloop succeeds with probability at least `1/(4K)`. Thus maximum reward is greater than `Wopt/(64K³κ)`. The fair common-sacrifice branch mixture gives the common target `sγWopt/(32Kκ)`; the required comparison is `4K²sγ≤1`.

Rounding costs B. Consequently the conditional guarantee is exactly `2^-293 K^-27 OPT(W)`: the K exponents are `13+1+1+8+4=27`, and powers of two are `140+16+5+100+32=293`. Finally the coordinate mixture law of W is `(1-p)D+pQ`. Retaining each label of an optimum of an independent V vector with probability 1-p gives `EOPT(W)≥(1-p)EOPT(V)≥EOPT(V)/4`; no product change of measure occurs. This proves the original `2^-295 K^-27` constant.

For a nonloop, `EV_e≤EOPT(V)` and `ES_e≤K EV_e`; finite many nonloops give integrability. Loops need no moments. Zero optimum, empty matroid and ties are covered by the deterministic rules. Replacing K by its next dyadic value costs at most 2^27 and increases the bit parameter by a constant.

### 2.6 Exact implementation and complexity — PASS without repairs

For a flat P0, `(n+1)[κ r(P0∪A)-|D_h∩(P0∪A)|]-|P0∪A|` is integer submodular on `E\P0`. Primary changes of size at least one outweigh all cardinality changes. A nonclosed minimizer can be enlarged without increasing rank and with strictly improved objective. Primary minimizers are closed under union; the cardinality perturbation therefore returns the **unique largest** primary minimizer, not an arbitrary flat with the same rank. Subtracting its value at ∅ supplies a normalized SFM oracle if needed. This checks I22 §3 in full at the variable κ required here.

Here is a concrete worst-case accounting, with no hidden numerical-K loop. There are at most `n(3n+3)` nontrivial density calls on times `[-3ℓ-2,0]`; disabled calls are identities. Each function evaluation has `O(log(n+2)+m)` output bits and needs one rank-oracle query (or at most n independence queries). IFF Theorem 4.2 gives `O(n^7 log(n+2))` value-oracle/arithmetic operations per SFM call in its oracle arithmetic model, with polynomial-size arithmetic. Thus a conservative bound is `O(n^9 log(n+2))` rank queries, or `O(n^10 log(n+2))` independence queries, plus lower-order closures and scans. This is not a claim that these are optimal or exact leading constants.

For bit complexity let `T_SFM(n,b)` denote the deterministic bit cost of that specified SFM implementation with b-bit integer function values, including exact arithmetic but charging its value-oracle call separately. The exact compositional upper bound is

`n(3n+3)[T_SFM(n,b)+O(n^7 log(n+2))·poly(n,b)] + poly(n,L_obs+m)`,

where `b=O(log(n+2)+m)` and `T_SFM(n,b)=poly(n,b)` by the strongly polynomial SFM bit guarantee. This explicitly keeps the arithmetic model separate from oracle counts; the original did not specify a machine encoding or leading polynomial degree, so attributing an exact integer bit count to it would be false. The asserted worst-case **polynomial** bit bound follows.

Masks use exactly `n(283+25m)+2` fair bits if all four masks, branch and parity are drawn: H one, D two, C `140+12m`, T `140+13m` bits per label. This includes unused branch coins. Rational rounding uses exponent division by `32+4m`; numerator/denominator shifts have size `O(L_obs+m)`. At most n occupied numerical levels are sorted, and numerical gaps do not generate path iterations. Paths as subsets use `O(n³)` storage bits. No residual family is enumerated and no likelihood is evaluated. Every tape terminates within the supplied-K polynomial bound.

The optional unknown-K geometric mixture also passes **at its stated scope**: the dyadic branch K0 alone has mass `1/(2K0)`, so its ratio is `2^-296 K0^-28`; feasibility holds in other branches. Geometric j gives polynomial expected work, not a worst-case or every-infinite-tape termination guarantee.

## 3. Other original components and exact contribution comparison

**Q113 — PASS without repairs.** Conditional retention probability `h_e(S_e)/K`, where `h=dD/dQ≤K`, gives retained subprobability `D_e/K` and independent membership probability 1/K. Conditioning on the entire membership vector leaves retained samples with product D law and independent actual V. The P seed is fresh and independent; rejection uniforms and rejected data may be known to the order adversary because its reward is pointwise at least the minimum over retained orders. The fixed optimum's retained subset proves `EOPT_(M|J)(V)≥EOPT_M(V)/K`. The constant `2^-293/K` uses the stronger proved P constant, not its looser displayed theorem. Arbitrary exact likelihood arithmetic and exact sampling probabilities are extra assumptions; no polynomial or law-free implementation is inferred.

**N113a — PASS without repairs.** With Q all zero and positive online probability 1/2 before cutoff h, `Q≤2D` holds coordinatewise including the zero atom. Every prefix through j has the same law for all h≥j, so the full-instance probability p_j of selecting its positive value is the same. `Σp_j≤1` even if zero values can be accepted. Summing the normalized prefix rewards gives `nc/2≤2`, hence some ratio ≤4/n. Replacing 1/2 by ε gives TV≤ε and ratio ≤2/(εn). The omitted reverse domination fails at the positive atom.

**N113b — PASS without repairs.** Common Q has masses 1/2 at 0,a_j, while D is the indicated deterministic cutoff vector. Thus `D≤2Q`. The entire sample law and relevant online prefixes are identical across cutoffs, now yielding `nc≤2`. The omitted Q≤KD fails where D has zero mass. Neither example satisfies the two-sided model; neither refutes R113.

**Method and concentration obstructions — PASS without repairs, scoped as originally stated.** The same Q and two different admissible D laws cannot be converted by one S-only kernel into both `D^+/K` and `D^-/K`. This blocks exact sample-only rejection calibration, not all algorithms using arrivals. For Bernoulli sample probabilities 1/3 versus online 1/2, K=3/2 is valid on both atoms, and the all-one sample event has likelihood `(2/3)^n`; the whole-vector likelihood black box really pays K^-n. It is not a lower bound for optimal welfare. The n=1 rare positive example blocks high-probability reward relative to **expected** optimum, not a realized-OPT theorem. All of these qualifications are essential.

**Technical disposition — confirmed independently.** This conclusion is not derived from missing titles. P113's complete lower-operation chain is: coordinate Bayes mixture → heterogeneous predictable certificates (`P:lem:transactions`) → dominated product transition on the same deterministic hybrid (`eq:hybrid-containment`) → whole-path generators and two pivot encodings (`lem:generators`, `lem:pattern-family`) → residual union bound → the same common-generator rank telescope and orderwise count (`lem:rank-cost`, `lem:all-orders`) → exact SFM implementation. Every changed probabilistic parameter and numerical budget was checked in §2. No new feasibility decomposition, hybrid containment, encoding or rank estimate remains as an additional mechanism. Q113 is exact rejection plus restriction; N113 is the full prefix-indistinguishability calculation. These are technical deductions under the unusually strong stipulated lower-operation premise.

The comparison with stronger relevant companions is at the operational level:

- ABHM's §5 stored-basis refresh is pathwise feasible. Its distributional invariant fixes the arrival prefix before orienting the independent sample/value pairs fairly. A full-seed/data-selected prefix need not preserve that distribution. Under misspecification the orientation conditional on endpoints x,y has probability `r(x)/(r(x)+r(y))`, not 1/2. Neither replacement is provided by its full proof. Its O(n²) query guarantee therefore does not subsume R113 or the almighty interface of P113.
- FSZ Theorem 2.5 needs a balanced spanning-chain distribution for a **product** active set with scaled vector in the matroid polytope. Its construction learns the chain with rank-dependent samples, and its prophet reduction uses additional logarithmically many samples. Fu Appendix C's bound `c≤1/M+M^((s+1)M)/N` concerns balanced CRS, even offline; it is not a welfare lower bound under one independent sample.
- Dütting–Kesselheim's complete threshold-policy proof propagates additive Kolmogorov error through a fixed online recursion; its arbitrary-policy TV coupling uses a union event and bounded total payoff. The bounds depend on n and bounded-value normalization. These operations do not provide a dimension-independent multiplicative comparison of unknown Q samples to independent D arrivals under a clairvoyant order.
- U's full schedule has activation `2^{T_P}-1` and additive charge `(2^{T_P}-2)diam+(2a+2)k diam`. Its shadow is evaluated on a deterministic filtered word. Neither this schedule nor its finite table supplies a polynomial startup charge, input-only per-request time, or adaptive-order guarantee. These are scoped missing interfaces, not impossibility theorems.
- MP's uniform prefix bound is for every deterministic consistent path; attraction terminates within |H| steps. S instead supplies expected pathwise-liminf guarantees. An almost-sure stochastic conjunction is not obtained by identifying those contracts. The old stochastic-parity comparison in I113 has a limsup-average objective and priority-dependent `d n^(2d) MeanGame` cost; no unconditional quasipolynomial liminf-conjunction result is inferred here.

## 4. G113 independent exact extraction audit — PASS without repairs

Use exactly S's explicit integer-reward/rational-chance model, including multiedges, zero probabilities and arbitrary behavioral opponents. Set `A0=n![Q(3+W)]^n`, `H=(W+4)A0`, `N=32H²`, `λ=1/N`. For a positional pair every determinant numerator and denominator has degree ≤n and coefficient ℓ1 norm ≤A0. Multiplying `D(1/N)` by N^n gives a common nonzero integer d with `|d|≤A0 N^n`; every discounted coordinate is an integer divided by **this same** d.

Consequently differences of outgoing expressions at a player vertex are integers divided by Nd. Every nonzero difference is at least `g=1/(A0 N^(n+1))`. This is why no squared-denominator loss is needed. It is an edge-expression gap, not the source's gain-versus-zero gap.

Set `ε=g/8`, `Kbox=256(N+1)` and take the integer `Scale=8 Kbox A0 N^(n+1)`. The scaled map `F(t)=Scale f_λ(t/Scale)` satisfies precisely S's discounted translation identity. Its unchanged comparison vectors `floor(Scale v)-N1` and `ceil(Scale v)+N1` have gap ≤2(N+1); the full source box shrink retains both and returns A/Scale within ε. The proof never required Scale to equal the original 16HKbox. It required this gap and a box containing the comparison vectors; `J=Scale W+N+1` supplies the latter.

All logs of A0,H,N are O((L+2)²), while `log Scale=O((L+2)³)` is still polynomial. Thus d0 can be cubic here; the original G113 asserted polynomial, not quadratic, size. The full labeling tree is bounded by

`(Λ+1)(B0+1)(1+Λ(2048n+3))^B0`,

where `Λ=d0+B0` and `B0=O(log(n+1))`. This remains `2^O(log²(L+2))`. Each exact floor evaluation uses denominator QN and polynomial-bit numerators `Scale w+(N-1)t_j`; every recursive box remains inside the initial box. Mass-changing edges number O(log(n+1)) per path, and every operation has polynomial bit cost. No slow contraction iteration or strategy enumeration is hidden.

Choosing approximate extrema gives true outgoing value error ≤2ε<g. Hence the chosen edge attains the exact extremum at every owned vertex. Selecting all such edges simultaneously makes the true discounted vector the selected pair's linear fixed point; uniqueness holds by contraction. For **this** pair, every comparison polynomial has coefficient norm ≤H. S's lowest-nonzero-coefficient sign calculation applies uniformly to all pairs, so optimality at λ implies optimality on all `0<u≤1/(2H)`. A numerator zero at λ in this interval must be identically zero; exact ties cannot conceal a later sign change.

For gains compute the determinant polynomials of `Q(I-(1-u)P)` and its replacing columns `Qu r`. Evaluation at n+1 distinct integer points 0,...,n and exact interpolation has polynomial bit cost: matrix entries have polynomial size, determinant lengths are bounded by n times entry length plus log(n!), and interpolation denominators divide products of differences of these n+1 points. Invertibility at interpolation points is not needed to compute a determinant. If ℓ is the least nonzero degree of D, boundedness near zero forces every N_i to vanish to order at least ℓ. The reduced ratio `[u^ℓ]N_i/[u^ℓ]D` is the exact gain.

S's gain/bias and martingale operations already identify it with the expected **pathwise liminf** value and give one pair optimal at every start against all behavioral opponents. G113 neither replaces that convention nor promises almost-sure equality to a scalar start value, finite-time convergence rates, or stochastic parity.

This is a complete full-scope technical reduction: universal-scale labeling + common-denominator edge gaps + source sign stability + determinant coefficient extraction. D's separate-player self-reduction independently confirms that exact strategy output is an algorithmic-output extension of the available decision operations; the sharper Blackwell part here is supplied specifically by S's all-pairs sign calculation. No contribution claim rests on the absence of an “exact strategies” title.

## 5. Continuation Route A: posterior comparison with one mismatch charge

R113 asks for a universal absolute c>0 with expected reward at least `(c/K)EOPT_D`, all original independence and full-seed order assumptions, a rank-oracle algorithm polynomial in n, rational observation bits and log K, and no distribution or likelihood access. The following identities are analysis tools; evaluating r is never proposed as an implementation.

### A116. Exact conditional rates and moment cancellation

Hypotheses: exactly P113's product masks and the two-sided model. Let `a=(1-1/4)(1-t)=3(1-t)/4`, so `p=1-a/2`. At one coordinate with likelihood r and normalization Z, direct summation of the eight posterior masses gives

`P(H=1|W)=r/(2Z)`,

`P(H=0|W)=[a+(1-a)r]/(2Z)`,

`P(D=1|H=0,W)=(r/4)/[a+(1-a)r]`,

`P(C=1|H=0,W)=tr/[a+(1-a)r]`,

`P(C=1|H=0,D=0,W)=tr/(1-t+tr)`.

For H=1 or D=1 the last guard rate is t. The exact candidate odds are `a/r+1-a`, and the exact unsacrificed probability is `(a/2)/Z`. These formulas prove the original bounds and identify where simultaneous worst-case substitutions can be wasteful.

There is an exact cancellation before any bound. If f(w,W_-e) is any nonnegative measurable function independent of the coordinate's masks after W is fixed, then

`E[f(W)1_{H_e=0,D_e=1}]=(1/8) E_{Q_e⊗M_-e} f`,

`E[f(W)1_{e∉B0}]=(1-p) E_{D_e⊗M_-e} f`,

where `M_j=(1-p)D_j+pQ_j`. Proof: multiply the respective posterior probabilities `(r/8)/Z` and `(1-p)/Z` by the marginal density Z dD and integrate; Fubini applies by nonnegativity. This remains valid for `f=w_e 1_{e∈I*(W)}`, since I* depends on W only. It does **not** remain an identity with the same product law after arbitrarily conditioning on a sample-dependent greedy path or the selected order.

This is the proposed reorganization: keep these measures until the aggregate safe-rank accounting rather than separately paying sample retention, candidate mass and measure comparison. The source deterministic layer and rank operations are available after conditioning, but the nonlinear generators/residual and later-path costs must then be charged in these varying measures. No identity above performs that charge.

### A116b. A fixed-vector c/K comparison already fails for the maximum rule

Hypotheses: rank one on two positive nonloops; fixed gluing vector `(W_1,W_2)=(1,ε)`, `0<ε<1`; an independent sacrificed mask with common prior probability `p∈[5/8,3/4]`; maximum-rule threshold and its pointwise minimum over orders. Take likelihoods `r_1(1)=K`, `r_2(ε)=1/K`. Their posterior sacrifice probabilities are

`q_1=pK/(1-p+pK)`, `q_2=(p/K)/(1-p+p/K)`.

A complete four-case enumeration gives exactly

`E[min_order reward|W]=(1-q_1)[q_2+(1-q_2)ε]`.

If both labels are unobserved, the adversary presents ε first; if only the top is unobserved it wins; if the top is observed nothing wins. In particular the expectation is at most `K^-2+ε/K` (using p≥1/2). Choose ε=K^-3. This is at most `2/K²`, and so no universal c/K bound relative to this conditional OPT(W)=1 holds for that rule.

This conditional configuration comes from an actual two-sided, mutually independent input: on label 1 put D mass `1/(K+1)` at 1 and `K/(K+1)` at 0, and reverse them for Q. On label 2 put D mass `K/(K+1)` at ε and `1/(K+1)` at 0, and reverse them for Q. All likelihoods are K or 1/K and the displayed W has positive probability. For these two labels the original enormous density charge produces no analyzed large group. Moreover, conditional on W every main-branch accepted label must belong to the independent test mask, so its expected reward is at most s(1+ε). The full fair mixture is therefore still O(K^-2) at this W. This obstructs strengthening the original conditional proof (J) to c/K for that same rule.

**Limit:** it is not a counterexample to unconditional R113. Other W configurations contribute reward, and the online optimum on these distributions is not the deterministic conditional benchmark 1. This distinction is exactly why the cancellation in A116 might still be useful.

### A116c. The uniform guard/test comparison has a quadratic rate spread

For candidate coordinates with H=D=0, the smallest and largest possible guard rates are

`c_-=t/[K(1-t)+t]`, `c_+=Kt/(1-t+Kt)`.

Hence

`c_+/c_-=K²(1-t+t/K)/(1-t+Kt)`.

If K≥1 and `Kt≤1/2`, then the last factor is at least 1/3, so the spread is ≥K²/3. Proof: numerator ≥1-t≥1/2 and denominator ≤1+Kt≤3/2. Both extreme likelihoods are realized by normalized two-point laws as above. Any argument that simultaneously controls **every** guard cost by c_+ and ensures hybrid domination by choosing one test rate at most c_- inherits this spread. This is a precise limitation of that pair of uniform estimates, not a lower bound on every choice of masks or every online policy.

**Unpaid inequality for Route A:** an aggregate payoff/rank comparison must charge heterogeneous safe samples and path changes directly in the mixed D/Q measures of A116, while allowing the K² conditional configurations of A116b/c. Replacing any one original K by a constant, or tuning κ,B,t,s while retaining the same extreme-rate bookkeeping, does not establish it. I have not proved that aggregate comparison. These identities and obstructions are technical Bayes/coupling deductions from the audited source construction, not a substantial target resolution.

## 6. Continuation Route B: law-free selection and calibration

This route uses observed comparisons instead of density values. It has two paid bridges and an explicit failed composition.

### L116. A local comparison preserves offline welfare at linear loss

**Theorem (author proof).** Let F be any finite nonempty downward-closed family of subsets of [n]. Let all S_e~Q_e,V_e~D_e be independent nonnegative finite random variables, with `Q_e≤K D_e`, K≥1, and `EOPT_F(V)<∞`. Define the observable-on-arrival candidate set `C={e:V_e≥S_e}`. Then

`E OPT_(F|C)(V) ≥ (1/(2K)) E OPT_F(V)`.

This uses only the **upper** domination; it is an offline benchmark theorem, so it does not contradict N113a.

**Proof.** Choose a maximum-value set I*(v) by a fixed ordering of feasible sets among ties. Holding v_-e fixed, `g_e(v)=v·1_{e∈I*(v,v_-e)}` is nonnegative and nondecreasing: the best feasible set containing e has objective v plus a constant, while the best excluding e has constant objective. The fixed tie rule changes the possible boundary inclusion only. If no feasible set contains e, g_e=0.

Let F_D be the right-continuous CDF of D_e and G its quantile function. From Q≤KD, for every v,

`F_Q(v)=1-Q((v,∞))≥max(0,1-K(1-F_D(v)))`.

Write `φ(u)=max(0,1-K(1-u))`. With U uniform on (0,1), G(U) has law D and `F_D(G(U))≥U`; this also handles atoms. The function h(u)=g_e(G(u)) is nondecreasing. The elementary association identity

`∫hφ-∫h∫φ = (1/2)∫∫(h(u)-h(v))(φ(u)-φ(v)) du dv ≥0`

holds first for bounded h and then by truncation. Since `∫_0^1 φ(u)du=1/(2K)`, independence of S_e yields

`E[g_e(V_e)1_{S_e≤V_e}|V_-e] = E[g_e(V_e)F_Q(V_e)|V_-e] ≥ E[g_e(V_e)|V_-e]/(2K)`.

Sum over e and average V_-e. The subset `I*(V)∩C` is feasible by downward closure and is a candidate for the left-hand optimum. This proves the claim, including ties and zero values. Nonnegative integration and finite expected optimum justify every step. ∎

**Information, complexity, sources and limits.** C requires one rational comparison per arrival, no densities, no new sample or hidden randomness. The optimum and conditional g_e are proof variables; no algorithm for arbitrary F is asserted. The proof is the displayed scalar quantile/association calculation plus deletion feasibility; its only matroid input when F is a matroid is downward closure. The finite diagnostics exhaust small discrete laws and feasible families, independently recomputing both optima. This is a useful paid linear-loss bridge, but it does not select its offline witness irrevocably. A constant online approximation to this retained optimum using the original information would imply c/K; that extra theorem is not assumed.

There is a concrete failed source substitution. For n=1, D=Q=Uniform[0,1], put `V'=V 1_{V≥S}`. Conditional on S=s, `P(V'>0|S=s)=1-s`. Thus the sample S is not an independent draw from the law of V'; it even has a different marginal, since `P(V'=0)=1/2`. The accepted exact-law theorem cannot simply be rerun on this censored online vector. Exchanging S and V to symmetrize would require future V to define the preprocessing sample. Full-seed concealment cannot fix that timing error.

### X116. Sample-greedy calibration pays an unconditional rank budget

Hypotheses: a finite matroid, independent S~product Q and V~product D, `D_e≤KQ_e`, and fixed label priority. Let B(w) be priority greedy on positive weights. Declare e a candidate exactly when V_e>0 and

`e∈B(S_-e,V_e)`.

This decision is computable at arrival from the stored samples, the current value and one greedy scan. Let `p_e=P(e is a candidate)` unconditionally, and let `q_e=P(e∈B(S))`.

**Claim.** `p_e≤K q_e` for each e, and consequently `Σ_{e∈A}p_e≤K r(A)` for every label set A. With both sides of the original domination, also `p_e≥q_e/K`.

**Proof.** Fix S_-e. The indicator of positive greedy membership is a measurable function of the single substituted value. Integrating the measure inequalities D≤KQ and D≥Q/K gives both bounds. Average over S_-e; substituting an independent Q_e draw recreates the entire product sample law. Each B(S) is independent, so its intersection with A has size at most r(A); sum and average. Thus p/K lies in the matroid independent-set polytope by its rank inequalities. ∎

This proof does not need a stochastic-order replacement. It uses the actual one-coordinate measure inequality only. The algorithm never computes p or q. Its n candidate tests use O(n²) independence queries and polynomial rational comparisons.

**Dependence obstruction, already at K=1.** On rank one with weights a_1<a_2<a_3, take independent S_j,V_j equal to a_j or 0 with probability 1/2 each. Then candidate indicators are

`C_1=1_{V_1=a_1,S_2=S_3=0}`, `C_2=1_{V_2=a_2,S_3=0}`, `C_3=1_{V_3=a_3}`.

Their probabilities are 1/8,1/4,1/2. But `P(C_1=C_2=1)=1/16`, whereas `P(C_1=1)P(C_2=1)=1/32`. Unconditional activations are not product. Conditional on S they are independent, but on the positive-probability event S=0 their conditional probabilities sum to 3/2, exceeding rank one. Thus neither the unconditional rank budget nor conditional independence supplies both hypotheses of the FSZ OCRS interface at once.

**Double-thinning obstruction within the full two-sided model.** On rank one with n strictly decreasing positive rational weights in [1,2], take each S_j positive with probability `q=1/(K+1)`, zero otherwise. Consider two alternative independent online laws with the same Q:

`D^dense_j(positive)=K/(K+1)`, `D^sparse_j(positive)=1/[K(K+1)]`.

For every coordinate and both atoms, each pair satisfies `K^-1D≤Q≤KD`: in the dense case the ratios are 1/K and K; in the sparse case the positive ratio is K and the zero ratio lies in [1/K,1]. For K=1 the two instances coincide.

For either online positive probability d, the candidate count has exact expectation

`Σ_j d(1-q)^(j-1)=(d/q)[1-(1-q)^n]`.

It tends to K for the dense instance and 1/K for the sparse instance. The initial sample law is identical in the two instances. If the proposed calibration then independently thins every candidate at rate 1/K, **any** feasible selection from those retained candidates has reward at most twice their count in expectation. For the sparse instance this is at most `2/K²`, for every n. Meanwhile `EOPT_D≥1-(1-d)^n`. For fixed K, take n sufficiently large that this is ≥1/2. The resulting ratio is at most `4/K²`. This is a universal analytic family, not a finite-search extrapolation.

For dyadic K the thinning has bounded fair-bit cost, so the failure has nothing to do with an unimplementable coin. The example refutes exactly the composition “sample-greedy candidates → uniform 1/K thinning → arbitrary selection”; it does not refute R113. In particular an unrestricted algorithm can accept a positive value and get a good reward on the sparse bounded-weight instance. It need not obey this candidate restriction.

**Unpaid comparison for Route B.** The local-filter optimum in L116 has the right welfare scale but no paid online feasibility argument. The exchange calibration in X116 controls unconditional congestion but loses the product/rank hypotheses needed by the source OCRS, and blanket thinning spends the desired factor twice on valid sparse laws. A new mechanism must use the observed samples and arrival values to allocate feasibility while charging **one aggregate K loss**; an assumed independent activation vector, fresh training sample, known conditional probabilities, or extra private seed would change the problem. No such mechanism is proved here.

All positive deductions in this route have elementary complete reductions to scalar measure comparison, monotone quantiles and matroid greedy membership. They are technical partials under the present premises, not multiple nominations. The S-only exact conversion impossibility remains only one method obstruction; it is not the reason for a claimed negative answer to R113.

## 7. Validation, inventory and decisive status

The owned `diagnostics.py` uses exact rational arithmetic and integers. It checks the new posterior formulas and moment cancellation, the conditional two-label adversarial reward by enumeration, the guard-rate spread, small downward-closed instances of L116, X116 rank inequalities, its dependence counterexample, and the two-sided sparse/dense calibration family. It also checks finite common-denominator edge gaps and lowest-degree gain extraction. I113's original deterministic diagnostics are independently replayed through its verified inventory. Neither collection is a universal theorem proof or a contribution certificate.

The final `verify.py` is offline and read-only. It first checks **every owned immutable artifact**, exact inventory and bytes, including itself and all diagnostic code. It then checks immutable inherited references and the original I113 inventory before loading inherited verifier code. That verifier checks all 10,373 original source-position/Git-blob bindings, every inherited extraction identity, selected source URLs, exact lexical memberships, reading passage membership and original diagnostics. The I116 verifier additionally checks its own passage identities, exact source-contract strings, frozen current ledger snapshots, external bytes and deterministic new diagnostic output. Only the four named live ledger originals may drift; neither their frozen snapshots nor any owned artifact may drift. No network, cache writes, bytecode, PDF extraction, repair or reseal occurs during verification. The seal is an inventory envelope, not a self-hash or a cryptographic signature.

Run from the repository (the verifier also locates its own root):

`PYTHONDONTWRITEBYTECODE=1 python3 -B frontier/experiments/i116_robust_prophet_continuation/verify.py`

Initial wrong-cwd read failures and output-truncation/rereading notes are retained in `validation-history.jsonl`. Preseal checks and their outcomes are retained; the final seal is created once after successful preseal validation. The first preseal replay passed in 17.95 seconds: the full inherited corpus/lexical replay, 35 then-recorded reading passages, 192 source-contract memberships and all 1,450 new finite diagnostic instances passed. Three subsequently recorded catalogue passages are checked again before the final seal. Source identity and exact finite arithmetic do not certify mathematical correctness of accepted source operations, universal proof validity, or substantiality.

The original arguments pass without repairs. The audit does not promote their technical deductions. R113's exact unresolved task remains a polynomial worst-case, density-free one-sample online rule attaining c/K against full-seed almighty order, or a genuine all-algorithms counterexample under both measure inequalities. A116 exposes why a uniform conditional comparison is too strong; L116 pays the desired loss for an offline retained optimum; X116 identifies the calibration/dependence hurdle and a genuine two-sided failure of a specific thinning composition. Those are the useful partials. **No substantial target is fully proved, and none is nominated.**
