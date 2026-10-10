# I52 — ergodic/dynamical discovery: additive standard-map entropy remains open

2026-10-09. **Completed discovery and gap report; no substantial finding nominated.** All deductions use the stipulated truth of the pinned OpenAI statements and proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. External papers are checked antecedents, not additional automatically true premises. This report makes no acceptance-count or priority claim.

The strongest target pursued is a constant additive loss in the area entropy of the exact standard map. Two constructions reach different useful interfaces: a finite-time continuant estimate and an invariant projective-measure estimate. Neither supplies the missing all-time deterministic control. An important screening result is that the weaker assertion `h/log K → 1` is already obtained by reusing the source's first-crossing proof operations. It is recorded with its reduction, **not offered as a new mechanism**.

## 1. Scope, frozen evidence, and previous screens

Read `AGENTS.md`, the ten-finding ledger and all four front-page/status files; snapshots are in [inputs](../sources/i52_ergodic_dynamical_discovery/inputs/). The task's later dependency update controls where those mutable snapshots lag parent integration. No shared/prior file, old seal, or old verifier was edited. No staging, commits, publication, or agents were used.

The [verbatim brief](../sources/i52_ergodic_dynamical_discovery/brief.txt), [working objections](../sources/i52_ergodic_dynamical_discovery/objections.txt), and [input manifest](../sources/i52_ergodic_dynamical_discovery/inputs-manifest.json) are frozen separately. The complete tree has 13,223 entries and 749 manuscript directories. `rg --files --no-ignore` enumerated 9,340 local corpus files; each was matched to its Git blob in that tree. This did not use the truncated root tree or treat the 719-entry catalogue as complete.

The [pinned manifest](../sources/i52_ergodic_dynamical_discovery/pinned-manifest.json) contains 97 files from ten manuscripts, with Git blob IDs, SHA-256 hashes, and immutable raw URLs. These are single-level copies of the relevant sources, not copies of previous evidence archives. [Passage records](../sources/i52_ergodic_dynamical_discovery/passages.json) identify the actual statements and proof passages used. The [search records](../sources/i52_ergodic_dynamical_discovery/searches.json) retain corpus/prior-screen query arguments and sorted line multisets. The verifier compares multisets, never raw `rg` order.

I05 already examined equal-degree polynomial averages and proposed a Gaussian specialization whose proof does not need the new corpus. I13 already refuted rate-free square-root nonconventional fluctuations using long-memory examples. Neither is reopened. Recurrence, product ergodicity, finite replication, diagonal subsequences, and the parked nonergodic topics in the brief are excluded.

## 2. Four precise screens, with early source and primary-literature audits

### A. A common exceptional set for nilsequence weights — reject as standard transfer

Fix an invertible mixing standard probability system, a positive integer `r`, distinct positive slopes `a_1,…,a_r`, and bounded fixed functions `f_1,…,f_r`. Candidate: there is a conull set depending on this tuple and these slopes such that

`N^{-1} Σ_{n=1}^N b_n ∏_j f_j(T^{a_j n}x)`

converges at every point of that set **for every nilsequence** `b`. This is a real simultaneous-weight assertion, not an uncountable intersection of tuple-dependent null sets. It does not quantify simultaneously over every bounded observable.

The master *Pointwise Multiple Ergodic Averages* gives all consecutive lengths (`thm:main`); insertion of constant-one slots gives distinct positive slopes. Its `inputs.tex`, `prop:smooth-input` and `lem:triple-convergence`, actually contain all-system triple convergence, not merely the mixing headline. The distinct-integer-slopes companion's `transfer.tex`, `prop:tr-oscillation`, bounds the sum of `w` deterministic-block oscillations by `C_{φ,b} sqrt(w)`; constants may depend on slopes and profile. Triple/fourfold companions were included in the audit. The master selected-law proof translates a **linear** averaging parameter, with endpoint error at most `2|t_0|2^{-a}`. This is not a polynomial-time or arbitrarily varying-function estimate.

Zorin-Kranich, [arXiv:1504.04647v2](https://arxiv.org/abs/1504.04647v2), Theorem 1.1 and Corollary 1.4, already transfer the unweighted `P_r` property for fixed slopes into this common-set nilsequence conclusion, with a stronger normalized Sobolev uniformity estimate. Its proof uses vertical Fourier decomposition and van der Corput induction. All the needed unweighted hypotheses are furnished by the master. **Disposition: an explicit prior-art transfer, not a fresh finding.** Arbitrary bounded weights are not covered.

Rokhlin's source `08-consequences.tex`, `cor:endomorphisms-flows`, already covers noninvertible maps through natural extensions and strongly `L¹`-continuous flows through fractional-time compactness. These are also excluded. No mixing rate is extracted.

### B. Strong mixing of an explicit fully irrational triangle — unresolved spectral bridge

Let `Q` be the area-one acute triangle with angles `πα, πβ, π(1−α−β)`, where `α=√2/5`, `β=√3/5`. All three ratios are irrational. Candidate: its unit-speed billiard flow is strongly mixing for normalized **full** Liouville measure `dA dθ/(2π Area Q)`, after deleting the null set of trajectories hitting a vertex in either time direction.

The ergodicity master already gives interior/boundary quantum ergodicity and density-one nodal-domain consequences. Those applications are not new. The weak-mixing companion proves, for bounded exact eigenfunctions, transverse rigidity `Yf=0` from `Xf=iλf`, then uses the side relations

`c(v)=c(Rv) exp(−iλ d·v)`.

At an irrational vertex, the angular relation kills every nonzero Fourier mode exactly; the third side kills nonzero `λ`. Its long-average proof first fixes discarded mass, then sends the spatial smoothing scale to zero, and only afterwards removes the discarded mass. It proves an exact-eigenfunction assertion, not a uniform estimate for `(X−iλ)f` small.

Chaika–Forni, [current arXiv v2](https://arxiv.org/abs/2003.00890v2) and [2026 Annals record](https://annals.math.princeton.edu/2026/203-3/p01), concern a dense `G_delta` family of full billiards. Arana-Herrera–Chaika–Forni, [2410.11117v1](https://arxiv.org/abs/2410.11117v1), concerns almost-every-direction weak mixing for rational billiards. Its §6.2(3) still asks for a polygon with mixing full billiard flow. These are different phase spaces/quantifiers. No stronger external mixing theorem for the displayed triangle was established in this search.

The unpaid implication is continuous spectral measure ⇒ Rajchman spectral measure (Fourier transform tending to zero), which is false in general. An explicit scalar diagnostic is the centered Cantor distribution `X=Σ ε_j/3^j`, independent signs. Its continuous law has Fourier transform `∏ cos(t/3^j)`; at `t=2π3^m` the transform is the same nonzero product for every `m`. Thus absence of atoms alone cannot finish this candidate. This measure is **not** asserted to be a billiard spectral measure. In addition, the exact angular multiplier `|1−exp(2π i mα)|` has arbitrarily small nonzero values, so the source's exact holonomy argument is not a uniform angular coercivity bound. **Disposition: a specific missing spectral regularity estimate, not a mixing proof or billiard counterexample.**

### C. Constant additive entropy loss at every large parameter — selected

For the exact map

`f_k(x,y)=(x+y+k sin(2πx), y+k sin(2πx)) mod 1`,

with normalized area `m`, put `K=2πk`. The target is

**H:** there exist absolute `C,K_0<∞` such that, for every `K≥K_0`,

`h_m(f_{K/(2π)}) ≥ log(K/2) − C`.

Logs are natural. No ergodicity, noise, perturbation, parameter deletion, or pointwise uniform hyperbolicity is assumed. H is weaker than a vanishing additive error or the exact Chirikov lower conjecture, but stronger than positivity and relative asymptotics.

The pinned master states positivity at each sufficiently large parameter (`main:entropy`) and already derives a positive-area hyperbolic ergodic component with a finite cyclic Bernoulli decomposition (`main:components`). More importantly, its cancellation, fast-bridge, first-crossing, and capped-deficit operations are available premises. Section 4 below audits their stronger consequence before proceeding to H.

Knill's [current version, math/9908014v2](https://arxiv.org/abs/math/9908014v2), explicitly removes an incorrect earlier proof. Its Conjecture 1.1 proposes an even more explicit additive bound; it is **not a proved input**. The one-step upper bound is already noted on its p. 2. Berger–Turaev's [published paper](https://www.ma.imperial.ac.uk/~dturaev/mypapers/advmath19.pdf), Theorem A and Corollary C, produce nearby conservative maps with positive metric entropy; they do not supply H for the exact sine map. Blumenthal–Xue–Young's [1701.07583v1](https://arxiv.org/abs/1701.07583v1), Theorems 1–3, use positive random perturbations and diffuse stationary projective laws. That mechanism is relevant to Construction B, but removing the noise is a missing step. Blumenthal's [1710.09058v1](https://arxiv.org/abs/1710.09058v1), Theorem D, gives a finite-time Hölder correlation bound growing with the time horizon; its long-time theorems require increasing coefficients. Neither is a fixed-parameter infinite-time estimate.

The accessible [MathDB problem](https://mathdb.com/p/345911/sinais-positive-entropy-conjecture-for-the-standard-map) is Sinai's positive entropy conjecture for every nonzero parameter. The actual response calls it a famous positive-entropy conjecture and contains a separate AI-assisted remark about the OpenAI large-positive-parameter claim. H concerns the large-parameter quantitative remainder, not the small-parameter conjecture. **No numerical significance score was observed or inferred.**

### D. Extend the smooth-model obstruction to rough equivalent volume — unpaid regularity

Candidate: the particular zero-entropy ergodic system constructed in *A finite-entropy system without a smooth positive-volume model* has no smooth compact finite-dimensional model whose invariant probability is merely equivalent to a smooth volume, with arbitrary measurable positive density.

The source `thm:main` expressly restricts the invariant density to smooth positive density. Its `thm:switching` constructs cellwise independent pairs, at partition cost `exp(C B_k 2^k)` with `Σ B_k^16<∞`, and an **unnormalized** retained switch law bounded by `2ν`. The proof uses uniform local density ratios, a pair Jacobian, and global injectivity. Measurable equivalence alone does not give these local density ratios at the required scales. Truncating a rough density or using an arbitrary measurable conjugacy does not preserve the geometric/summability interface. A quantitative modulus for the retained pair density is unpaid. The separate C¹ entropy-counterexample master is explicitly a **noninvertible** self-map; its entropy localization and homology operations do not remove that restriction. **Disposition: no rough-density or diffeomorphism counterexample claimed.** This screen was not pursued in preference to H.

## 3. Exact standard-map interfaces

In transfer coordinates `(q,p)=(x,x−y)`, the map is

`F(q,p)=(2q−p+k sin(2πq), q)`,

and

`A(q)=[[v(q),−1],[1,0]],  v(q)=2+K cos(2πq),  M=K+4`.

The coordinate change preserves area and changes logarithmic derivative norms by a bounded amount. Put

`T_{a,b}=A(q_{b−1})⋯A(q_a)`, `a_n(K)=n^{-1} ∫log||T_{0,n}|| dm`,

and `e_n=1−a_n/log M`. For every `K` and integer `n≥1`, `0≤a_n≤log M`. Subadditivity and stationarity give

`h_m(f_k)=lim_n a_n=inf_n a_n`,

by the source's Oseledets/Pesin contract and bounded convergence. **A finite-time lower bound on `a_n` has the wrong direction to be a lower bound on `h`.** Dyadic `a_{2^j n}` are nonincreasing and have the same limit.

The source operations used below are:

1. `can:theorem`: uniformly in center, length `n`, and all large `M`, the event that both wings grow at least `(1−δ)n log M` while their concatenation grows at most `δn log M` has probability at most `C exp(−γn)`.
2. `bridge:theorem`: for fixed bounds on finitely many bounded Lipschitz shortfall observations `W≥0,H`, at opposite ends of a long segment,

   `E[1_{log_M||T_{a,b}||≥c_b(b−a)} W 1_{H>t}] ≤ C(EW+M^{−σ(b−a)}) P(H>t/2)`.

   The constant and lower cutoffs may depend on the fixed observation bounds and **fixed** threshold `t`. The fast-segment indicator remains present. This is not unconditional mixing and says nothing directly about tangent slope conditioning.
3. `scale:fourpoint`, `scale:truncation`, `scale:doubling`: determinant-one geometry and cancellation scarcity give `e_n≤e_{2n}≤C e_n+C/n`.
4. `scale:selection` through `end:remainder`: selected growing deficits generate measures off affine distance arrays, a positive dilation decomposition, support exclusions from (1)–(2), exact capped balance, a strict terminal loss, and a nonpositive invariant remainder. In `end:balance`, intermediate affine speeds are handled one fixed threshold at a time; at unit speed one first takes a fixed weak limit and then shrinks a dyadic interval.

The local-scarcity proof is also significant for what it does **not** supply: its reciprocal-cosine comparison handles almost opposite cosines and vanishing phase slopes by normalized analytic identities and Hausdorff subsequences. It yields uniform qualitative scarcity sufficient for (1), but no printed fixed-parameter additive entropy budget. The exact third-order polynomial extraction cannot be replaced silently by a quantitative anti-concentration estimate for the invariant projective law.

## 4. A stronger source-operation consequence, deliberately not nominated

**Technical deduction S.** Under the accepted proof operations,

`h_m(f_{K/(2π)})/log(K+4) → 1` as `K→∞`.

Here is the reduction, including the relevant quantifiers. If S fails, since the ratio is in `[0,1]`, there are `η>0` and `K_j→∞` such that

`lim_n e_n(K_j)=1−h_m(f_{K_j/(2π)})/log(K_j+4)≥η`.

The source's fixed-length cone argument proves `e_a(K_j)→0` for every fixed integer `a`. Choose dyadic `n_0(K_j)→∞` slowly so that `e_{n_0}→0`, and put `θ=(n_0^{-1}+e_{n_0})^{1/2}`. For all large `j`, `θ<η`. Hence a first dyadic `N≥n_0` with `e_N>θ` exists, just as in `scale:selection`. The doubling estimate gives

`θ<ε:=e_N≤Cθ+C/n_0→0`, `ε n_0→∞`,

`e_{2^m n_0}=o(ε)`, `e_{2^m N}=O_m(ε)` for every fixed integer `m`.

The entire downstream accepted construction uses these displayed selected-scale properties, stationarity, the fixed-parameter matrix estimates, and the two uniform source inputs. It does not use `e_n→1` again. Specifically: `scale:local-mass` telescopes those boundaries; `scale:limits` and `scale:decomposition` give `S_*μ=μ+ν`; `shape:exclusions` uses `ε n_0→∞` and fixed-test bridge bounds; `end:balance` gives `∫G dμ=H_Φ>0`; `end:terminal` and `end:remainder` give `∫G dμ<H_Φ`. This is the same contradiction. The only change to the source is replacing its reason for existence of the first crossing by the displayed lower bound `η`.

Thus S is a reuse of already accepted operations, not an independently new bridge. It provides no modulus. A loss such as `sqrt(log K)` is compatible with S and incompatible with H. Obtaining `e_∞=O(1/log K)` is not justified by repeating the same compactness argument at a moving threshold.

## 5. Construction A: deterministic continuants and an additive growth budget

### 5.1 A fully proved finite-time bound and sharp-scale upper bound

**Proposition F.** For `K≥16`, `2≤b≤K/4`, and every integer `n≥1`,

`a_n(K) ≥ log(K/2) − 2 n b log(K+4)/K − 2/[b(b−1)]`.  (F)

Moreover,

`h_m(f_{K/(2π)}) ≤ a_1(K) ≤ log(K/2)+4/K`.  (U)

These are technical finite-time/upper estimates, independent of the new source inputs. In particular, (F) is uniform on growing horizons `n=o(K/log K)` with an `o(1)` additive error after optimizing `b`; it does not establish H.

**Proof of F.** Let `G={|v(q_j)|≥b for 0≤j<n}`. Each `q_j` is uniform, whether or not the orbit coordinates are independent. The law of `v` has density

`w_K(t)=1/[π sqrt(K²−(t−2)²)]`, `2−K<t<2+K`.

On `|t|≤b≤K/4`, `w_K(t)≤2/(πK)` for `K≥16`. Thus `m(G^c)≤2nb/K` by a union bound.

Solve `u_{j+1}=v(q_j)u_j−u_{j−1}` with `u_0=1,u_{−1}=0`. On G all ratios are defined and `|u_{j+1}/u_j|≥b−1` inductively. Indeed the preceding reciprocal ratio has absolute value at most `1/(b−1)`. Consequently

`log|u_{j+1}/u_j| ≥ log|v(q_j)| − 2/[b(b−1)]`,

using `log(1−z)≥−2z` for `0≤z≤1/2` (the first step has no error). Therefore `log||T_{0,n}||≥Σ_j log|v(q_j)|−2n/[b(b−1)]` on G. Everywhere the left side is nonnegative. Integrating and subtracting the bad-set contribution, whose signed average is at most `m(G^c)log M`, proves F once

`∫_0^1 log|2+K cos(2πq)| dq=log(K/2)`  (J)

is established. To see J, put `z=e^{2πiq}` and factor `2+K(z+z^{-1})/2=(K/(2z))(z²+(4/K)z+1)`. For `K>2` both roots are on the unit circle; each factor `log|z−ζ|` has zero circle mean and integrable logarithmic singularity. This proves J. Optimizing `b≈(K/(n log M))^{1/3}` proves the growing-horizon assertion whenever that number is at least two and at most `K/4`.

**Proof of U.** The Euclidean norm of `A(t)=[[t,−1],[1,0]]` is `(sqrt(t²+4)+|t|)/2`, so its log is `asinh(|t|/2)`. Define `D(t)=asinh(|t|/2)−log|t|≥0`. For `t≠0`, `D(t)≤t^{-2}`; also `∫_R D(t)dt=4`, by integration by parts on each half-line. On `|t|≤K/2`, `w_K(t)≤2/(πK)` for `K≥16`; on the remainder, `D(t)≤4/K²`. Hence

`a_1−log(K/2)=E D(v)≤8/(πK)+4/K²≤4/K`.

Subadditivity gives `h≤a_1`. This proves U without claiming novelty for an upper bound already noted by Knill.

### 5.2 Attempt to continue beyond the finite horizon

For adjacent length-n blocks set

`L_n(z)=log||T_{0,n}||+log||T_{n,2n}||−log||T_{0,2n}||≥0`.

Then exactly

`a_{2n}=a_n−E L_n/(2n)`,

and for a starting scale `n_*`,

`a_{n_*}−h = Σ_{j≥0} E L_{2^j n_*}/(2^{j+1} n_*)`.  (BUDGET)

This telescopes by bounded convergence. BUDGET is an identity, **not a newly proved useful bound**. At the finite horizon supplied by F, H would follow from a constant bound on its right side. Such a bound is essentially the remaining target at that interface and must not be relabeled as an established lemma.

I tried to pay it using the source's local cancellation estimate. In base-M units the source proves only

`E ℓ_n≤C(1+2n e_n)`, where `ℓ_n=L_n/log M`.

Inserting this in BUDGET gives terms of size `C log M/n + C log M e_n`; the latter cannot be summed over infinitely many dyadic scales. The fast-bridge estimate might isolate repeated loss events, but it restricts to bridges of speed at least `c_b` and its constants are not uniform as the shortfall threshold shrinks like `1/log M`. The capped-limit proof also uses strict terminal loss with no quantitative lower margin. These are concrete unpaid interfaces, not a claim that H is false.

The alternative all-good-orbit cone construction fails because for fixed K a critical strip has positive area and its union bound grows with n. Smooth finite-time correlation estimates do not fix this: they deteriorate with the horizon, and the relevant loss event also depends on tangent direction and past products.

## 6. Construction B: projective dynamics and a precise conditional-density criterion

This construction does not sum dyadic block losses. It studies an invariant law on the tangent projective bundle and attempts to control the single-step logarithmic singularity. The overall strategy has an explicit antecedent in Blumenthal–Xue–Young; the missing deterministic estimate is identified rather than assumed.

Write a line as `(1,r)` with `r=∞` for the vertical line. The projective lift is

`F_hat(q,p,r)=(F(q,p), 1/(v(q)−r))`.

It is a continuous invertible map of the compact projective bundle; the fractional formula is interpreted projectively at its poles. For finite r,

`g(q,r)=log(||A(q)(1,r)||/||(1,r)||)`

`= ½log((v(q)−r)²+1) − ½log(1+r²)`.  (P)

The function g extends continuously to the bundle and is bounded at each fixed K.

### 6.1 An invariant lift with the entropy integral

Start with `ν_0=m×` uniform angular measure and let `ν_N=N^{-1}Σ_{j=0}^{N−1}(F_hat^j)_*ν_0`. Any weak limit `ν` is invariant and projects to m. Telescoping logarithmic expansion gives

`∫g dν_N = ∫ [N^{-1}log||T_{0,N}u||] dν_0`.

For almost every base point, Oseledets gives the top exponent for all lines except at most one stable line when the exponents are distinct. Uniform angular measure assigns that line measure zero. When both exponents are zero, the limit is zero for every nonzero vector on the Oseledets set. Fubini and the bound `|N^{-1}log||T u||||≤log M` permit dominated convergence. Thus every subsequential limit of these Cesàro laws satisfies

`∫g dν=h_m(f_k)`.  (LIFT)

No uniqueness of ν, ergodicity of m, or absolute continuity of ν is asserted. Initial angular absolute continuity need not survive uniformly in N.

### 6.2 A sufficient condition, with its full proof

**Conditional Proposition P.** Suppose an invariant lift ν as above has the following property: for ν's r-marginal almost every projective r, its conditional q-law is bounded by `C_0 dq`, with `C_0≥1` independent of K. Then

`h_m(f_k)≥log K−C C_0` for `K≥16`,

with an absolute C. Thus a uniform bound of this kind would imply H. This condition is stronger and more geometric than the target; it has **not** been verified for these invariant lifts.

For any real a and `δ>0`, the elementary cosine sublevel bound is

`|{q:|cos(2πq)−a|<δ}|≤4 sqrt(δ)`.

One proof integrates the arcsine density and splits at its two endpoints; its maximal interval mass is of order the square root of interval length. Constants larger than one also cover `δ≥1`. Conditional density therefore gives

`ν(|v(q)−r|<s)≤4C_0 sqrt(s/K)` for finite r, after conditioning and integrating. The preimage of `r'=∞` is `{r=v(q)}` with finite r; each conditional q-law assigns this finite level set measure zero. Invariance implies `ν(r=∞)=0`.

Apply the same bound with `s=1/R` and use invariance of the r-marginal:

`ν(|r|>R)≤min(1,4C_0/sqrt(KR))`, `R>0`.  (TAIL)

Layer-cake integration yields

`∫½log(1+r²)dν=∫_0^∞ [R/(1+R²)]ν(|r|>R)dR ≤ C C_0/sqrt K`.

For the other term in P put `a=(r−2)/K`. Since

`½log((v−r)²+1)≥log K+min(log|cos(2πq)−a|,0)`,

conditioning and another layer-cake estimate bound the negative part by

`∫_0^∞4C_0 exp(−t/2)dt=8C_0`.

The first term is integrable: its upper bound is `log(M+1)+log(1+|r|)`, and TAIL controls the latter. Thus both terms may be integrated separately in P. Combining them with LIFT proves the proposition.

### 6.3 Attempts to establish the missing condition

Adjacent base coordinates `(q,p)` are independent uniform variables, but r depends on a long tangent history. This gives **no** independence of q and r. Under one lift of the initial product law, the new q is uniform even conditioned on old q and initial direction, because old p was uniform; this explains why the first step looks promising. At later steps p and r are correlated, and the same argument no longer applies.

A direct change-of-variables approach also loses its uniform constant. The angular Jacobian of a determinant-one matrix acting on lines is `||Au||^{-2}`. An N-step pushforward from the smooth initial angular law may therefore have densities of size `M^{2N}`. Compactness of ν_N alone does not supply a bounded conditional q-density in the limit. The source's contracting graphs control endpoint **growth-shortfall observations on fast bridges**; they do not give a conditional q-law at fixed r or a bound stable under projective Cesàro limits. Identifying such a graph-to-projective estimate is the genuine missing bridge in this route.

This is precisely where the noisy antecedent has an extra operation: smoothing/diffusion of the projective stationary law. Setting its noise parameter to zero violates its hypotheses. We do not import its lower bound into the deterministic system.

## 7. Adversarial examples and finite diagnostics

1. **Rare bad matrices can erase long growth.** Let `A_L=[[L,−1],[1,0]]`, `L≥3` integer, and write `A_L^{2m}=[[P,−Q],[Q,−R]]`. Set `b=2Q/P`. Then `B=A(b)A_L^{2m}` has determinant one and trace zero, hence `B²=−I`. The periodic cocycle with `2m` entries L and one entry b per period has exponent zero; the bad-site frequency tends to zero as m grows. This is an exact rational matrix example, not an orbit of the standard map. It does not satisfy all of the source's uniform cancellation estimates and does not refute H. It refutes the shortcut from rare critical visits and long good runs alone.
2. **Actual large-parameter nonhyperbolic points.** For each integer `j≥1`, let `k_j=sqrt(j²+π^{-2})` and choose `q_j` with `sin(2πq_j)=j/k_j`, `cos(2πq_j)=−1/(πk_j)`. Then `(q_j,0)` is an actual fixed point of f, and its transfer matrix is `A(0)`, a rotation of order four. Thus no positive pointwise lower growth rate holds at every point at arbitrarily large parameters. This zero-area example makes no claim about a surrounding KAM island and does not obstruct an area entropy lower bound.
3. **Base marginals do not control tangent conditioning.** Take q uniform and set `r=2+K cos(2πq)`. Both its base lift with independent uniform p and its q-marginal are perfectly admissible probability laws, but `v−r=0` identically. The conditional q-law given r is atomic and the next line is vertical. This law is not claimed invariant. It directly refutes an inference of conditional density from the base area marginal.
4. **Spectral and holonomy diagnostics.** Finite Cantor products check the nonvanishing Fourier subsequence described in screen B; near-resonant angular modes test the absence of a uniform inverse to exact irrational holonomy. Neither is a billiard simulation or proof of nonmixing.
5. **Genuine finite standard-map trajectories.** The diagnostic script samples deterministic initial grids at several K and horizons, tracks stabilized transfer products, checks the cone inequality wherever its stated good-orbit hypothesis holds, and compares finite averages with the proved bounds. These values are finite-time diagnostics, not entropy estimates or universal numerical certification. One-dimensional quadrature separately checks the explicit one-step norm formula and upper remainder scale.

The [diagnostic program](../experiments/i52_ergodic_dynamical_discovery/diagnostics.py) includes exact rational trace/determinant checks and negative controls. Its [recorded output](../experiments/i52_ergodic_dynamical_discovery/diagnostics.json) is reproducible. No diagnostic is substituted for the analytic arguments above.

## 8. Evidence reproduction, limitations, and handoff

Run from the repository root:

```bash
python frontier/experiments/i52_ergodic_dynamical_discovery/verify.py
```

The verifier is read-only. It checks the final artifact seal, pinned blob hashes, all 9,340 corpus blobs, frozen input hashes, passage bindings, retained HTTP bodies, PDF text extractions, search line multisets, and diagnostic recomputation. It reports current differences in the four mutable ledgers separately. It neither refreshes an old seal nor invokes I49's verifier. Provenance and finite checks do not constitute independent proof acceptance.

The HTTP archives record retrieval dates, status codes, hashes, redirects and version pages. Current arXiv versions observed: Knill v2 (2005-11-25), Zorin-Kranich v2 (2015-08-05), BXY v1 (2017-01-26), Blumenthal v1 (2017-10-25), Chaika–Forni v2 (2025-08-14), and Arana-Herrera–Chaika–Forni v1 (2024-10-14). Berger–Turaev was read in the published author-hosted PDF. The Annals publication record was checked separately. The Cambridge DOI could not be opened by the web tool, but direct HTTP retrieval then supplied its record and the published Blumenthal PDF; its Theorem D retains the finite-time restriction. A web-tool failure on the direct MathDB URL was likewise followed by a successful archived HTTP retrieval. The current [Berger ICM 2026 survey](https://doi.org/10.1137/25M1810787), §2.3, was readable through the web tool; it describes the perturbative entropy construction and its fragile heteroclinic-connection interface, not an exact standard-map additive bound. Its direct HTTP request returned 403, retained alongside the successful web response. Initial optional HTML parsing failed because `bs4` was absent; standard-library parsing replaced it. These failures are retained in the process notes.

**Strongest established partial:** source-operation deduction S plus the explicit finite-time bound F and upper bound U. **Strongest developed conditional construction:** Proposition P with a proved tail/integrability argument. **Unpaid:** a deterministic estimate controlling recurrent tangent near-cancellation uniformly in time at fixed parameter—either an effective summable growth-loss bound beyond the source's qualitative crossing argument, or a valid uniform anti-concentration substitute for the projective conditional-density hypothesis. H is unproved and unrefuted here. The weighted screen is a known transfer; the billiard and rough-density screens have explicit unpaid interfaces. None is presented as a substantial newly enabled theorem.
