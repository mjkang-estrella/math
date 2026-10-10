# I42 — Independent proof audit of the four-time profile and fair-start partial results

**R: PASS ORIGINAL WITHOUT REPAIRS. Representations: PASS ORIGINAL WITHOUT REPAIRS. Entropy/Orlicz sufficient criterion: PASS ORIGINAL WITHOUT REPAIRS. Fair-start product-refresh countermodel: PASS ORIGINAL WITHOUT REPAIRS.** These verdicts assume the pinned OpenAI theorems and local proof operations, as instructed. They concern the original I41 report, whose bytes are preserved. The derivations below verify applicability and expand the original argument; they do not replace a false statement, add a hypothesis to its theorem, change its construction, or repair its proof.

The fixed-horizon profile transfer is technical. It pays C(ii), not C(i). Full two-disorder W remains **unproved and unrefuted**. There is no substantial nomination, acceptance, count change, priority claim, or attempt here to solve the remaining warming problem. The inherited count is six of ten. No shared/prior file, stage, commit, publication, or additional agent is part of this review.

## 1. Frozen object and exact scope

The reviewed object is `frontier/iterations/i41-rademacher-fair-start-warming.md`, including its §4 author proof, read in full together with I39, I40, their original briefs, and the parent verification records. The complete operative I42 brief is copied verbatim from the parent's task record to `../sources/i42_four_time_profile_r2/full-brief.txt`. The I41 sealed package, inherited objections, manuscript dependencies, and source identity records are independently frozen. `inputs.json`, `read-passages.json`, and `contracts.json` distinguish bytes acquired, passages actually read, and proof hypotheses invoked.

Throughout, the pin is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. QU means *Universality of critical quench autocorrelations in the Sherrington–Kirkpatrick model*, October 5; FU means *Functional universality of critical SK autocorrelations*, October 5. References to QU §7/8/9 mean its `build/sections/07-history-cutoffs.tex`, `08-clock-scores.tex`, and `09-replacement.tex`, respectively. I read all three files, including the proofs. I also read the actual Gaussian strong-semigroup/two-copy-tail proof, warming theorem and its final assembly/log-tail proof, and FU's static polynomial-moment, conditioned-measure, recovery/positivity/relaxed-energy statements and proofs, plus the gradient-domain statement and the proof of its constant kernel. Upstream local estimates are accepted, not subjected to a new truth audit.

The convention is

\[
 H_J(x)=n^{-1/2}\sum_{i<j}J_{ij}x_ix_j,\quad
 \pi(x)=\frac{e^{H_J(x)}}{\sum_y e^{H_J(y)}},\quad \nu(x)=2^{-n},
 \qquad T=n^{2/3},\quad Q(s)=P_{sT}.
\]

Each site has rate one. The generator is \(L=\sum_i(E_i-I)\), not its division by n. The disorder entries are independent standard Gaussians or independent symmetric signs, with zero external field and inverse temperature one. Define

\[
 q(x,y)=n^{-2/3}x\cdot y,\quad
 F_t(x)=\mathbb E_x q(x,X_{tT}),\quad A_n(t)=\pi F_t,
 \quad G_t=F_t-A_n(t),\quad R_n(u,t)=\|Q(u)G_t\|_2^2.
\]

R asserts joint convergence of \((R_n,A_n)\) to \((R_g,A_g)\), with R in \(C([c,d]\times[a,b])\) for each fixed \(0<c<d\), \(0<a<b\). This is convergence in disorder law of quenched expectations; thermal randomness has already been averaged. No time endpoint approaches zero or infinity with n. The limit is the random Gaussian-source object \(R_g(u,t)=\|S_u^gG_t^g\|_{L^2(\Pi_g)}^2\), not a claim that its distribution is a normal distribution.

## 2. Inherited analytic inputs checked independently

**The stationary four-time identity is exact.** On one stationary path in rescaled time, condition the first overlap on \(X_t\). Reversibility gives its conditional mean \(F_t(X_t)\). The Markov property and conditioning the last leg give

\[
 H_n(u,t):=\mathbb E_\pi[q(X_0,X_t)q(X_{t+2u},X_{2t+2u})]
 =\langle F_t,Q(2u)F_t\rangle_\pi
 =A_n(t)^2+R_n(u,t).
\]

The shared middle leg is essential; independent replicas would give a different quantity. The length is 2u, since \(Q(u)^*Q(u)=Q(2u)\). Centering subtracts exactly A². In particular R is nonnegative and decreases in u despite the signed endpoint product.

**I40 G and I41's audit of it pass without repairs.** Here is the actual analytic bridge needed again for the Gaussian side of R. On QU's represented Gaussian subsequence, let \(x_{a,n}=n^{-1/3}\langle u_a,x\rangle\). Orthogonality gives \(F_{n,t}=\sum_a x_{a,n}Q(t)x_{a,n}\). QU `glim:static-tail` controls

\[
 V_{n,m}=(\pi\otimes\pi)\left(\sum_{a>m}x_{a,n}(x)x_{a,n}(y)\right)^2,
 \qquad \lim_m\limsup_n V_{n,m}=0.
\]

Its proof retains the entire square before Haar comparison. Multiplication by the squared cube/spherical likelihood cancels both Gibbs denominators; changing overlap within a cell changes the projected overlap by \(O(n^{-2/3})\), uniformly in m; spherical sign symmetry then removes cross terms. The monotonicity \(V_{n,m}=\sum_{a,b>m}(\pi x_ax_b)^2\) justifies the countable tail extraction. It is not an assertion about the divergent sum \(\sum_a\pi x_a^2\).

For each fixed positive a, QU warming gives an eventually common kernel cap K(a). Conditional Jensen, using the full row mass one, gives

\[
 \left\|\sum_{a>m}x_{a,n}Q(t)x_{a,n}\right\|_2^2
 \le\iint p_t(x,y)\left(\sum_{a>m}x_{a,n}(x)x_{a,n}(y)\right)^2d\pi(x)d\pi(y)
 \le K(a)V_{n,m},\quad t\ge a.
\]

No positivity of the sum is used. The limiting finite tail intervals obey the same bound. For each head coordinate, FU's polynomial-growth static convergence supplies strong L² convergence and a bounded fourth moment. QU `glim:semigroup-strong` applies to that strong input at varying positive times. The evolved factor has supremum norm at most K(a)π|x_a|. Clip the unevolved coordinate at R: its product error is at most \(C_a(\pi[x_a^2\mathbf1_{|x_a|>R}])^{1/2}\le C_a'/R\). Multiplication by the bounded common clipped cylinder preserves strong convergence, by common-cylinder approximation. Thus take n, then R, then m to obtain strong \(G_{n,t_n}\to G_t^g\) whenever \(t_n\to t\in[a,b]\). The same bounds prove compactness and L² continuity of the limit family.

The source strong-semigroup proof uses bounded resolvent optimizers, whose polynomial supremum, norm, and energy bounds meet FU's restricted relaxed-energy hypothesis. Recovery uses each fixed polynomial index before its outer limit. It never asserts compactness of all bounded-energy sequences. FU's constant-kernel proof uses finite-block angular connectedness and the trivial tail field under its absolutely continuous product-Gaussian tail law. Together with \(c_*>0\), spectral calculus gives \(S_uG_t^g\to0\) for each t; a finite L² net gives uniformity on [a,b].

For any initial probability ρ, one common Gaussian warming event gives \(\|d(\rho Q(s_0))/d\pi-1\|_2\le\sqrt{K(s_0)-1}\), even if ρ depends on disorder. Therefore

\[
 \sup_\rho\sup_{s\ge S,t\in[a,b]}|\rho Q(s)F_t-A_n(t)|
 \le\sqrt{K(s_0)-1}\sup_t\|Q(S-s_0)G_{n,t}\|_2.
\]

Contraction handles all late s before any limit. For fixed S the right profile converges; compact-family decay handles S→∞. Tight-constant localization or the source represented-subsequence convention pays the disorder quantifier. On an offending sequence \(S_k\to\infty\), compare with each fixed integer S before Portmanteau, using the closed threshold ≥η. The auxiliary Gaussian diagonal has no effect on the physical functions. These checks confirm the original all-law G, but do not make G substantial.

**C passes as sufficient only.** The same inequality for the fair start is \(\sup_{s\ge s_0+u,t}|B_n-A_n|\le L_n\sqrt{\sup_tR_n(u,t)}\). For deterministic M, split its failure probability into \(\mathbb P(L_n>M)\) and \(\mathbb P(\sup_tR_n>\eta^2/M^2)\). First n→∞, then u→∞, then M→∞ proves W under C(i) and C(ii). Independence of L and R is unnecessary. C(i) is not proved necessary.

The old spike calculation also passes: with \(\pi(E)=m^{-3}\), \(\rho(E)=m^{-1}\), \(f=m\mathbf1_E\), one has \(\rho f=1\), \(\pi f=m^{-2}\), \(\pi f^2=m^{-1}\), entropy at most \(2\log(m)/m\), and a density-square contribution m. The complement contributes nonpositive entropy. I39's actual eight-state product-chain calculation likewise passes: its late bump is \(e^{-t}/72\), and the hidden centered variance is \(4e^{-2t}/27\). Keeping only z loses strong convergence of F; keeping x,y loses ergodicity. Neither is an SK counterexample or an objection to G.

## 3. Audit of R: why the third leg meets the source hypotheses

### 3.1 Geometry, conditional laws, and the filtration

Put \(c_0=\min(a,2c)\), \(C_0=\max(b,2d)\). The three complete legs tT, 2uT, tT all lie in \([c_0T,C_0T]\). Use the source binary tree independently on each leg, with its chronological check order (at a common right endpoint, smaller nodes first). This does not introduce a check spanning a leg boundary.

A prefix through its first failing check has zero, one, or two completed earlier legs and the usual earlier-sibling forest in its final partial leg. Within that leg the maximal-root lengths decrease and dominate the failing-root length. Across legs, each complete root has length at least c₀T and every later root is at most C₀T. Thus an earlier maximal root has length at least κ times any later root, with \(\kappa=\min(1,c_0/C_0)>0\). The node count is at most \(C(c_0,C_0)T\); maximal-root count is \(O(\log n)+2\). The constant κ need not be one, and the middle leg need not be shorter than the first.

For a nonnegative external test v, \(v\le n^B\), base mass \(z\ge n^{-M}\), the normalized tested path density relative to the ordinary path is ≤n^(B+M), since every check weight is at most one. This remains true with all four observed endpoints in v. **Those endpoints are variables in the test, not information revealed at time zero.** In the natural forward filtration their effect enters the tilted predictable intensities. The source Hellinger bound consequently gives action \(\mathcal J\le n^\eta\) with arbitrary inverse-polynomial confidence. A fixed polynomial test budget changes the required moment order and n-threshold, not the exponent losses C_Kβ.

Fix a node I=[v,w] and condition on its exterior and boundary spins x,y. Checks in other legs are disjoint; ancestors and the endpoint test are fixed by this conditioning. The only remaining weights are its proper descendants. Therefore the conditional interior is exactly

\[
 \mathsf C_I^{x,y}(d\omega)=
 \frac{\prod_{J\subsetneq I}w_J\,\mathbf1_{X_w=y}}{\pi(y)\bar k_I(x,y)}\mathsf P_x^I(d\omega).
\]

This proves law preservation of resampling, rather than importing it from the printed two-leg class. Iterating the same conditional sampling proves the marginal claim for copies inside copies. It does not make complete copied histories independent; independent interiors are conditional on the appropriate shared boundaries.

The endpoint lower-bound argument integrates the node first and drops all other weights:
\(\mathbb P_{test}(\bar k_I(X_v,X_w)<\delta)\le n^{B+M}\delta\).
Choose δ=n^−L after the desired precision. A retained proper node in the remaining third gives forward and reversed prefix-density bounds \(n^L\exp(CN(|I|))\). Local marked detailed balance, including self refreshes, permits reversal of this one conditional interior. Reversal of the entire stopped forest is neither needed nor asserted.

Within each root, the two/four-overlap estimates use disjoint contained nodes between observation times and between the root start and the first time. Their cap cost is \(\exp(CN(m))\), paid by static exponents whose ratios to N(m) are n^(2β) and n^(7β). The polynomial density n^(B+M) and polynomial time-grid union fit inside these tails. The proof never needs a new cross-leg overlap estimate: it uses overlaps within the root being compensated. The extra external endpoints remain covered by the tested-law density. Conditional copies inherit these overlap events marginally; no rare boundary gets a uniform sharp assertion.

Finally, if z<n^−M, do not normalize. The coarse coefficient proof uses the size support, positive leaf transitions, O(log n) recursion depth, and at most K differentiated slots. With three legs these facts still give \(|\partial^jZ|\le n^{C_K}z\). Products, polynomial query/node counts, and the later n^(10K) factors are paid by selecting M and exceptional precision last. This prevents an inverse-small-mass error.

### 3.2 Fixed-weight derivative allocations, including initialization

In this subsection write C_l(D) for the source's conditional score coefficient \(R_l(I)\), to avoid confusion with the profile R. The accepted local estimates supply

\[
 |C_l(D)|_\infty\lesssim_\beta D^{l/2},\quad
 |C_l(D)|_2\lesssim_\beta D^{l/2-1},\quad
 |C_l(D)|_4\lesssim_\beta D^{l/2-1/2},
\]

\(|C_3|_1\lesssim_\beta D^{-1/4}\), \(|C_l|_1\lesssim_\beta D^{(l-4)/2}\) for l≥4. At D≥Tn^−0.005 there are the source late gains n^−0.01 for the L⁴ norm of C₁, n^−0.001 for L² of C₂,C₃, and n^−0.0007 for L¹ of C₄. Their proofs require precisely the local conditional law, overlap event, action budget, and endpoint-averaged precision just verified. No dependence on a count of two legs appears in those local inductions.

There is still **one** stationary initialization factor \((1+v q_e(X_0))/(1+v\bar q_e)\), with v=tanh of the coefficient perturbation. New leg boundaries are Markov transitions, not new initializations. If only initialization is differentiated, the initial marginal density p is bounded by n^(B+M). The exact edge/replica identity and static pair tail give \(|\pi[pq_e]|_2\lesssim_\beta T^{-1/2}\), and the same bound for \(\bar q_e=\pi q_e\). This pays the otherwise missing initialization-only terms.

For clock terms, merge the root lists of the at most K independent histories by their greatest remaining root length. Comparability by κ makes the chosen current root comparable to that maximum. Earlier projected endpoints on its own path are now in the past; data on other independent histories may be exposed first. Project an earlier raw coefficient while later insertions are still raw, using \(c_l=C_l+q_{end}C_{l-1}\). Only then compensate the final differentiated root. A previously computed drift is not reconditioned as though it were predictable.

For a last raw root of length z and order l, the forward representations have costs

\[
 L^2:n^{-1/2}z^{l/2-1/4},\quad
 L^4:n^{-1/4}z^{l/2-3/16},\quad
 L^1:n^{-1/2}\max(z^{1/2},z^{l/2-5/4}),
\]

up to n^(C_Kβ). These bound representations inside expectation, not absolute raw scores. With no positive-order earlier C factor, l<4 saves a power; for l=4 split at z=Tn^−ε₀, ε₀=10^−4. The short case gains n^−3ε₀/4 and the long case gains n^−0.001 by the late raw L¹ estimate.

If earlier C factors have total order p and greatest length D, the L²/supremum allocation gives

\[
 n^{C_K\beta}D^{p/2-1}z^{l/2-1/4}T^{-3/4},\quad z\le C D.
\]

For total order four, D=Tx and z=Ty yield respectively
\((y/x)^{1/2}y^{3/4}\), \(y^{3/4}\), \(x^{1/2}y^{1/4}\) for (p,l)=(1,3),(2,2),(3,1). If either length is short, comparability yields at least n^−ε₀/4. Otherwise all earlier roots in this allocation are in the late range. When l≥2 the final raw L² improvement applies. For l=1, an earlier order two or three supplies n^−0.001, with length substitution costing at most n^(ε₀/2). If the earlier orders are (1,1,1), use four L⁴ factors: three late C₁ gains and a last cost \(n^{-1/4}T^{5/16}=n^{-1/24}\). Lower total orders save a power, higher ones fit T^((k−4)/2). Three complete legs only change fixed constants and the O(log n)^K counting factor.

### 3.3 Cutoff marks, terminal Gibbs denominator, and depth

The exact pre-density ratio remains

\[
 \frac{\bar k_I^v}{\bar k_I}
 =(1+v\bar q_e)\,\mathsf C_I^{x,y}\left[
 \frac{L_{I,e}(v)}{1+vq_e(y)}
 \prod_{J\subsetneq I}\frac{w_J^v}{w_J}\right].
\]

The denominator πᵛ(y) in the definition of a density accounts for both endpoint factors. At a terminal slot, with no descendant receiving positive cutoff order, the coefficient is \(C_r(I)+\bar q_e C_{r-1}(I)\). Separating the terminal denominator by absolute values would lose the guaranteed positive-order conditional factor and is not what I41 does. The \(\bar q_e\) factor may be assigned length T: its static norms satisfy the requisite C₁ bounds, including the late L⁴ improvement.

A mark ratio is at most \(C n^\eta\lambda_I/N_I\), where λ=1−w for a survival mark and λ=1 for a failure mark. For survival, very small w is paid by its included base survival factor before the sharp ratio is used. For a tested whole history,

\[
 \mathbb P_{test}\left(\sum_{I\in\mathscr S}(1-w_I)>h\right)
 \le n^{B+M}e^{-h}.
\]

This uses \(\prod w_I\le\exp[-\sum(1-w_I)]\) and remains true over all three legs at once. Every resampled marginal has the same estimate. For at most P+K marks, the indexed prefix tree has n^O_K(P) possibilities; choose the exceptional probability after P. At each shared sampled prefix the sum of λ_I times a continuation is bounded by the hazard sum times the supremum of that continuation with the same N_I^−1 retained. The gain is not multiplied by a raw number of nodes. All compensation identities precede restriction to this future-dependent hazard event.

The positive Taylor orders of active slots sum to at most K=24. Marks transfer orders and do not increase that sum. Consequently the coarse exponent C_cr for unexpanded positive-order slots depends on K and the fixed three-leg geometry, **not on P**. A long chain of scalar marks contributes constants depending on P, not extra positive-order moments or a new n-exponent C_cr(P). The depth remainder is

\[
 C_{K,P}n^{C_{cr}-P\beta+2(P+K)\eta}.
\]

Choose β small after the fixed local/mass constants, then P>(C_cr+3)/β, then η≤β/[4(P+K)], then all precision orders. Fixed combinatorial factors and logarithms are absorbed for sufficiently large n. The remainder is ≤n^−2; if a smaller additive precision is desired P may be increased with the same depth-independent C_cr. Only at most K final positive-order factors incur score losses C_Kβ. This verifies the order of choices; it does not hide a condition βC(P)<a after P≈1/β.

### 3.4 Fully expanded marked terms and the exceptional (3,1) case

Let m be the shortest marked-node length, capped at T. Partition only at ancestors needed to isolate marks. Every resulting piece is at least a constant times m except untouched smaller roots of the final stopped forest. A new complete earlier leg cannot be such a root: choose the exception constant below c₀ and κ. Every exceptional root occurs after every mark on its own original path. Copies begin at marked nodes and have no smaller untouched original root.

Select a terminal C factor from the indexed monomial. Its assigned length is at least m. The low-order Hölder allocations are: up to four C₁ in L⁴; C₂ with up to two C₁ in L²,L⁴,L⁴; two C₂ in L²; singleton C₃ in L¹ at cost D₃^−1/4; singleton C₄ in L¹; and C₃C₁ in L²,L² at cost (D₃/D₁)^1/2. All but the last cost at most a constant. These are all partitions of positive order ≤4; endpoint factors have magnitude at most one.

If D₁≥cm, retain the shortest-mark gain \(n^{-\beta}(m/T)^{3/2}\). It absorbs (T/m)^1/2 in the regular (3,1) case, leaving m/T; all other patterns leave (m/T)^3/2. After hazard/log losses, m≤Tn^−ε₀ thus gives a fixed saving.

For a raw order-one untouched root of length z<cm paired solely with a terminal C₃, its endpoint is **not** revealed. Its C₃ factor and all same-path mark endpoints precede the root. Conditional copies at those endpoints can be sampled before it with the same sampling kernel under reference and tested laws. Factors on other original histories are independent and their tests factor separately. Later external endpoint tests on this path stay inside the tilted intensity, not in the predictable multiplier. Thus forward compensation is admissible and gives

\[
 |C_3(D_3)|_2\,n^{-1/2}z^{1/4}
 \lesssim_\beta(D_3/T)^{1/2}(z/T)^{1/4}\le Cn^{C_K\beta}.
\]

There is no divergent (D₃/z)^1/2. The shortest-mark gain again pays the short-m case. This is the exact filtration point most at risk in a three-leg extension, and it survives because complete extra legs are earlier complete roots; no extra future information is exposed.

If m≥Tn^−ε₀, the selected terminal factor is late. C₁,C₂,C₄ supply their respective local gains; a singleton C₃ saves T^−1/4 n^(ε₀/4). For regular (3,1), put δ₀=0.005. If D₃≥Tn^−δ₀ the gain is n^−0.001+ε₀/2=n^−0.00095; otherwise the length ratio gains n^−(δ₀−ε₀)/2=n^−0.00245. For the reserved raw small root the same two branches gain n^−0.001 or n^−δ₀/2. There are positive margins in every allocation before C_Kβ is chosen. The source value a=10^−7 is conservative.

For k>4, an order ≥4 uses L¹ and saves two T powers relative to its supremum; a 3 pairs with a 2/3 in L² or two 1s in L²,L⁴,L⁴; two 2s, a 2 with two 1s, or four 1s give the same two-power saving. The leftover (3,1) costs at most T^1/2 and is allowed when k≥5; a singleton 3 is bounded by one. Unused factors use supremum norms. Thus the original form of (10) follows, including the T^((k−4)/2) and T^(k/2) bounds. No three-leg-only allocation remains unaccounted for.

### 3.5 Mass, survival, localization, replacement, and tightness

For the full stationary query, the four boundary spins under the checked subprobability are dominated by \(\exp(Cn^\beta)\pi^{\otimes4}\), by the three top caps and the initial π. At a dyadic scale comparable to c₀T, each of the two pair-tail events costs \(\exp(-c n^{3\beta})\). Off their union, each overlap q is ≤Cn^(2β). Therefore

\[
 \mathbb E_\pi[|q(X_0,X_t)q(X_{t+2u},X_{2t+2u})|\prod w_I]
 \le Cn^{4\beta}+2n^{2/3}e^{Cn^\beta-cn^{3\beta}}.
\]

This is a product-Gibbs domination argument, not independence of four actual observations. Crucially it bounds each signed-part base mass by n^O(β), rather than n^(2/3). With at most 24 mass factors, its exponent cost is at most 96β before other fixed constants. Enlarging the source C_K by that fixed amount and choosing β afterward preserves the fourth-order margin.

Gaussian survival uses the row-uniform warming log-tail bound for all node lengths 1≤D≤C₀T and all starting spins. There are O(T) nodes; choose its fixed log-moment order after query-grid size and the desired precision. Consecutive legs have arbitrary starting marginals, but the row bound already covers those. First-failure masses are positive and telescope; their unneeded future integrates to one, since the loss query has endpoint test one, not the signed overlap product.

Localize by the static cutoff times \(\chi(n^{10}\sum_q\mathrm{loss}_q)\). On derivative support the summed losses are ≤2n^−10. Differentiated loss factors cost their base masses; after summation, each n^10 factor is paid by \(n^{10}\sum_{q,I}\mathrm{loss}_{q,I}\le2\). Trace factors use the preceding n^(4β) estimate. Small-mass and exceptional precisions are chosen after polynomially many queries and nodes and n^(10K). The static cutoff has the same deterministic support as before. This proves I41 (12) for every disorder matrix, not merely almost surely under either pure entry law.

For completeness, in the iid mixture interpolation expand each entry about an independent mixture completion V. Conditional proposal moments match through order three, even though the expansion center is V. The completed matrix has the full mixture distribution when the edge is averaged, so the averaged derivative bound really applies. Order four costs n^−a₁; for 5≤k<24 the exponent is

\[
 2-k/2+\delta+(k-4)/3=-(k-4)/6+\delta<0,
\]

and the global order-24 remainder has exponent 2−24/6+δ=−2+δ. The mixture tail beyond log n is negligible against the global polynomial derivative bound. This step requires the preceding deterministic support construction and does not follow from a pure-Gaussian derivative estimate alone.

Taking the test equal to one gives \(\mathbb E(1-G_{cut})\to0\) for both laws, hence high probability of the cutoff. On its positive support the **quenched** error in each four-time integral is at most \(n^{2/3}\mathrm{loss}_q\le2n^{2/3-10}\). Bounded smooth joint tests in H and A can therefore be compared after removing the cutoff. This is stronger than comparing their annealed means.

There is an entirely deterministic time mesh bound. Write the four-time expression as the n²-term operator product
\(n^{-4/3}\sum_{i,j}\pi[M_iQ(t)M_iQ(2u)M_jQ(t)M_j1]\).
Each M is multiplication by a spin and has supremum norm one; each Q is a contraction. Differentiation in t inserts TL in either outer leg and differentiation in u inserts 2TL in the middle. Since \(\|L\|_{\infty\to\infty}\le2n\), the sum of the two partial derivative bounds is ≤8n^(7/3). For A² the bound is ≤4n^(7/3). A mesh n^−4 therefore has error O(n^−5/3). Its points and pairs have polynomial cardinality.

Use signed linear forms ±y_q and ±(y_q−y_q′), with coefficient ℓ¹ norm at most two, in softmax with parameter (log n)². Its approximation error is O(1/log n), and its jth derivative's total coordinate absolute sum is O_j((log n)^(2j−2)). Bounded smooth scalar threshold functions hence satisfy the original test contract. For fixed modulus radius and threshold, comparison transfers Gaussian modulus and supremum bounds on the grid; interpolation extends them to the rectangle. The radius is sent to zero after n. This proves tightness, not just finite-dimensional comparison.

On the Gaussian representation, the strong G family in §2 and varying-time strong semigroup operation imply strong \(Q(u_n)G_{n,t_n}\to S_u^gG_t^g\) for any \((u_n,t_n)\to(u,t)\) in the rectangle. Squared norms converge. Compactness gives uniform convergence of their scalar profiles and a continuous limit. Joint convergence with A follows on this same representation. Thus H converges to R_g+A_g², jointly with A. Tightness and the transferred finite-dimensional laws identify the Rademacher pair; the continuous map \((H,A)\mapsto(H-A^2,A)\) proves R exactly as stated.

**Verdict on R: PASS ORIGINAL WITHOUT REPAIRS.** The audit has paid the new endpoint and root-count costs explicitly. It does not invoke a theorem for arbitrary many legs, an n-dependent number of replicas, or an escaping horizon.

## 4. Density and path representations

Fix any finite J, let \(z_\pm=\nu e^{\pm H}\), \(w_0=\nu/\pi=z_+e^{-H}\), r=sT, and \(w_s=P_rw_0\). Detailed balance gives \(\rho_r=\nu P_r=\pi w_s\). Consequently

\[
 D_J(s)=\pi w_s^2
 =\sum_z\frac{\rho_r(z)^2}{\pi(z)}
 =\mathbb E_{\nu\otimes\nu}\frac{\mathbf1_{X_r=Y_r}}{\pi(X_r)}
 =\langle w_0,P_{2r}w_0\rangle_\pi
 =z_+\mathbb E_\nu e^{-H(X_{2r})}.
\]

The two forward paths in the collision formula are independent before weighting. Their collision midpoint after weighting has law \(\pi(z)w_s(z)^2/D_J(s)\). This is not π, ν, or ρ_r in general.

Let m=E_νe^−H(X₂r)=D/z₊ and tilt the single marked path by e^−H(X₂r)/m. Its initial marginal is \(\nu(x)P_{2r}e^{-H}(x)/m\), which integrates to one and is generally nonuniform. The midpoint marginal is
\(\rho_r(z)P_re^{-H}(z)/m=\pi(z)w_s(z)^2/D\).
Marked detailed balance gives a forward/reversed likelihood ratio e^(H(end)−H(start)); the terminal weight cancels it exactly, including at self refreshes. Given the midpoint, the two outward half histories are independent, each tilted from its ordinary law started there by w₀ at its endpoint and normalized by P_rw₀(z). Their final spins are not independent uniform spins. These derivations validate the original marginals, rather than deducing them just from equality of total masses.

For a coefficient θ_e, the ordinary marked-path score is
\(S_e=\sum_{\text{rings at }i,j}(\mathrm{new\ sign}-\tanh h_{site})\mathrm{other\ spin}\).
Poisson clocks have parameter-independent rates, and uniform initialization has score zero. Differentiating z₊ contributes πq_e; differentiating the terminal weight contributes −q_e(X₂r). Therefore

\[
 \partial_{\theta_e}\log D=\pi q_e+
 \mathbb E_{\mathsf M}[S_e-q_e(X_{2r})].
\]

The normalized path-density score itself is \(S_e-q_e(X_{2r})-\partial_{\theta_e}\log m\), whose mean is zero. This distinction avoids a missing-normalizer error in (8). At finite n, bounded mark derivatives and Poisson exponential moments justify differentiation. Writing \(h_v=P_{2r-v}e^{-H}\), the tilted mark intensity is \(r_{i,\zeta}(x)h_v(x^{i,\zeta})/h_v(x)\). It changes ordinary transition intensities and the initial law; its future dependence is represented by the Doob factor. No source polynomial-density/action bound has been established for this exponential tilt.

For the symmetric conjugation, \(H(x^i)-H(x)=-2x_ih_i\), so
\(e^{H(x)/2}c_i(x)e^{-H(x^i)/2}=1/(2\cosh h_i)=a_i(x)\).
The diagonal stays −Σc_i. Thus \(S=e^{H/2}Le^{-H/2}=L^a-U\), \(U=\sum_i(c_i-a_i)\), and with v=e^−H/2,

\[
 D=z_+\langle v,e^{2rS}v\rangle_\nu
 =z_+\mathbb E_\nu^a[v(Y_0)v(Y_{2r})e^{-\int_0^{2r}U(Y_l)dl}].
\]

The auxiliary rates a_i are symmetric under the relevant flip. U is real and bounded for finite n, so the finite-state Feynman–Kac formula applies, but U need not be nonnegative. For two spins, θ=log2 gives flip rates 1/5 aligned and 4/5 antialigned, a=2/5, and U=−2/5 or 4/5. The centered spin product has eigenvalue −2. The density excess has squared norm 9/16, whence D=1+(9/16)e^−4r. All signs and factors in the original (9) check. Dropping the exponential would be an invalid upper bound. Spectral nonpositivity alone yields only 1≤D(s)≤D(0)=z₊z₋ and monotonicity.

For initial annealed Rademacher mass, expand z₊z₋ over x,y and set r_i=x_iy_i. A same-sign r-edge cancels; a crossing edge contributes cosh(2/√n). Summing the gauge x gives

\[
 \mathbb E_JD_J(0)=2^{-n}\sum_{k=0}^n{n\choose k}
 \cosh(2/\sqrt n)^{k(n-k)}.
\]

For even n retain k=n/2, use \({n\choose n/2}\ge2^n/(n+1)\), and integrate \(\tanh x\ge x-x^3/3\) to obtain \(\mathbb ED(0)\ge e^{n/2-1/3}/(n+1)\). For Gaussian entries the edge factor is e^(2/n). These are annealed statements at s=0 only. Monotonicity gives no positive-time lower bound, and a growing mean alone gives no failure of quenched tightness.

**Verdict on the representations, score, conjugation, and enumeration: PASS ORIGINAL WITHOUT REPAIRS.** The unresolved assertion is an upper tightness bound on their positive-time weighted mass, not any of these identities.

## 5. Entropy criterion and countermodel

For a density w with πw=1, the entropy variational inequality applied to |h|/λ gives

\[
 |\pi wh|\le\pi w|h|
 \le\lambda\{\operatorname{Ent}_\pi(w)+\log\pi e^{|h|/\lambda}\}.
\]

Markov Jensen makes entropy nonincreasing under the reversible dynamics. With h=Q(u)G_t and v=s−u≥s₀, self-adjointness identifies πw_vh=B_n(s,t)−A_n(t). Put
\(K_n(u)=\sup_t\inf\{\lambda>0:\pi e^{|Q(u)G_t|/\lambda}\le2\}\).
For every λ>K_n(u), the same bound holds for all t; let λ decrease. If K=0 the function is zero π-almost everywhere and the result still holds. Hence

\[
 \sup_{s\ge s_0+u,t}|B_n-A_n|\le K_n(u)\{H_n(s_0)+\log2\}.
\]

Tight H and \(\lim_{u\to\infty}\limsup_n\mathbb P(K_n(u)>\epsilon)=0\) suffice by a deterministic threshold split, with no independence assumption. Both inputs remain unproved for Rademacher SK. A bound on every fixed moment is not a bound on the exponential norm with uniform constants. **Entropy criterion: PASS ORIGINAL WITHOUT REPAIRS, as a sufficient criterion only.**

For the countermodel, set p=2^−m, q=1/m. A coordinate refresh at rate α/m sends its rare-state probability to p+(q−p)e^−αs/m. Use independent coordinates with α=1,2 and f=m(1_{x=1}−1_{y=1}). The stationary probability is the product of the two stated m-state laws. Refresh generators are reversible and irreducible, and the initial law is uniform on the full m²-state space. Directly,

\[
 \rho_sf=(1-mp)(e^{-s/m}-e^{-2s/m}),\qquad
 P_uf=m[e^{-u/m}(1_{x=1}-p)-e^{-2u/m}(1_{y=1}-p)].
\]

The centered indicators are independent under π, with variance p(1−p), yielding the original profile formula. Every fixed stationary absolute moment of f is \(2m^kp(1-p)\to0\); Markov contraction gives the same fixed-moment convergence after evolution. The compact-s expectation tends uniformly to zero, but at s=m log2 it tends to 1/4. For each fixed S, that time is eventually ≥S, so the late supremum fails. This is a genuine moving-time counterexample.

For one coordinate the relative entropy from the uniform law is exactly
\(q\log(q/p)+(1-q)\log((1-q)/(1-p))\le\log2\).
The second term is nonpositive because q≥p, and the first is \(\log2-(\log m)/m\). Product entropy and data processing give the uniform 2log2 bound at all times. In contrast, each evolved coordinate's density-square norm is
\(1+(q-p)^2e^{-2\alpha s/m}/[p(1-p)]\), so the product density norms diverge at every fixed s. On m=2^k, the uniform start is exactly independent fair bits under a bijection with 2k bits. The transitions refresh a block, not each spin with SK rates.

The tail failure persists at every fixed u, which is the order needed in the entropy criterion: on \(\{x=1,y\ne1\}\), whose π-mass is p(1−p),
\(P_uf=m[e^{-u/m}+p(e^{-2u/m}-e^{-u/m})]\).
Its ratio to m tends to one. Thus for every fixed λ<1/log2,
\(\pi\exp(|P_uf|/\lambda)\to\infty\).
In particular the limit inferior of its exponential norm is at least 1/log2 for every fixed u; the outer u→∞ cannot make it vanish. At u=0 this is exactly the original closed formula \(1+2p(1-p)(e^{m/\lambda}-1)\). This explains the mismatch between all fixed moments and the required exponential tails.

The one-point visible limiting space is ergodic and f has strong limit zero; no statement about convergence of the entire hidden state space is required. The countermodel neither has the SK generator nor asserts that f is an SK autocorrelation F. It refutes the generic inference that these observable profiles and bounded fair-start entropy suffice for uniform late pairing relaxation. **Countermodel: PASS ORIGINAL WITHOUT REPAIRS in precisely that scope.**

## 6. Remaining obligation and evidence reproduction

With R validated, the remaining C-route sufficient estimate is: for some fixed s₀>0, the Rademacher random variables

\[
 D_J(s_0)=z_+\mathbb E_\nu^J e^{-H_J(X_{2s_0n^{2/3}})}
 \quad\text{are tight as }n\to\infty.
\]

Equivalently, for every ε>0 there is finite M with \(\limsup_n\mathbb P(D_J(s_0)>M)<\epsilon\); D=1+L². No n-dependent burn time, n^o(1) upper bound, raw endpoint exponential query, or kernel-log cap exp(Cn^β) pays this. The entropy/Orlicz route has two separate unpaid inputs. These are sufficient routes, not necessary characterizations of W. This review stops at that exact obligation.

The independent diagnostic checks all first-failure prefixes for five unequal three-leg trees, root comparability and the small-root/mark order; marked finite-path score differentiation and normalization; tilted initial and midpoint marginals; discrete Doob normalization; the normalized Gibbs denominator in a perturbed conditional-kernel recursion; continuous-time density Taylor coefficients through order eight; and the borderline/replacement/mesh exponent arithmetic. It has **1,310 exact assertions**, using rational arithmetic only. Discrete paths test marked-path algebra, not transcendental matrix exponentials; continuous-time claims are proved above and their Taylor identities are separately checked. The diagnostic does not certify local analytic source bounds or the theorem by sampling.

The unchanged I41 diagnostic reproduces its 2,846 assertions and its 3,285+389 replays. The original I41 verifier, run directly, now **fails** at `README.md`: post-integration shared ledgers have changed. Four live differences are retained in `observed-live-drift.json`: `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md`. The first two were marked immutable by I41; their recorded diffs are status/history prose, not mathematical premise edits. This discrepancy is not concealed or relabeled as an unchanged vanilla verifier PASS.

For a reproducible frozen-baseline replay, the I42 verifier executes the unchanged I41 verifier with a read-only byte view substituting **only those four exact live ledger paths** by their existing I41 frozen bytes. It does not modify verifier code, author files, or seals, and it reports the substitution explicitly. All other live reads remain live, including every artifact and corpus file. This replays the 238-artifact I41 seal, its 174 frozen inputs, 258 I39 and 237 I40 artifacts, all 9,340 corpus files against the 13,223-entry/749-manuscript tree, source/read contracts, retained primary responses, and searches. Current mutable drift is reported separately. The raw failed run is retained in `i41-reproduction.json`.

Three fresh primary raw responses for QU §7/8/9 returned HTTP 200 and match the pinned corpus byte hashes. A browser lookup of the same pinned replacement source is retained. No new current-literature absence or priority claim is made; I41's literature records are frozen evidence, not an assertion that a worldwide literature audit was repeated. The complete corpus is inventoried with `rg --files --no-ignore`; only the recorded relevant passages are claimed read.

Run from the work root:

```bash
python -B frontier/experiments/i42_four_time_profile_r2/check.py
python -B frontier/experiments/i42_four_time_profile_r2/verify.py
```

The I42 one-time seal binds this report, its 370 frozen input files, read passages/contracts, primary bytes, scripts, diagnostics, replay record, and ledger-drift record. The verifier is read-only and never refreshes a seal. Evidence integrity and finite diagnostics remain distinct from the independent analytic verdicts above. The parent integrates; full W remains unproved/unrefuted and the substantial count remains six.
