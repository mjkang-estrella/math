# I41 — Rademacher fair-start warming: audit and constructive follow-up

**Disposition: developed gap, with a completed technical four-time comparison. Full W for both disorder laws remains unproved and not refuted.** My independent analytic verdict on I40's Gaussian theorem G, criterion C, four-time identity, and entropy-spike obstruction is **PASS ORIGINAL WITHOUT REPAIRS** under the stipulated pinned source operations. The new three-leg comparison below pays clause C(ii). It does not pay C(i). Two constructive approaches are developed: a normalized reversed-history/two-copy representation of fair-start density, and finite-horizon observable comparison followed by an entropy/Orlicz attempt. The latter also produces an explicit fair-uniform-start reversible countermodel to replacing C(i) by tight entropy, even with convergence of every fixed observable moment. It is not an SK counterexample.

G and the new comparison are technical deductions, not substantial nominations. No acceptance, count change, independent significance acceptance, worldwide-priority claim, commit, staging, agent launch, or publication occurs here. The parent decides on further reviews and integration. All writes are confined to the three I41 destinations. Earlier reports and seals are preserved.

## 1. Exact problem, controls, and source scope

For independent Gaussian N(0,1) or independent fair-sign unordered couplings J_ij, put

ℋ_J(x)=n^(-1/2) Σ_(i<j) J_ij x_i x_j,
π_J(x)=exp(ℋ_J(x))/Σ_y exp(ℋ_J(y)),  ν_n(x)=2^(-n).

There is no field and beta=1. Each site refreshes from its conditional Gibbs law at rate one. Write T_n=n^(2/3), Q_n(s)=P_(sT_n), q_n(x,y)=n^(-2/3)x·y,

F_(n,t)(x)=n^(-2/3)Σ_i x_i Q_n(t)x_i,
A_n(t)=π_J F_(n,t),  G_(n,t)=F_(n,t)−A_n(t),
B_n(s,t)=ν_n Q_n(s) F_(n,t).

Thermal randomness is already integrated. W requires, **for each of both disorder laws**, every 0<a<b<∞ and η>0,

lim_(S→∞) limsup_(n→∞) P_J{sup_(s≥S,t∈[a,b]) |B_n(s,t)−A_n(t)|>η}=0.       (W)

The waiting supremum is unbounded before n tends to infinity. No n-dependent S, stationary-lag substitution, changed initialization, temperature slack, or exchange of these limits is allowed. In total site-attempt units the scale would be n^(5/3); all formulas here use per-site clock units. The exclusion of t=0 is necessary since A_n(0)=n^(1/3).

All theorems **and actual proof operations** at openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are accepted premises. QU denotes *Universality of critical quench autocorrelations in the Sherrington–Kirkpatrick model*, October 5; FU denotes *Functional universality of critical SK autocorrelations*, October 5; CM denotes *Critical mixing in the Sherrington–Kirkpatrick model*, September 25. Exact paths, pinned raw URLs, Git blobs, SHA-256, theorem labels, read ranges, and excerpts are in the I41 source manifests.

I read I39 and I40 in full and searched the entire frozen prior-report inventory for SK, quench, warming, waiting-time, and strong/weak-convergence issues. I17's different-temperature free-energy question is not repeated. The I30/I36 reduction standard and I38/R011 significance decisions remain controlling: an absent verbatim statement does not make a deduction substantial. The existing counts and publication authorization are inherited history, not decisions made here.

Source coverage includes QU's entire warming, Gaussian-limit, checked-history, clock-score, and replacement sections; FU's conditioned-measure/replica passages, full gradient-form proof, and actual recovery/positivity/divergence/relaxed-energy proofs. In particular, I used the whole two-copy overlap tail, not a divergent sum of coordinate variances; restricted relaxed-energy liminf plus bounded resolvent optimizers, not arbitrary low-mode compactness; and the normalized, conditional-copy history derivatives, not a formal application of two-point universality to four endpoints. CM's exponent slack and its sqrt(log n) minimum observation dimension do not supply tight critical-time constants. Gaussian diagonal completion does not give a Haar frame for Rademacher off-diagonal entries.

Early current primary searches, exact requests/responses and versioned PDFs are retained. The complete 13,223-entry, 749-manuscript inventory and all 9,340 corpus files are reused with hashes and Git-blob verification; the 719-entry catalogue is not the denominator. The entire corpus is searched, not claimed read. Selection and actual reading are recorded separately.

## 2. Independent audit of I40, without repairs

### 2.1 G: products, tails, events, and the infinite waiting interval

The audit starts with the finite exact identity, independent of the auxiliary Gaussian diagonal and eigenvector signs,

F_(n,t)=Σ_a x_(a,n) Q_n(t)x_(a,n),   x_(a,n)=n^(-1/3)〈u_a,x〉.

For T_(n,m)(x,y)=Σ_(a>m)x_(a,n)(x)x_(a,n)(y), define V_(n,m)=(π⊗π)T_(n,m)^2. QU `glim:static-tail` really asserts lim_m limsup_n V_(n,m)=0 almost surely on a further representation. Its proof cancels both Gibbs denominators with L_circ² before its Haar integration, inserts the whole squared projected overlap, bounds the overlap-cell error uniformly in m, and only then uses spherical sign symmetry. On the cube the cross terms are retained. Equivalently V_(n,m)=Σ_(a,b>m)(πx_a x_b)², so it decreases in m. This validates the further extraction rather than asserting almost sure tails from convergence in probability alone.

At positive lag, conditional Jensen has its full Markov mass one:

||Σ_(a>m)x_a Q_n(t)x_a||_2²
≤∫p_(n,t)(x,y) T_(n,m)(x,y)² dπ(x)dπ(y)
≤K(a)V_(n,m),  t≥a.                                                     (1)

No sign of the tail sum is used. The limiting kernel and `glim:limit-static-tail` give the same estimate for finite tail intervals, hence a Cauchy series in L² uniformly on [a,b]. K(a) is bounded on the represented sequence for all sufficiently large n; the vanishing warming threshold is below a then. This is a legitimate strengthening of the source's scalar pairing estimate.

For each fixed head coordinate, FU's **polynomial-growth** static convergence gives convergence of its fourth moment, of its second moment, and of its pairings against bounded cylinders. Thus x_(a,n) converges strongly. QU `glim:semigroup-strong` yields Q_n(t_n)x_(a,n)→S_t x_a strongly for t_n→t>0. The kernel gives a common supremum bound K(a)π|x_(a,n)| on the evolved factor. Multiplying it by a bounded smooth clipped coordinate preserves strong convergence: approximate the evolved factor by the same bounded cylinders on both spaces, bound the multiplication error by the clip's supremum, and pass the cylinder product statically. The omitted unbounded product has norm at most

C K(a)π|x_(a,n)| (π[x_(a,n)² 1_(|x_(a,n)|>R)])^(1/2) ≤ C_a/R.

Thus first n→∞, then R→∞, then m→∞ in (1) proves strong F_(n,t_n)→F_t. Centering is legitimate because the constant function is a common strong test. This proves strong G_(n,t_n)→G_t and compactness/continuity of {G_t:a≤t≤b}. No independence between the coordinate and its evolved value was assumed.

For all initial probability laws ρ, QU warming at any fixed s0>0 holds on **one common event**, and gives 0≤w^ρ_(n,s0)≤K(s0), πw=1, and ||w−1||_2≤sqrt(K(s0)−1). This is an all-law pointwise kernel conclusion, so taking a supremum over disorder-dependent ρ does not cost a union bound. Reversibility and L² contraction then give, for S>s0,

sup_ρ sup_(s≥S,t∈[a,b]) |B_n^ρ(s,t)−A_n(t)|
≤sqrt(K(s0)−1) sup_t ||Q_n(S−s0)G_(n,t)||_2.                              (2)

Only the burn s0 and the fixed lag window are bounded away from zero. There is no replacement at an escaping time. For every fixed integer S>s0 the right-hand profile converges, by strong-input semigroup convergence and the sequential compactness of [a,b], to sup_t||S_(S−s0)G_t||_2. FU `prop:gradient-domain` proves the closed form kernel is exactly constants, and `lem:micro-positivity` gives c_*>0; hence each centered G_t decays under S_u. A finite L² net and contraction make that decay uniform in t.

For a precise subsequence test of the disorder quantifier, suppose the double limit in G failed. Choose n_k→∞ and S_k→∞ with a fixed positive lower failure probability. On a further represented subsequence include the countable integer-S profiles, tail errors, head moments, and tight warming constants. For each fixed S, eventually S_k≥S, so the event at S_k is contained in the one bounded by (2) at S. Portmanteau bounds its limsup by the probability that the limiting bound is **at least** η. This tends to zero as S→∞ because K(s0)<∞ almost surely. This contradicts the lower probability. This spells out, and does not repair, I40's offending-subsequence paragraph. Alternatively localize tight constants at fixed confidence, pass n before the head/cutoff limits, and exhaust the confidence events. Auxiliary diagonal marginalization is valid since both sides of G depend only on off-diagonal entries.

Measurability causes no extra supremum issue: at finite n the initial-law supremum of the absolute linear functional occurs at a point mass, and rational s,t suffice by continuity. The all-s supremum follows from contraction before taking limits. The source's restricted liminf was invoked only on bounded resolvent optimizers, as in its proof, and was never converted into a whole finite spectral gap.

**Audit verdict on G: PASS ORIGINAL WITHOUT REPAIRS.** G remains technical under the existing operation-level reduction. This audit does not grant it a new significance status.

### 2.2 C, centering, the four-time identity, and both countermodels

For any finite reversible chain and this F, conditioning a stationary trajectory on X_t and reversing its first leg gives E[q(X0,Xt)|Xt]=F_t(Xt). Conditioning its final leg gives the other F_t. Therefore

E_π[q(X0,Xt)q(X_(t+2u),X_(2t+2u))]
=〈F_t,Q(2u)F_t〉_π,
R_n(u,t)=||Q_n(u)G_(n,t)||_2²=the preceding expectation−A_n(t)².            (3)

The middle interval is 2u, not u; the whole trajectory lasts 2t+2u. This is one three-leg path, not independent replicas. The term A² is required. Consequently R_n≥0 and decreases in u, even though the path endpoint product is signed.

If L_n=||w_(n,s0)−1||_2 is tight and R_n(u,·)⇒R_g(u,·) in C[a,b] for every fixed u>0, then

P{sup_(s≥s0+u,t∈[a,b])|B_n−A_n|>η}
≤P(L_n>M)+P(sup_t R_n(u,t)>η²/M²).

After limsup_n, the second term is bounded by the limiting **closed** threshold event. Its probability tends to zero as u→∞ by the compact-family argument in §2.1. Then M→∞ pays the first term. Independence or even joint convergence of L_n and R_n is not required. **C passes as a sufficient criterion; no necessity or equivalence is proved.**

I reconstructed I39's eight-state product generator and I40's formulas. With flip rates 1/(2N),1/N,1/2, h0=1+(x−y)/4, f=z(1+x+y)/3, u=e^(−t/N), v=e^(−t),

fP_t f=(v/9)[1+u+u²+(1+u)x+(1+u²)y+(u+u²)xy].

The moving-time difference at s=N log2 tends to v/72. The hidden centered variance tends to 4v²/27. Retaining only z gives an ergodic visible limit but loses strong convergence of this observable; retaining x,y as well makes the limit nonergodic. Kernel bounds alone do not satisfy G's other premises. This is a valid model counterexample, not an SK one.

For the I40 spike, π(E)=m^(-3), ρ(E)=m^(-1), F=m1_E: πF=m^(-2), ρF=1, πF²=m^(-1), and D(ρ||π)≤2log(m)/m. The complement's density is below one, so dropping its negative entropy contribution is in the correct direction. The density square norm contains the divergent term m. Its use as an obstruction, rather than a purported SK law, passes. The new diagnostic uses a nonuniform Gibbs chain in addition to replaying I40; thus (3) is not checked only under uniform stationarity.

## 3. Attempt A: normalized fair-start collision and reversed histories

This approach is specifically for ν_n; it does not demand worst-start warming. In this section J is any fixed finite zero-field interaction matrix, and the identities do not use its disorder law. Set z_+=ν_n[e^ℋ], z_−=ν_n[e^(−ℋ)], w0=z_+e^(−ℋ), r=sT_n, ρ_r=ν_nP_r, and

D_J(s)=π[(Q_n(s)w0)²]=1+||w_(n,s)−1||_2².

### 3.1 A positive normalized representation, and its actual marginals

Two independent forward paths with uniform initial states, stopped at physical time r, give exactly

D_J(s)=E[1_(X_r=Y_r)/π(X_r)].                                             (4)

This is positive; it is a weighted collision, not the ordinary collision probability. Conditioning on the common endpoint z gives probability proportional to ρ_r(z)²/π(z). In particular its midpoint law is π(z)w_(n,s)(z)²/D_J(s). Removing this tilt would change the representation.

Reversibility and the semigroup property give the equally useful one-path formula

D_J(s)=〈w0,P_(2r)w0〉_π=z_+ E_(ν_n)^J[e^(−ℋ(X_(2r)))].                    (5)

Let M_(J,s) be the probability on a length-2r marked path obtained by weighting its uniform-start path law by e^(−ℋ(X_(2r))) and dividing by m_(J,s)=E_ν e^(−ℋ(X_(2r)))=D_J(s)/z_+. All clocks and self-resampling marks are retained. Marked detailed balance shows this probability is invariant under reversing the path: the ratio of forward to reversed ordinary likelihood is e^(ℋ(end)−ℋ(start)), which cancels the terminal weight. Its midpoint law is exactly the square-tilted law in (4), and, given that midpoint, its two reversed outward half-paths are independent with transition-path probability from z tilted by w0 at the terminal state and normalized by P_r w0(z). The terminal spins of those half-paths are **not** independent fair spins after the tilt.

This gives an explicit normalized two-copy/reversed-history representation with the correct marginals. It also explains why unweighted conditional-replica estimates cannot be inserted into it. The changing square tilt is the quantity needing control.

### 3.2 Cancellation of inverse normalizers does not cancel the size or score cost

There is no inverse partition function in (5). Nevertheless the factor at s=0 is exactly z_+z_−, rather than one. For Rademacher couplings, averaging over disorder gives the exact finite formula

E_J D_J(0)=2^(−n) Σ_(k=0)^n binom(n,k) cosh(2/√n)^(k(n−k)).               (6)

To derive it, expand z_+z_− using two independent uniform spins x,y and set r_i=x_i y_i. On an edge with r_i=r_j the exponent cancels; on a crossing edge its sign-average is cosh(2/√n). There are k(n−k) crossing edges. For Gaussian couplings the same formula holds with cosh(2/√n) replaced by exp(2/n). The normalization includes 2^(−n), not 2^(−2n), after summing the gauge spin.

For even n, the central term and binom(n,n/2)≥2^n/(n+1), with log cosh x≥x²/2−x⁴/12 for x≥0, imply

E_J D_J(0)≥exp(n/2−1/3)/(n+1)    (Rademacher),                            (7)

and exp(n/2)/(n+1) for Gaussian disorder. The log-cosh inequality follows by integrating tanh x≥x−x³/3; the latter has nonnegative derivative difference x²−tanh²x. Thus the normalization cancellation still leaves a genuinely exponential **annealed initial** mass. This is not a lower bound at any fixed s>0, or a failure of quenched tightness; it identifies what time evolution must remove.

The entry derivative is also exact. Differentiate in the physical coefficient θ_e=J_e/√n, keep the marked path fixed, and let

S_e(ω)=Σ_(rings at i or j) (new_sign−tanh h_site) · other_spin.

The uniform initialization has zero score. Differentiating (5) gives

∂_(θ_e) log D_J(s)=π(q_e)+E_(M_(J,s))[S_e−q_e(X_(2r))].                  (8)

All derivatives exist at finite n; Poisson exponential moments justify differentiating. Normalizing M is essential. Its density relative to the ordinary forward law is e^(−ℋ(end))/m_(J,s). Its supremum can be exponential, and its initial marginal is ν_n(x)P_(2r)e^(−ℋ)(x)/m_(J,s), generally nonuniform and disorder-dependent. The Doob transform has intensities r_(i,ζ)(v) h_v(x^(i,ζ))/h_v(x), with h_v=P_(2r−v)e^(−ℋ). These ratios are not the ordinary rates used by QU.

QU's compensated-score estimate pays a tested-law log-density of order log n. Applying its likelihood/Hellinger bound to the present density yields at best an order-n action on a bounded-operator-norm event, not the n^η action used for a saving at fourth derivative. Bounded normalized endpoint scores ±q_e in (8) do not control that path action. Higher derivatives produce conditional cumulants of the full score and terminal q_e; treating them as static replica derivatives discards the history dependence. Thus (8) is a real cancellation but not a verified universal replacement bound.

### 3.3 Symmetric Feynman–Kac form and a sign test

Write c_i(x)=exp(−x_i h_i)/(2cosh h_i) for the actual flip rate (self refreshes do not change the generator), and a_i(x)=1/(2cosh h_i). Conjugate the generator ℒ by e^(ℋ/2):

𝒮=e^(ℋ/2) ℒ e^(−ℋ/2)=ℒ^a−U,
ℒ^a f=Σ_i a_i(x)(f(x^i)−f(x)),  U(x)=Σ_i(c_i(x)−a_i(x)).

The off-diagonal a_i are symmetric under the corresponding flip, so ℒ^a is reversible for ν_n. With v=e^(−ℋ/2),

D_J(s)=z_+〈v,e^(2r𝒮)v〉_(ν_n)
=z_+ E_(Y0∼ν_n)^a[v(Y0)v(Y_(2r)) exp(−∫_0^(2r)U(Y_l)dl)].                (9)

This is a positive Feynman–Kac weight, but **not a killing representation with U≥0**. For two spins with θ=log2, an aligned state has c_i=1/5, a_i=2/5 and U=−2/5; an antialigned state has U=4/5. The exact density decay is D(s)=1+(9/16)e^(−4r). This checks signs, factors of two, and normalization in (9). It prevents an invalid upper bound obtained by dropping the Feynman–Kac exponential. The interaction in this diagnostic is a general two-spin model, not beta-one SK at that size.

Spectral nonpositivity of 𝒮 yields only 1≤D_J(s)≤z_+z_− and monotonicity of D in s. For an upper bound tight at fixed s, the required compensation is the quadratic matrix element in (9) reducing the extensive starting mass. The static sources supply no bound on that weighted evolution. Exact fair-spin gauge symmetry makes the annealed one-time spin marginal uniform, but says nothing about its correlation with the random inverse Gibbs weight in (4) or (5).

**Status of attempt A:** (4)–(9), their path marginals and the obstruction to nonnegative killing are proved. They improve the formulation and expose a concrete weighted-history estimate, but do not prove that D_J(s0) is tight for any fixed positive s0 under Rademacher disorder. Gaussian posterior/Haar estimates or a log-cap exp(C n^β) cannot be substituted for this missing estimate. No annealed upper bound is asserted; such a bound would be sufficient by Markov, but is stronger than the required quenched tightness.

## 4. Attempt B: completing the fixed-horizon four-time comparison

Here is a complete technical extension of QU's proof operations, submitted to the parent for a fresh check. Fix 0<a<b<∞ and 0<c<d<∞. Under Rademacher disorder,

R_n(u,t) ⇒ R_g(u,t)=||S_u G_t||_2² in C([c,d]×[a,b]),                     (R)

jointly with A_n on the required compact intervals. In particular this supplies C(ii). It neither proves nor assumes fair-start density control.

### 4.1 Three checked legs are admissible, with the same derivative savings

For H_n(u,t)=E_π[q_n(X0,Xt)q_n(X_(t+2u),X_(2t+2u))], use three consecutive complete legs of lengths tT, 2uT, tT, each with QU's binary checks. Every leg length lies in [c0T,C0T] for fixed positive c0,C0. The external endpoints are the four displayed states. The new endpoint test ζ is their overlap product; |ζ|≤n^(2/3), independent of the entry being differentiated. Use ζ+ and ζ− separately.

The following verifies the extension from the source's one/two-leg query class; it is not an assumption that its printed proposition already mentions three legs.

1. A first-failure prefix consists of at most two complete earlier legs followed by the binary-prefix forest in the failing leg. Earlier maximal roots still have length at least a fixed multiple of later ones. There are O(T) nodes and O(log n)+2 maximal roots. The geometric comparison of root lengths and the polynomial counts used by QU are unchanged, with constants depending on c0,C0 and the fixed number three.
2. Each node's transition, pre-density, top cap and conditional interior is exactly QU `hist:kernel-recursion` and `hist:bridge-definition`. Checks are laminar inside each leg and disjoint across legs. Conditioning the exterior, including the new leg boundaries, fixes the endpoint test. Resampling a node interior therefore preserves the tested marginal, even with its extra endpoint factors. This proves the conditional-copy contract and the reversed-prefix density bound for the enlarged class, with no conditioning on arbitrary rare endpoints for sharp bounds.
3. For any external test 0≤v≤n^B of mass z≥n^(−M), the forward tested density is at most n^(B+M). QU's Hellinger/action and Poisson-count estimates hold verbatim in that natural forward filtration. The extra final endpoints remain unrevealed; their tilt is included in the intensities. Within each root, the two/four-overlap proof keeps disjoint contained nodes, so its static-support bounds and polynomial-grid extension apply. Conditional copies preserve these root marginals. Small masses z<n^(−M) are discarded only after the coarse unnormalized coefficient bound n^(C_K)z, choosing M after the required precision.
4. QU `score:raw-projection` and `prop:clock-scores` use only these node/filtration/action/overlap properties. Their proofs, including earlier-endpoint projection **before** later compensation, midpoint cancellation, reversal, and the late improvements, consequently apply to every node of these three-leg histories. No new score is inserted at a leg boundary. A stationary history still has just one stationary initialization factor (1+u q_e(X0))/(1+u πq_e).
5. In `repl:history-derivatives`, the fixed-weight terms expand over the O(log n)+2 roots. Merge lists from independent histories in decreasing comparable-root order. The final differentiated root and every earlier projected root have exactly the same admissible law as above. The four borderline allocations (no earlier R, and orders (1,3),(2,2),(3,1)) use the same length inequalities. Adding one complete root changes the number of terms, not their powers. The small untouched root in the exceptional (3,1) allocation remains after all marked ancestors in its last forest; complete earlier legs cannot be smaller than a fixed multiple of T. Its terminal state is still unrevealed before forward compensation.
6. Differentiated cutoff marks use the same exact conditional-copy ratio, with the terminal Gibbs denominator kept together with the likelihood. Total positive Taylor order stays ≤K=24, independent of the number of marks. The tested hazard bound P(H>h)≤n^(B+M)e^(−h) applies to each whole three-leg history and every resampled marginal. The finite-depth stopping remainder is n^(C_cr−Pβ+2(P+K)η), just as in QU. Choose β small, then P>(C_cr+3)/β, then η≤β/[4(P+K)], then the arbitrary exceptional precision. Constants may increase for three legs, but neither C_cr nor C_K depends on the chosen depth P.

This gives, for products of at most K checked integrals with total derivative order k and base masses z_α, the **same form** of estimates as QU:

average_e |∏_α ∂_e^(j_α)Z_α|
≤C ∏_α z_α × {n^(−a0+C_Kβ) if 1≤k≤4;
                n^(C_Kβ)T^((k−4)/2) if 5≤k≤K} + n^(−A),
max_e |∏_α ∂_e^(j_α)Z_α|≤C n^(C_Kβ)T^(k/2)∏_α z_α+n^(−A).               (10)

Here ∂_e is in θ_e, a0>0 can be taken no larger than the source's 10^(−7), and A,B and time rectangles are fixed before n. Positive/negative tests have their own nonnegative masses. The preceding six checks identify every extra law/count/filtration issue introduced by the additional leg; the local source coefficient estimates are accepted operations, not re-audited upstream claims.

### 4.2 Endpoint mass, survival, and localized derivative bounds

On static support, the three top caps bound the four-endpoint subprobability by exp(C n^β)π^⊗4. The first endpoint already has law π. At a dyadic scale comparable to c0T, each of the two pair events |ρ_2|>r_2 has π^⊗4 probability at most exp(−c n^(3β)). On their complement each |q_n|≤C n^(2β). Consequently

E_π[|ζ|∏_I w_I]
≤C n^(4β)+2n^(2/3)exp(Cn^β−c n^(3β))≤C n^(4β)+n^(−A).                 (11)

This is the needed base-mass estimate. Using the crude n^(2/3) endpoint bound in place of (11) would destroy the tiny fourth-order saving and is not acceptable. It is enough to control two pairs here; no unjustified independence between the trajectory's four endpoints is used. The domination is a subprobability inequality followed by a product-Gibbs integral.

Gaussian survival follows by summing QU's row-uniform log-kernel-tail estimate over the nodes in all three legs. There are still O(T) nodes, so choosing its fixed log-moment order after the desired polynomial precision gives loss n^(−A) uniformly over this rectangle. First-failure masses are positive and telescope exactly; unneeded future after the failure integrates to one.

For polynomially many queries (allowing ordinary A queries as well), take Γ times the smooth cutoff of n^10Σ_q loss_q exactly as in QU. On the support of its derivatives, Σ_q loss_q≤2n^(−10). Loss derivatives use the positive first-failure masses; summed products multiplied by n^10 are ≤2 per factor. Equation (11) bounds trace mass factors by n^(O_K(β)). Combine this with (10) and smooth test derivative sums bounded by a fixed power of log n. For β small enough **after** K and the three-leg constants, the localized observable Φ has

average_e |∂_e^4Φ|≤n^(−a1),
average_e |∂_e^kΦ|≤n^δ T^((k−4)/2)  (5≤k<K),
max_e |∂_e^jΦ|≤n^δ T^(j/2)  (1≤j≤K),   0<δ<0.01, a1>0.                (12)

The static cutoff derivative bounds and support are unchanged. These bounds hold for every deterministic matrix; they are not asserted only for pure Gaussian or Rademacher matrices.

### 4.3 Replacement, quenched cutoff removal, and the time modulus

Use the iid mixture of Gaussian and fair-sign entries. The two proposals match through order three, so expanding at an independent mixture completion leaves the fourth term controlled by n^(−a1). For orders 5≤k<24 the summed factor is

n^(2−k/2+δ) T^((k−4)/2)=n^(−(k−4)/6+δ),

and the global remainder is n^(2−24/6+δ)=n^(−2+δ). Mixture tails beyond log n are smaller than every fixed inverse power and are paid by the global polynomial bounds. Thus the difference of the localized smooth-test expectations tends to zero uniformly along the interpolation. No horizon in this argument tends to infinity with n.

Taking the test equal to one transfers the high probability of the whole cutoff to Rademacher disorder. On its support,

|H_n−H_n^truncated|≤n^(2/3) loss_q≤2 n^(2/3−10).                         (13)

This removes the cutoff for the **random quenched expectation**, not just an annealed moment. Joint smooth tests in H and A identify their joint finite-dimensional laws.

For tightness use ||ℒ||_(∞→∞)≤2n and the exact three-leg kernel expression for H. A derivative of a leg inserts Tℒ. The endpoint sum has total absolute coefficient n^(2/3), each spin multiplication has supremum norm one, and each Markov kernel is a contraction. Thus |∂_t H|+|∂_u H|≤8n^(7/3); derivatives of A² are bounded by 4n^(7/3). A mesh n^(−4) has vanishing interpolation error O(n^(−5/3)). Grid cardinalities and all grid pairs are polynomial. QU's soft maximum with parameter (log n)² has derivative sums of logarithmic size and applies unchanged to supremum and modulus tests for the joint grid. Gaussian tightness transfers to Rademacher tightness exactly through (12)–(13).

Gaussian convergence of H itself follows from (3), §2.1's strong F/G family, and the strong semigroup uniformly for u in [c,d]. Its limit is R_g(u,t)+A_g(t)², continuous in both variables. Joint convergence and the continuous map subtracting A² now prove (R). Uniform lag comparison, first-failure survival, and quenched cutoff transfer have all been included. This is a fixed-horizon **technical extension**, not full W and not a new acceptance candidate.

## 5. Attempt B continued: can density control be bypassed?

### 5.1 Entropy duality supplies a distinct conditional route

Let H_n(s0)=Ent_π(w_(n,s0)). Suppose it were tight under Rademacher disorder. Markov Jensen implies entropy is nonincreasing, so it would be tight uniformly after s0. For h_(n,u,t)=Q_n(u)G_(n,t), the Gibbs variational inequality gives for every λ>0

|〈w_(n,v),h_(n,u,t)〉_π|
≤λ[H_n(s0)+log π exp(|h_(n,u,t)|/λ)],  v≥s0.                            (14)

For s≥s0+u put v=s−u; duality identifies the left side with |B_n(s,t)−A_n(t)|. Thus tight entropy would suffice if the exponential integrability norm

K_n(u)=sup_(t∈[a,b]) inf{λ>0: π exp(|Q_n(u)G_(n,t)|/λ)≤2}

satisfied lim_(u→∞)limsup_n P(K_n(u)>ε)=0 for every ε>0. The resulting bound is K_n(u)(H_n(s0)+log2), with the infimum handled by λ↓K_n(u). This is a genuinely different integrability requirement from C, and (14) proves exactly why it would suffice. It is only a sufficient criterion, not an equivalent reformulation of W.

The new R comparison controls the quadratic term, not K_n. Extending a polynomial-query comparison to any **fixed number** of overlap factors might give fixed moments, but not the exponential series with constants uniform in its order. The direct exponential endpoint test has maximum exp(O(n^(1/3)/λ)) and is outside (10); truncating it leaves a tail weighted by precisely that exponential. The retained static/history caps allow exp(Cn^β), which does not make this tail uniformly integrable at a fixed λ. Furthermore, a tight fair-start entropy bound at fixed s0 has not been proved for Rademacher either. Equation (14) identifies a viable alternative set of inputs, but neither unproved input is silently assumed.

### 5.2 A fair-uniform-start reversible countermodel with all fixed moments

The following strengthens the test of the entropy shortcut to an actual reversible evolution with a fair uniform start. It is **not heat-bath SK**, and its observable is a generic pairing test, not asserted to be an SK autocorrelation F. It refutes the generic inference needed to replace C(i) by tight entropy even after every fixed observable moment is controlled.

For integer m≥2 let Ω_m={1,…,m}². On each coordinate let p=2^(−m), assign stationary mass p to state 1 and (1−p)/(m−1) to every other state. Let π_m be the product stationary measure. Independently refresh coordinate one from this law at rate 1/m and coordinate two at rate 2/m. The chain is irreducible and reversible. Start uniformly on Ω_m (a product of two uniform laws), so each rare-state initial probability is q=1/m. Put

f_m(x,y)=m(1_(x=1)−1_(y=1)),   π_m f_m=0.

If literal independent fair bits are desired, restrict to m=2^k and identify Ω_m with {−1,1}^(2k). The initial law is then exactly independent fair spins; the dynamics remains block refresh, not SK heat bath.

Then exactly

ρ_s f_m=(1−mp)(e^(−s/m)−e^(−2s/m)),
||P_u f_m||_2²=m²p(1−p)(e^(−2u/m)+e^(−4u/m)).                           (15)

For any compact s-interval the first quantity tends uniformly to zero. The visible limit may be taken to be the one-point ergodic probability space, with strong limit f=0. Every fixed L^k(π_m) norm tends to zero: π_m|f_m|^k=2m^k p(1−p). The positive profiles in (15) tend to zero even at u=0. Yet at s=m log2,

ρ_s f_m=(1−mp)/4→1/4.                                                    (16)

The initial entropy of each coordinate is

q log(q/p)+(1−q)log((1−q)/(1−p))≤log2,

because q≥p, the second term is nonpositive, and q log(q/p)=log2−(log m)/m. Hence Ent(ρ_s||π_m)≤2log2 for **every** s≥0 by data processing. This model has fixed-time convergence with a relaxing limit, strong observable convergence in all fixed L^k, and uniformly bounded evolved entropies, but fails uniform late-time pairing relaxation. Its densities do not have tight L² norms. For any fixed λ<1/log2,

π_m exp(|f_m|/λ)=1+2p(1−p)(exp(m/λ)−1)→∞,

so the exponential norm required in (14) does not tend to zero. This locates the failure rather than merely restating that L² is missing. No uniform kernel hypothesis is claimed for this model, and no Rademacher SK counterexample follows.

## 6. Primary comparisons and the remaining mathematical obligation

The following comparisons use actual proof passages and retained current version responses; search snippets and catalogue descriptions are not premises.

- [Pei, 2609.14273v1](https://arxiv.org/abs/2609.14273v1), Theorem 1.1, Lemmas 2.1/3.1 and their full proofs: positive static replica expectations have a multiplicative Gaussian/bounded-law comparison. Differentiating introduces a fixed number of Gibbs replicas; the fourth-order cancellation uses squared two/four overlaps. Its test A is deterministic and independent of J. Neither e^(−ℋ(end)) under a heat-bath trajectory nor the Doob history law in (8) has that contract. The result is a useful static tail input, not a proof of fair-start warming or weighted-history comparison. This current comparison was absent from I40's list and does not close its density gap.
- [Davies–Lee–Sandhu–Shi, 2607.08160v1](https://arxiv.org/abs/2607.08160v1), Corollary 1.5, Theorems 1.6/7.2, Algorithm 1 and the warm-start proof: the regime is beta<1/2 and the start is constructed through an annealed/approximate-localization distribution, followed by localized sampling. Its Jarzynski-weighted path uses Lipschitz-drift and annealed-LSI assumptions. It is not the independent-fair-spin critical heat-bath path. The approximate warm-start TV error cannot be multiplied by n^(1/3) without a decay rate here.
- [Dembo–Gheissari, 2006.13167v2](https://arxiv.org/abs/2006.13167v2), Theorem 1 and the Taylor proof: multitime polynomial statistics of random-matrix **diffusions** on a fixed horizon are covered, with constants depending on that horizon and the moment orders. This is not Ising heat bath at n^(2/3), nor an infinite-wait comparison. QU's actual score proof is the stronger usable operation for §4.
- [Chatterjee, math/0508519v3](https://arxiv.org/abs/math/0508519v3), Theorem 1.1 and proof: derivative control is the obligation in replacement. The correct identifier/version was fetched afresh; the unrelated math/0508213 paper is not cited as this theorem. In §4 the small derivative comes from the QU score/cutoff operations, not from the abstract replacement principle alone.
- [Du–Huang, 2607.02172v2](https://arxiv.org/abs/2607.02172v2), critical overlap-moment input and its reweighted-moment setup: these are equilibrium replica/free-energy controls. Such a static Gibbs expectation does not identify the square-tilted midpoint in (4). No critical fair-start density conclusion is imported from it.

The named problem remains the finite-size critical quench's approach to equilibrium when waiting times escape compact sets. QU itself separates compact positive-time convergence and relaxation of the limiting quench. That separation motivates W; no invented importance score or worldwide-priority conclusion is used.

After the completed technical profile transfer (R), the most concrete remaining sufficient estimate is now a **single fair-start density obligation**:

for some fixed s0>0 and every ε>0, some M<∞ satisfies
limsup_n P_Rad{z_+ E_ν^J exp(−ℋ(X_(2s0T_n)))>M}<ε.                        (17)

Unlike merely renaming W, §3 derives this exact positive weighted-history quantity, its normalized two-copy marginals, its entry score, and its Feynman–Kac generator, and proves why three proposed simplifications fail. Equation (17) is C(i) in that representation, explicitly sufficient and not necessary. It remains unproved. The entropy/Orlicz alternative has different unproved inputs and the explicit countermodel (15)–(16) precludes dropping its tail requirement. Gaussian W is proven technical; Rademacher W and full W remain unproved/unrefuted. No theorem qualifying for a substantial nomination has been completed.

## 7. Reproduction and evidence boundaries

The one-time I41 seal binds the report, scripts, exact diagnostics, frozen briefs/reports/gate history, searches, selected pins, current response bodies and version records. The verifier rehashes the complete corpus against its existing manifest and the nontruncated Git tree; reconstructs corpus and frozen-project searches; checks read-range and contract excerpts; verifies fresh raw responses; checks the old I39/I40 artifact seals **without refreshing them**; and reruns the new exact checks and I40/I39 checks in memory. Mutable shared-ledger drift is reported separately from immutable dependency drift.

The new rational diagnostic constructs nonuniform finite Gibbs heat-bath kernels, reconstructs the collision/reversal/semigroup representations, checks stationary four-time centering, conditional square-tilted midpoints, the symmetric generator and sign-changing potential, Rademacher initial-normalizer enumeration, first-failure telescoping, and the fair-start entropy-countermodel algebra. Its semigroup algebra checks use discrete powers of a reversible heat-bath kernel; the continuous-time deductions in the report follow by generator conjugation/spectral calculus and are not mislabeled as rational evaluations of transcendental matrix exponentials. The two-spin continuous-time formula is checked by its exact eigenvector/generator identities. There is no floating numerical evidence. These finite checks do not certify the analytic three-leg extension or the target W; the parent may commission fresh independent proof review of the new partial results.

Pre-seal reproduction passed: 174 frozen inputs, 160 prior Markdown files searched (16 matching documents), 74 selected pinned files from five manuscripts, 22 read records, 46 label contracts, and 17 successful fresh primary responses (seven pinned raw files and five versioned PDFs with current-version pages). All 258 I39 and 237 I40 sealed artifacts are unchanged. The new diagnostic passes 2,846 exact assertions and replays I40's 3,285 plus I39's 389. These are diagnostic counts, not independent theorem verifications. No frozen-input or mutable-ledger drift was observed at packaging.

Run from `/home/mj-kang/Documents/Dev/math/openai-proof-research`:

```bash
python -B frontier/experiments/i41_rademacher_fair_start_warming/check.py
python -B frontier/experiments/i41_rademacher_fair_start_warming/verify.py
```

**Final verdict:** I40's audited deductions pass in their original form. The new fixed-horizon positive-profile comparison is complete as a technical source-operation extension, pending a fresh parent-arranged review. The normalized fair-start density and entropy-duality approaches retain precisely identified unpaid estimates. Full two-law W remains unproved and not refuted; no substantial finding is nominated.
