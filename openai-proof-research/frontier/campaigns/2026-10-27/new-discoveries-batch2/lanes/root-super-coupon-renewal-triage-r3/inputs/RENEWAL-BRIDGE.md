# A regeneration replacement for the spectral step

Solo ordinary derivation, 2026-10-30; not independently reviewed, not a novelty certificate. This replaces the analytic/Riesz-projection step, rather than repeating the finite-chain audit. It uses the retained proof's exact distinguished-union transition matrix and stationary one/pair flows. All r,s are fixed, 2≤s<r, n→∞. Constants depend on r,s only. Put N=binom(n,s), p=binom(r,s)/N, q=sp/r.

For W=S or S∪U, let B_t=H_t∩W, m=|W|≤2s and o=∅. Let A be the states containing S, or containing S or U. Write Q=Σ_{x∉A}π(x)P(x,A). The already reviewed elementary flow calculation gives Q=q for one target and Q=2q(1+O(1/n)) for two distinct targets. Also π(o)=binom(n-m,r)/binom(n,r)=1-O(1/n). There are finitely many overlap types, so all constants below are uniform in target choices.

**Uniform return bound.** From every state, within r steps there is probability at least c>0 of reaching o: choose deletion of a distinguished member while one remains, choose no distinguished additions, and pad the remaining steps with no additions. The distinguished deletion probability when nonempty is at least 1/r; each no-addition probability is at least 1-m/(n-r), hence bounded below for large n. This supplies a uniform geometric tail for the time to o from every state, by the Markov property in r-step blocks. The first positive return L to o also has a uniform exponential moment. Its mean μ satisfies μ=1/π(o)=1+O(1/n). This last identity can equivalently be obtained by normalizing the expected occupation counts of one return cycle: those counts solve the stationarity equations and have mass μ, with exactly one visit to o before the terminal return.

**Success probability of a cycle.** Success means at least one entry into A before the return to o; let h be its probability. Let V count all D→A entries in that cycle. The occupation-count identity gives EV=μQ exactly. From any state in D, hitting A before o requires a distinguished addition. Its probability is at most [m/(n-r)] E_x τ_o=O(1/n), by summing the conditional probabilities up to τ_o; the return bound controls this expectation uniformly. After each exit from A the same bound applies. Starting at the first entry, the expected number of further entries before o is therefore at most η/(1-η), with η=C/n<1. (The first exit exists before return to o, because o∉A.) Thus

    h ≤ EV ≤ h/(1-η),
    h = μQ(1+O(1/n)),   h/μ = Q(1+O(1/n)).

This calibrates the rare-event normalizer with relative O(1/n) accuracy. A bare exponential approximation with an unspecified mean would not do this.

**Relative tails without eigenvalues.** Successive full un-killed return cycles from o are iid pairs (length,success). Length and success within a cycle need not be independent. Let R_k=L_1+...+L_k and C_t=max{k:R_k≤t}. A uniform exponential moment implies E exp[u(L-μ)]≤exp(Cu²) for |u|≤u_0, by Taylor's formula with an exponentially integrable second derivative. Consequently, for 0<δ<δ_0 and δt sufficiently large, the Chernoff bound gives

    P(C_t outside [floor((1-δ)t/μ),ceil((1+δ)t/μ)])
        ≤ C exp(-c δ²t).

The bound extends to all t≥0 by increasing C. For clarity, apply the mgf inequality to R_k-kμ with u a fixed constant times δ; the gap between t and kμ is at least δt-O(1). The exponent is -cδ²t when δt is large, and is bounded by changing C otherwise.

Let S_o(t) be avoidance of A at integer times 0,...,t starting at o, and k_± the preceding floor/ceiling indices. Even though length and success are correlated, set inclusions give

    (1-h)^(k_++1)-C exp(-cδ²t) ≤ S_o(t)
       ≤ (1-h)^k_-+C exp(-cδ²t).

The lower bound excludes successes in the first k_++1 cycles and excludes C_t>k_+; the upper bound uses C_t≥k_- and failure of the first k_- cycles. No conditioning on cycle counts and no independence of lengths from marks has been used.

Take δ=n^(-1/4), t=floor(θ log N/q), θ>0 fixed. Then δlog N→0, t h²=O(q log N)→0, and δ²t is of order n^(s-1/2)log n. Therefore the additive Chernoff error is negligible relative to any fixed power of N, and

    S_o(t)=exp(-Qt)(1+o(1)).

For stationary start, let R be the first time to o and J=floor(δt). The same return bound gives P(R>J)≤Ce^(-cJ), while monotonicity and strong Markov give

    π(o)S_o(t) ≤ S_π(t) ≤ S_o(t-J)+Ce^(-cJ).

Discarding possible initial hits only increases the upper bound. This is a multiplicative squeeze because π(o)→1 and QJ→0 on the log-time scale; it does NOT subtract an O(p) initial-hit error from an N^(-2θ) pair tail. Hence stationary one and distinct-pair avoidance probabilities are respectively N^(-θ)(1+o(1)) and N^(-2θ)(1+o(1)).

**Uniform integrability.** The same bounds, now for every t, give

    S_π(t) ≤ C exp(-Q(1-Cδ)t)+C exp(-cδ²t)

for sufficiently large n, with fixed constants. Floors cost a bounded factor, and initial-return delay J changes the first exponent by 1-O(δ). For the one-target chain put α=q(1-Cδ), and t_0=ceil((log N+sqrt(log N))/α). Union bound and summation after t_0 give O(exp(-sqrt(log N))/α) plus O(Nδ^(-2) exp(-cδ²t_0)), both o(q^(-1)log N). The missing-target second moment at θ=1-ε and cover-statistic permutation symmetry then proceed exactly as in the reviewed proof. Thus ET~q^(-1)log N for every fixed 2≤s<r.

**Dependency assessment.** This route removes complex contours, analytic eigenprojections, spectral gap calibration and uniform complementary matrix-power bounds. It still needs finite Markov paths, strong Markov return cycles, occupation-count stationarity, exponential-moment Chernoff bounds, asymptotic estimates, and expectation tail sums. These are real proof obligations; no Lean timing or readiness guarantee follows. The elementary renewal structure increases the routine-adaptation objection. It neither identifies an existing same-model published theorem nor clears substantive novelty. Independent adversarial review of this replacement is required before it replaces the retained proof in any candidate packet.
