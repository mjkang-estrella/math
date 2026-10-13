# I220 — quantitative Coulomb continuation

**PROVED NOMINATION, at the author level; both parent acceptance gates remain pending.** The nomination is a sharp cost/regularity theorem for one concrete smooth identical-marginal Coulomb/Riesz construction. It is not a claim that its interpolation exponent is new to the literature. The closest prior result, Carioni–Del Grande–Iglesias–Schönberger, Example 4.6, already establishes the corresponding fractional penalization exponent for a two-marginal line-segment model. The parent must decide whether the extension here is substantial enough.

## Complete statement

For every integer d>=2 and s>0, specialize the accepted family-373 construction at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` by taking its free bump to be

    g(x)=C product_i exp(-1/(a^2-x_i^2)) on Q=(-a,a)^d,

zero outside Q, with Qbar compactly inside the source's common branch ball and integral g^2=1. With nu=g^2 dx and the source maps Y_k,W_k,

    mu=nu/3+(Y_1#nu+W_1#nu+Y_2#nu+W_2#nu)/6.

This has rho,sqrt(rho) in C_c^infinity. Let Delta be the three-marginal c_s cost excess over E_s(mu), where c_s=sum_{i<j}|x_i-x_j|^{-s}. All constants depend on the fixed geometry and bump, and fractional constants also on t,p.

For every Borel pair T_2,T_3 individually preserving mu,

    Delta(T_2,T_3)>=c(1+V)^(-2),
    V=|DT_2|(Q)+|DT_3|(Q).

For 0<t<1,1<=p<infinity and alpha=tp<1,

    Delta(T_2,T_3)>=c(1+S)^(-2/alpha),
    S=[T_2]_{W^{t,p}(Q)}^p+[T_3]_{W^{t,p}(Q)}^p.

These are unweighted Lebesgue seminorms. The lower proofs actually use only T_2's central complexity. Consequently the bounds hold for larger componentwise or global complexities as well.

There are explicitly defined preserving maps T_n, with T_n^3=Id mu-a.e., satisfying

    0<Delta(T_n,T_n^2)<=C n^(-2),
    |DT_n|(R^d)+|D(T_n^2)|(R^d)<=C n,
    [T_n]_{W^{t,p}(R^d)}^p+[T_n^2]_{W^{t,p}(R^d)}^p<=C_{t,p} n^alpha.

Both actual powers have bounded compactly supported representatives. Thus all the stated constrained cost gaps have matching powers for sufficiently large budgets. The seminorm, rather than its pth power, gives exponent -2/t.

A preserving T_2 continuous on Q, in W^{1,1}_{loc}(Q), or with finite W^{t,p}(Q) seminorm for tp>=1, instead has an absolute positive cost gap independent of its norm. **No smooth or Lipschitz near-optimal recovery is asserted.**

## Proof package and nonroutine steps

The complete argument, including constants, is in [analytic-attempt.md](../experiments/i220_quantitative_coulomb_continuation/analytic-attempt.md).

1. Source strict convexity yields a uniform quadratic residual. The two negative outer branches require a separate inverse-map comparison; they are not assumed covered by a Hessian with the wrong coordinate fixed. Compact forbidden-pattern gaps cover every other configuration, including collisions.
2. For a branch selection S_j in the central cube, exact marginals give `(H_j^{-1} composed with T_2)#(nu|S_j)<=nu/2`. Incoming outer mass only strengthens this. Either at least half the central mass incurs a fixed gap, or one of four outer selections has nu-mass at least 1/8. Testing against its mollified indicator at a chosen scale gives the lower bounds. Both BV and fractional zero-extension boundary terms are included; no positive lower bound for the flat density is used.
3. Equal geometric cells of the first coordinate are split into equal **conditional probability** halves. Cellwise CDF doubling maps each half onto half the full cell law. Their inverse maps complete exact cycles `v -> Y_k(u) -> W_k(u) -> v`. Every leg's pushforward is verified. Source stationarity removes the linear Taylor term, giving n^{-2}, while monotonicity and jump-interface estimates give variation O(n). Full-space translation estimates give fractional energy O(n^alpha), including all support-crossing terms.
4. Continuous images cannot split among separated components, and a central mass 1/3 cannot fit in an outer target of mass 1/6. Sobolev label rigidity extends this to W^{1,1}_{loc} and to the critical fractional exponent tp=1. This explains exactly where the recovery ceases to be regular enough.

As a direct consequence, the infimum of `Delta+epsilon V` scales as epsilon^{2/3}; that of `Delta+epsilon S` scales as epsilon^{2/(2+alpha)}. These are infimum estimates, not existence or Gamma-limit theorems.

## Limits and significance decision

The upper theorem is for the displayed product bump, not every smooth marginal in the source. Flat endpoint densities can make inverse-CDF derivatives unbounded; BV monotonicity, not Lipschitz inversion, is used. A zero extension is arranged with T_n(0)=0 so the actual T_n^2 is compactly supported too. No weighted dmu-dmu fractional estimate, uniform constants in d,s, exact leading coefficient, or regularized-minimizer existence is claimed.

The separate lower and upper routes both close under these hypotheses. There is no remaining analytic lemma being hidden as a partial theorem. What remains is independent proof review and the contribution decision. General interpolation, the fractional jump threshold, equality of Monge/Kantorovich values and the bare fractional penalty exponent are explicitly excluded from the novelty claim. The proposed contribution is their fully checked sharp realization for the smooth identical-marginal three-particle Coulomb/Riesz example, with quantitative control of exact cycles.

## Reading, authentication and delivery

Read the complete 749-line family-373 manuscript in its existing source location; a fresh pinned-PDF extraction matched its SHA256. Read all three saved I217 external excerpts and bounded primary-source material on mixing, interpolation and Coulomb smoothing. Exact limits, failed shortcuts and prior-project overlap are in [reading-and-failures.md](../experiments/i220_quantitative_coulomb_continuation/reading-and-failures.md); the close prior-art comparison is in [literature.md](../sources/i220_quantitative_coulomb_continuation/literature.md). [input-authentication.json](../experiments/i220_quantitative_coulomb_continuation/input-authentication.json) records full-file hashes alongside limited-read scopes. Full-file hashing does not imply full-file reading.

Only assigned I220 documents and fully read source excerpts were written. No subordinate agents, research code, experiments, tests, snapshots, seals, replay, shared-ledger edits, staging, commits or publication. Output hashes are returned detached; no file contains its own hash. This author-level nomination does not increment the accepted-finding count.
