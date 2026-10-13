# R022 — Sharp small-information stability for arbitrary binary summaries

**Accepted as the sixteenth substantial finding.** The complete theorem passes [I335 independent proof review](../reviews/i335-full-endpoint-proof.md) unchanged and [I336 independent contribution review](../reviews/i336-full-endpoint-contribution.md) as SUBSTANTIAL. The endpoint theorem and its production estimate count once. Validation is written mathematical review under the stipulated source corpus, not machine formalization or external human peer review.

## Exact theorem

Let X be uniform on {-1,1}^n, n>=1, and let T_r be independent bit noise with correlation r. For u:{-1,1}^n -> [-1,1], define, with natural logarithms,

    psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2,
    I(u)=E psi(u)-psi(Eu),
    d_a(u)=min_(1<=i<=n, s in {-1,1}) E|u-s a X_i|².

For every 0<a1<1 and 0<r0<=r1<1, there is a finite C=C(a1,r0,r1), independent of n, such that for every 0<a<=a1, every r in [r0,r1], and every u with exactly I(u)=psi(a),

    d_a(u) <= C a^(-4) [psi(ra)-I(T_r u)].             (S)

All original bounded kernels are included: arbitrary means, endpoint values, rare spikes, any degree, and dimensions and distributions depending on a. There is no prior closeness or residual-tube hypothesis. The exponent four is optimal: no smaller exponent works over this same class.

A supporting theorem, included in this acceptance, is an absolute constant c>0 such that every interior bounded cube field satisfies

    D(u) >= F(I(u)) + c (Eu)² I(u)²,                  (P)
    F(psi(t))=t atanh(t),
    D(u)=(1/4) sum_i E[(u-u^(i))(atanh(u)-atanh(u^(i)))].

Here u^(i) flips coordinate i. Positive-time smoothing allows (P) to be used on original endpoint-valued fields without assuming finite initial D. The coefficient c is uniform in dimension and mean, including means tending to ±1. This is not the stronger false claim with an extra factor 1/(1-(Eu)²).

## Dependencies and proof

The source is [sharp binary-information contraction at the immutable revision](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026), including its actual scalar, capacity, canonical, reserve, thinning, upgrade and flow statements. These upstream theorems are stipulated true as requested. The new endpoint deductions are proved in [I325's complete analysis](../experiments/i325_global_endpoint_alternative/analysis.md), with the [I334 production construction](../iterations/i334-uniform-biased-production-candidate.md). I335 independently recalculates them in full.

Write m=Eu, b=max_i|uhat(i)|, H=sum_|S|>=2 uhat(S)² and B=m²+sum_i uhat(i)²-b²+H. Conditional Jensen and an endpoint-safe Bregman comparison give b<=a and

    B <= d_a(u) <= (1+2U_a1)B,
    Var(u)<=2I(u)<=C a².

The proof separates absolute entrance from relative payment.

1. **Original higher-mode entrance.** On a fixed interior-mean interval, write u=m+L+W and compare with m+clip(L), leaving u unchanged. Concavity of f_r(J)=psi(r psi^(-1)(J)) gives an exact tangent inequality. Split the original residual into small and large values. Input strong convexity pays the large values; hypercontractivity makes their output and low-degree projections small. The higher Walsh gap gives

       H <= C[Delta+a^4],  Delta=psi(ra)-I(T_ru).

   The first-chaos clipping error is exponentially small. This is only an entrance bound.

2. **Uniform quartic passage.** If H=O(a^4), split the residual at a^(1/2). Keep its large-value input Bregman entropy A_bad exactly; its output and low projections are negligible at order a^4. With h=1-m², q=||L||²=h a²+O(a^4), and kappa=sum_i uhat(i)^4/q², the deficit is

       r²(1-r²)a^4[kappa m²/(3h)+(1-kappa)/6]

   plus a nonnegative completed level-two square, positive higher-mode terms, r² A_bad and a dimension-uniform o(a^4). Hence Delta=o(a^4) forces m->0, one original singleton to carry almost all q, and H=o(a^4). This enters a fixed cone, not an assumed shrinking tube.

3. **Relative cone estimate.** Use the genuine conditional field v=m+bX_1 and let L0 be the L2 norm of the other singleton terms. Retain the full conditional entropy baseline and clip only those other terms. One-bit capacity pays the bias contribution; the exact conditional quadratic multiplier pays a² L0²; global input convexity and the higher-mode gap pay H. Mixed couplings are absorbed with small fixed cone parameters. Clipping costs exp(-c/L0²), exactly zero at L0=0, and are small relative to a²L0². Thus

       Delta >= c[a^4m²+a²L0²+H].

   A hypothetical failure of Delta>=c a^4 B first enters this cone by steps 1–2, then contradicts this relative bound. An absolute o(a^4) error is never divided by a vanishing B.

4. **Uniform bias production.** Construct G(m,I)=F(I)+cm²I² and join max{B_m(I),G(m,I)}, where B_m is the source reserve profile. Its Hessian is positive for small absolute c, and the old reserve pays it at high information. On a one-positive-corner optimizer, retained strict thinning slack pays the flag-information demand, while the genuine one-bit core surplus pays its mean-dependent part. On the reflected optimizer, the strict source entropy/rate ratios keep the upgraded demand increasing to the already-paid wall. The cost optimizer uses average entropy, but pooling retains the original individual child informations. Dimension induction gives (P), including endpoint-mean limits after positive-time smoothing.

5. **All means and amplitudes.** Put y(s)=I(T_(exp(-s))u), w(s)=psi(a exp(-s)) and R=D-F(y). Their difference satisfies z'=R-Az with 2<=A<=K(a1). Integrating (P), either the terminal deficit is already at least w/2, or y remains bounded below by a constant times a². Therefore |m|>=1/2 gives Delta>=c a^4 uniformly, even as |m|->1. For |m|<=1/2 use steps 1–3 at small a. On the fixed remaining positive-amplitude interval use [R020](R020-global-binary-information-stability.md). This proves (S).

## Sharpness

Fix 0<|m|<1 and a correlation r in (0,1). There is a genuine one-coordinate field u_a=m+b(a)X with exactly I(u_a)=psi(a). With h=1-m²,

    b(a)²=h a²-(2/3)m²a^4+O_m(a^6),
    Delta_r(u_a)=r²(1-r²)m²a^4/(3h)+O_(m,r)(a^6),
    d_a(u_a)=m²+(a-b(a))² -> m²>0.

It is admissible for all sufficiently small a. Thus a^(-p)Delta tends to zero for every p<4 while the distance does not. This earlier one-coordinate calculation is supporting evidence for the one accepted theorem, not a separate finding.

## Contribution and validation limits

R020 already gives unrestricted dimension-free stability on every compact positive-amplitude rectangle, but supplies no rate as its lower amplitude tends to zero. The new contribution is the paid original-spike quartic/relative passage and the bias-sensitive joining correction uniform up to endpoint means. Source optimizer facts, Bregman calculus, hypercontractivity, maximum/induction frameworks, earlier modal and quartic calculations, and the final scalar integration are credited ingredients.

I336 compares actual primary arbitrary-array induction, Boolean stability, FKN and fixed-law contraction interfaces; its [literature record](../sources/i336_full_endpoint_contribution/literature.md) states the exact scopes. Those do not supply a checked reduction retaining all arbitrary soft kernels and the uniform fourth-power rate. This focused assessment does not establish worldwide priority or audit every external proof margin.

- I335 full proof: PASS unchanged; analysis SHA256 `70e9a758606162f947b756d7343495cb619ff9d5086bf7d204ae4027564af59a`.
- I336 full contribution: SUBSTANTIAL; analysis SHA256 `e70c3a5123ddddebf70beb7fda5b0c7335e6203a7c49f2c610fadeeefba6c14d`.
- Parent matched the five terminal hashes for each gate, local source identities and fresh pinned bodies. See [proof disposition](../iterations/i335-full-endpoint-proof-parent-disposition.md) and [contribution disposition](../iterations/i336-full-endpoint-contribution-parent-disposition.md).
- Constants are existential. No bound uniform as r approaches zero or one, or as a1 approaches one, is claimed. No formal proof certificate is claimed.

This acceptance has its own commit. **Sixteen accepted; four remain toward twenty.**
