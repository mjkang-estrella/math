# Sustained full-question work: fractional-Gaussian prediction

Status: INCOMPLETE, no qualified survivor, no credit. This document records actual proof work and exact failed bridges. It is not a proof of the source conjecture.

Mishura–Ralchenko–Schilling, arXiv:2209.02501v1, Conjecture (A), pp1–2, Eq(1), Proposition2.16/Eqs(25)–(26), §2.5: for **every H∈(1/2,1), every integer n≥2, every k=2,…,n**, the unique coefficients Γ_n^k of E(Δ_1|Δ_2,…,Δ_n)=Σ Γ_n^k Δ_k are strictly positive. Δ_k=B_k^H−B_(k−1)^H, with covariance r_0=1 and r_k=((k+1)^(2H)−2k^(2H)+(k−1)^(2H))/2. Time reversal identifies these with finite-predictor coefficients; it changes no signs or quantifiers.

Closest actual later source: Bodnarchuk–Mishura–Ralchenko2408.09188, introduction Conjecture A3 and §2.1. It retains the universal question, proves the missing middle coefficient at n=4 through r_2+r_2²−r_1²−r_1r_3>0, and distinguishes the one-sided problem from bilateral coefficient order. It is not a proof for all n. Chigansky–Kleptsyna2504.01562v2, actual introduction Theorems1.1–1.3, alternating-projection discussion, gives asymptotic PACF machinery with explicit hypotheses; it does not state universal finite-predictor coordinate positivity. Its full long proof has not been audited for an implicit subsumer. These are bounded comparisons, not full novelty clearance.

## Approach 1: positive exponential mixtures / Hausdorff moments

Put p=2H∈(1,2), C=1/(2Γ(−p))>0. The compensated Laplace integral for x^p, after taking a second difference, gives for every k≥1

    r_k=C∫_0^∞ e^(−(k−1)t)(1−e^(−t))² t^(−p−1) dt.

The compensation cancels exactly. Near zero the integrand is O(t^(1−p)); at infinity for k=1 it is O(t^(−p−1)); hence this is an actual convergent positive integral, including k=1.

A tempting complete bridge is to represent **all** lags k≥0 by r_k=∫_[0,1] u^k μ(du) with finite positive μ, then invoke prediction results for mixtures of AR(1) covariances. That representation is impossible for every p∈(1,2). Let ν=u μ. Its moments of order j≥0 would be r_(j+1). By uniqueness of finite measures from moments on [0,1] (polynomials are uniformly dense in continuous functions), ν is the pushforward, under u=e^(−t), of C(1−e^(−t))²t^(−p−1)dt. But then

    μ((0,1])=∫_(0,1] u^(−1)ν(du)
             =C∫_0^∞ e^t(1−e^(−t))²t^(−p−1)dt=∞.

This contradicts μ([0,1])=r_0=1. An atom at u=0 cannot repair the divergence. Thus complete monotonicity of the **shifted** covariance is not the finite positive-mixture hypothesis starting at lag zero. This is an all-H obstruction, not a low-order test. It does not prove predictor negativity for fGn.

Remaining route: a renormalized kernel/precision theorem allowing this infinite lag-zero mass, with its diagonal renormalization tracked exactly. No such applicable theorem has been proved or source-verified here. Replacing fGn by FARIMA would change the source process.

## Approach 2: exact Levinson recursion and a ratio invariant

Use usual lag indexing c_(m,j), j=1,…,m. With α_m=c_(m,m), source Eq(26) becomes

    c_(m,j)=c_(m−1,j)−α_m c_(m−1,m−j), j<m.

If preceding coefficients and α_m are positive, preservation of positivity requires the **full** inequality

    α_m < min_(1≤j<m) c_(m−1,j)/c_(m−1,m−j).

Positive PACFs alone, even with decreasing positive log-convex covariances, do not give it. Here is an exact obstruction to that proposed induction. Take r_0=1,r_1=4/5,r_2=169/250,r_3=319/500. The 4×4 Toeplitz covariance has positive leading principal determinants

    1, 9/25, 8019/62500, 21434787/488281250.

Its first three PACFs are 4/5,1/10,1/5. All four r_k are decreasing and positive, and r_1²≤r_0r_2, r_2²≤r_1r_3. Yet c_(3,1)=7/10, c_(3,2)=−11/250, c_(3,3)=1/5. These rational identities are checked independently in checks.py. The relevant failing comparison is α_3=1/5 > (1/10)/(18/25)=5/36. Positive definiteness is exact by Sylvester, not inferred from floating eigenvalues. A stationary Gaussian extension exists by the standard finite positive Toeplitz extension theorem, but that extension is not needed to refute the finite linear-algebra implication.

This is **not an fGn counterexample**. It shows exactly why the general properties read in the source cannot close the recurrence by themselves. The sought new ingredient is an fGn-specific bound on the asymmetric coefficient ratios, uniform over all m and H. Asymptotic α_m∼(H−1/2)/m alone neither bounds those ratios nor handles finite m. No endless grid or fixed-n specialization is proposed.

Adaptation objection: if a classical alternating-projection representation supplies nonnegative terms for every finite coefficient under hypotheses actually satisfied by fGn, it would close the whole question and could make this routine. The exact global AR/MA sign hypotheses and full finite-coordinate theorem have not been verified here. Therefore no substantive/newness PASS is asserted.

## Abandoned earlier lead, positively excluded

Newman2606.18654v1 Conj1.2 was screened first. Conditional cumulants give E κ_4(η)=−6Var(v(η)), which permits cancellation unless an additional sign theorem is available. A second Hermite-kernel approach rules out finite-polynomial directing densities: the highest nonzero coefficient of a nonnegative polynomial must have even degree and nonnegative sign, while Gaussian marginal averaging gives mean zero; descending induction kills every coefficient. Neither was a resolution.

Before substantial further investment, the exact-author follow-up search found Zheng–Zhou2606.25976v1,24June2026, Theorem1.1, fully resolving the source question. Actual §§2–3 were read: for every directing-measure event E, the localized difference measure ν_E is dominated by its Gaussian average and has nonnegative Fourier transform bounded by the matched Gaussian Fourier transform. Hardy's equality theorem forces ν_E=P(E)γ; a countable determining class makes η*η̃ deterministic Gaussian, and Cramér then gives Gaussian η with deterministic variance and Gaussian random mean. Degenerate variance is handled explicitly. This is a complete applicable bridge, so the family is EXCLUDED PUBLIC. No amendment, vector extension or helper is nominated.
