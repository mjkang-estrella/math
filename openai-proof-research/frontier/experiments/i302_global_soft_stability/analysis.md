# I302 — proposed global arbitrary-kernel soft-information stability

2026-10-13. **Complete proposed implication chain, not independently accepted.** This combines the new unreviewed I300 Gaussian translation argument with the completed internal I128/I131/I290/I295 deductions. Internal deductions are not stipulated upstream results. Their required proof and contribution gates remain open. This is the full version of the same S128 research target; the restricted I295 theorem is not a second independent finding if this version is accepted.

## Exact proposed theorem

Let X be uniform on {-1,1}^n, n>=1, and let T_r be independent bit-noise with correlation r. Put

    psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2,
    I(u)=E psi(u)-psi(Eu),
    d_a(u)=min_{i,sign} E|u-sign*a*X_i|^2.

Fix any 0<a0<=a1<1 and 0<r0<=r1<1. The proposed theorem is that there exists C depending only on these four endpoints such that, for every finite n, every a in [a0,a1], every r in [r0,r1], and every u:{-1,1}^n->[-1,1] with exactly I(u)=psi(a),

    d_a(u)<=C[psi(ra)-I(T_r u)].                  (S302)

There is no restriction r1*a1<1/sqrt(2). Bias, endpoint values, rare spikes, arbitrary dimension, and unbounded complexity are included. No initial closeness or singleton lower bound is assumed. The constant is existential and no computable numerical value is asserted.

All OpenAI statements at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. The essential family119 hypotheses and labels are recorded in I295's authenticated source index. The proof below still depends on independent validation of the actual internal lemmas listed at the end.

## 1. Uniform Gaussian gap on every compact rectangle

Use standard Gaussian expectation and the OU correlation operator Q_sigma. Write I_G(v)=E psi(v)-psi(Ev). I295 R295 proves that every measurable v:R^N->[-1,1] has a nondecreasing scalar rearrangement w:R->[-1,1], with the same full input law, satisfying

    I_G(w)=I_G(v),
    I_G(Q_sigma v)<=I_G(Q_sigma w).

The proof uses layer cake, Borell for two arbitrary sets at every level, compatible parallel halfspaces, largest-set integrals, and convex order. This is a credited classical rearrangement argument; its full displayed verification is I295 Sections 2.1–2.2.

The new I300 claim U300 says

    I_G(Q_sigma w)<psi(sigma psi^{-1}(I_G(w)))

for every scalar w with 0<I_G(w)<log 2 and 0<sigma<1. Its proposed proof uses the non-strict Gaussian limit of the stipulated cube inequality, the equality Euler identity, and a translation second variation. The exact new scalar inequality, bias-dependent variance bound, smooth-tail justification, and removal of prior smoothing are in I300 Sections 2–6. No part is an upstream stipulation or an already obtained independent PASS.

If U300 is valid, the following compactness makes it uniform. Bounded nondecreasing scalar functions are compact in Gaussian L2: select at rational points, extend monotonically, and use pointwise convergence away from countably many jumps plus dominated convergence. On bounded fields, I_G is L2-continuous by uniform continuity of psi. The mapping (w,sigma)->Q_sigma w is jointly L2-continuous on compact correlation intervals, by contraction and the Hermite expansion. Thus for any

    0<b0<=b1<1, 0<sigma0<=sigma1<1,

the set of triples (w,b,sigma) with w monotone, b and sigma in these intervals, and I_G(w)=psi(b), is compact. It is nonempty: w=b sign(x) works. The continuous deficit is positive at every triple by U300, hence has a positive minimum eta_G. Rearrangement therefore gives, for every Gaussian dimension N and arbitrary measurable v with I_G(v)=psi(b),

    I_G(Q_sigma v)<=psi(sigma b)-eta_G.           (G302)

This is dimension independence from a fixed scalar compact set, not from compactness of growing Gaussian spaces.

## 2. Exclude diffuse increasing near-extremizers

Suppose increasing cube kernels g_k have exact parameters a_k in [a0,a1], r_k in [r0,r1], deficits Delta_k=psi(r_k a_k)-I(T_{r_k}g_k)->0, and max_i ghat_k(i)->0. Choose once and for all

    r1<lambda<1,
    sigma_k=r_k/lambda.

All sigma_k lie in a compact subinterval of (0,1), and lambda*a_k lies in a compact subinterval of (0,1). Unlike the restricted I295 proof, no small-amplitude threshold enters.

The I128 production identity, with the stipulated sharp inequality, is

    z'=R-Az, 2<=A<=K, R>=0,
    z(t)=psi(a exp(-t))-I(T_{exp(-t)}g).

The integrating factor bounds every earlier z(t) by exp(K t_max) Delta_k, where t_max=-log r0 and K=max_{[0,psi(a1)]}F', F(psi(a))=a atanh(a). Therefore, with h_k=T_lambda g_k,

    I(h_k)=psi(lambda a_k)+o(1),
    I(T_{sigma_k}h_k)=psi(r_k a_k)+o(1).          (1)

Both are actual information budgets, including their mean corrections.

For fixed degree d, let p_k=(h_k)_{<=d}. Its cube L2 truncation error squared is at most lambda^(2(d+1)). The polynomial p_k itself has the same L2 norm on cube and Gaussian space, at most one. Monotonicity and boundedness give 0<=partial_i h_k<=1, so

    Inf_i(p_k)<=E(partial_i h_k)^2
       <=E partial_i h_k=lambda ghat_k(i)->0.

The fixed-degree bit/Gaussian replacement bound is controlled by C_d times the maximum influence, because the first three moments match and sum_i Inf_i<=d. I290 and I295 give the full fourth-moment calculation and its extension to the clipping-distance test. Apply those estimates to p_k and the additionally noised polynomial Q_{sigma_k}p_k. Let v_k=clip(p_k) on Gaussian space. For every desired epsilon>0, first take d sufficiently large, then k sufficiently large, to obtain

    |I_G(v_k)-I(h_k)|<epsilon,
    |I_G(Q_{sigma_k}v_k)-I(T_{sigma_k}h_k)|<epsilon. (2)

The Gaussian clipping-distance bound pays the unbounded polynomial tails; uniform continuity of psi pays both entropy and mean errors. No degree growing with k is claimed.

Set b_k=psi^{-1}(I_G(v_k)), so the Gaussian input budget is exact. For sufficiently small errors, b_k belongs to a fixed compact interval strictly inside (0,1), slightly larger than [lambda*a0,lambda*a1]. Equations (1)–(2) and continuity make psi(sigma_k b_k) close to psi(r_k a_k). But (G302) gives a fixed positive gap at those b_k,sigma_k. Choose the errors smaller than one half that gap. This contradicts (1).

Thus no increasing diffuse sequence of vanishing deficit exists on the original endpoint rectangle.

## 3. Recover the uniform linear stability estimate

The contradiction implies that there exist beta>0 and eta>0, depending only on the original endpoints, such that every increasing exact-information kernel with max singleton<=beta has Delta>=eta. Otherwise take max singleton<=1/k and Delta<=1/k to produce the excluded sequence. Since d_a<=4, this sector satisfies d_a<=4 Delta/eta.

The internal B290 theorem supplies a constant C_beta for the complementary sector max singleton>=beta, with d_a<=C_beta Delta. Its proof uses the actual pinned joining equality and strict retained losses, compact pair laws, a positive-time production entrance, the original-information backward inequality E131, and the spike-tolerant L131 estimate. B290 permits bias and arbitrary remaining coordinates. Its proof is part of the required dependency review, not a new hypothesis imposed on S302.

Hence all increasing kernels satisfy d_a<=C_inc Delta, with C_inc=max(C_beta,4/eta). Q131b sorts any arbitrary kernel u to an increasing g preserving its law and information, and supplies

    Delta(u)=Delta(g)+L_gain, L_gain>=0,
    d_a(u)<=C_comp[d_a(g)+L_gain].

It follows that S302 holds with

    C=C_comp max(C_inc,1).

The full proof never inverts noise in L2. The backward passage in B290 uses the original exact-information budget to enter the local theorem. Its square-root intermediate estimate does not replace the final linear deficit estimate.

## 4. Frozen dependencies and review boundaries

- I300 new proposed U300 proof: `frontier/experiments/i300_gaussian_translation_strictness/analysis.md`, SHA256 `a00cd592d623d7b9b1cc5be06a3fd3c96f09de8cc0fc933295e68238fa75af1e`.
- I295 R295 rearrangement, compact scalar optimization, and fixed-degree transfer details: `frontier/experiments/i295_gaussian_rearrangement_stability/analysis.md`, SHA256 `70992530f4413ff1a7ce8149dc5643cfd2215ca2bb85f2a5861ee70e405ef813`.
- I290 B290, joining equality and non-strict Gaussian limit: `frontier/experiments/i290_global_soft_summary_stability/analysis.md`, SHA256 `2057261d4defe12b348fc97625130cf909e345c99d83a26ead7947171d794cf5`.
- I131 L131, Q131b, E131: `frontier/iterations/i131-soft-summary-stability.md`; I128 production/entropy identities at the exact passages cited there. These are internal proofs, not accepted-count or upstream premises.

I298 and I299 are independently reviewing the restricted I295 target, including the earlier internal chain. I301 is independently reviewing the new I300 strictness argument and its non-strict Gaussian premise. Their future results must be read and reconciled, not predicted or assumed. A separate full-target contribution gate is required. Classical Borell, compactness, invariance, Jensen/Renyi and hyperbolic identities are credited. This proposed unrestricted theorem and restricted S295 must not be counted as two findings.
