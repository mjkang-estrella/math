# 122: unknown common retention — compatible estimation reduction

This pre-freeze screen found an existing compatible operation. No candidate or gate is proposed. The following calculation is an author compatibility check, not a new contribution claim.

## Exact scope of the compatibility calculation

Fix a known rational a>0 with a≤1. A deterministic binary string has known length n≥2. Traces independently retain each bit with a single unknown real probability p∈[a,1]. The desired reconstruction succeeds with probability at least 2/3 for every such string and p, in quasipolynomial time and samples, with constants depending on a. This is not unknown position-dependent retention, unknown length, or a guarantee uniform as a tends to zero.

Source122, `Uniform-quasipolynomial-time-trace-reconstruction-October-5-2026/build/manuscript/main.tex`, `thm:main` and its displayed budget, is for known rational p. Writing q=1−p, its scale is

B=p^{-1} log n · X²(1+log X)^6,  X=1+log n/(1+log(1/q)),

with X=1 at q=0. The sample budget is ceil(exp(CB)), and every random tape and well-formed trace stream runs within a fixed polynomial in n, parameter bit length, and the sample budget. Both the uniformity and every-stream work bound are useful here.

## Whole-input coupling closes the apparent interface problem

For every rational p'∈[a/2,1], X≤1+log n and p'^{-1}≤2/a. Choose an integer quasipolynomial upper bound U(n,a) for the source sample budget over this entire interval. It can be chosen as a power of two with an integer exponent that dominates the displayed expression. Constants incorporate the stipulated source constant C. Repeat the source on an odd constant R of independent blocks so that a majority of outputs equals the true string with probability at least .99 at the correct supplied parameter. Such an R exists by a binomial tail bound. Allocate M=RU traces, ignoring unused tails in each block.

Use independent pilot traces to estimate p from Y=length(trace)/n∈[0,1], whose expectation is p. Put δ=1/(100nM). Hoeffding's inequality gives error at most δ/2 with probability at least .99 using O(δ^{-2}) pilot traces. Round to a dyadic mesh of spacing at most δ/2 and clip to [a/2,1], obtaining rational p_hat with |p_hat−p|≤δ on that event. Projection onto this interval cannot increase error because p lies in it. Its encoding has O(log M+log n+bitlength(a)) bits.

Conditional on the pilot, the fresh M traces remain independent at the true p and p_hat is fixed. Couple each input bit's retention at p and p_hat with the same uniform random variable. Across nM possible retained bits, the chance of any disagreement is at most nM|p−p_hat|≤.01. Concatenation of surviving bits and the entire randomized decoding computation are measurable functions of these masks, so total variation of the complete decoder input laws is at most .01. The actual reconstruction success is consequently at least .99−.01−.01=.97. No stability theorem for a particular decoder coefficient or feasibility slack is necessary.

The pilot work, rounding, and every-stream decoder work are quasipolynomial in n at fixed a. Squaring a quasipolynomial budget preserves this class. All randomness, including inaccurate pilot estimates, has the same predetermined finite work budget. The case p=1 is included by the coupling and clipping argument. This is a full compatibility calculation within the stated fixed-a scope; no growing-a^{-1} bound is asserted.

## Closest primary and same-family comparison

Hartung–Holden–Peres, [1708.02216v1](https://arxiv.org/pdf/1708.02216v1), Theorem 1.2 and the actual §4 proofs, already handle unknown letter-specific retention. Lemma 4.1 estimates a rate using the count's mean μ=rp and variance v=rp(1−p), hence p=1−v/μ. The proof then thins estimated channels to a common rate and controls perturbations with Lemma 4.2. Its older time scale differs, but parameter estimation, channel adjustment, and feeding a known-channel reconstruction algorithm are already operative there. For unknown common retention and known n, the simpler length estimator plus entire-input coupling above is compatible with the new source budget. No unpaid reconstruction mechanism remains in this proposal.

The source decoding section was read through `lem:prefix-slack` and its proof, to avoid assuming that an internal coefficient estimate had to be reworked. The quantitative-lower-bounds companion's introduction, `thm:main`, `thm:tv`, and channel-reduction discussion were read: they concern known channels and do not obstruct this quasipolynomial reduction. Its subsequent proof was not read. The latest-anchor companion's retrieved TeX is only a PDF wrapper; its included PDF proof was not retrieved or semantically read. It is not being used for clearance.

I152's actual channel-extension discussion was checked: output-flip debiasing and contamination are separate, while arbitrary position-dependent retention remains a different unresolved interface. This calculation does not settle that interface. No source truth audit, new nomination, or independent contribution classification is made.
