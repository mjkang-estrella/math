# I295 — Gaussian rearrangement and restricted global soft stability

2026-10-13. **S128 is proved here on every compact rectangle with ρ₁a₁<1/√2, for all arbitrary kernels and all dimensions. Full S128 on all compact rectangles remains unresolved.** No acceptance nomination or worldwide-priority claim is made. The user updated the current total to 13/20 during this assignment; no counts or frozen input snapshots are edited.

The [complete proof](../experiments/i295_gaussian_rearrangement_stability/analysis.md), [reading and failure log](../experiments/i295_gaussian_rearrangement_stability/reading-and-failures.md), [authentication manifest](../experiments/i295_gaussian_rearrangement_stability/input-authentication.json), and [literature comparison](../sources/i295_gaussian_rearrangement_stability/literature.md) distinguish proved operations from the remaining large-amplitude obligation. All pinned OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated.

## Exact theorem

Let X be uniform on {−1,1}^n, u:{−1,1}^n→[−1,1],

    ψ(t)=((1+t)log(1+t)+(1−t)log(1−t))/2,
    I(u)=Eψ(u)−ψ(Eu), I(u)=ψ(a).

Fix 0<a₀≤a₁<1 and 0<ρ₀≤ρ₁<1 with **ρ₁a₁<1/√2**. There exists C depending only on these four endpoints such that for every n≥1, a∈[a₀,a₁], ρ∈[ρ₀,ρ₁], and every such u,

    min_(i,ε∈{−1,1}) E|u−εaX_i|²
       ≤C[ψ(ρa)−I(T_ρu)].                         (S295)

Bias, endpoint values, rare spikes, and unbounded complexity are all included. There is no initial closeness premise. The parameter condition is a real restriction; it is not removed or advertised as optimal.

## Paid Gaussian operations

**R295.** Every Gaussian kernel v:R^N→[−1,1] has a nondecreasing scalar rearrangement v* with the same entire input law and

    I_G(v*)=I_G(v), I_G(Q_σv)≤I_G(Q_σv*)

for 0<σ<1. Shift to f=(1+v)/2. Borell's two-set theorem applies to an arbitrary output set and every level set {f>t}. Parallel upper halfspaces attain all of these comparisons simultaneously for f*. Largest-p integrals and stop-loss functions prove convex order, hence the entropy inequality. This preserves mean as well as input information. The actual complete Mossel–Neeman §2 primary semigroup proof was read; its normalization and endpoint passage were checked directly, not inferred from the parent-read statement alone.

**E295.** Scalar ordinary EPI, applied separately to biased binary posterior laws and followed by convex Jensen in their differential entropies, gives

    I_G(Q_σv)≤B_σ(I_G(v)),
    B_σ(J)=−½log(1−σ²+σ²e^(−2J)).

This becomes dimension independent only after R295. Posterior densities are bounded by a constant times the scalar Gaussian density, so entropy and second moments are finite even at kernel endpoints. Rioul's actual primary proof and equality argument were read. Strictness below this EPI curve at positive information is also proved, using a preliminary smoothing split to handle nonsmooth posteriors.

**G295-small.** For every 0<b₀≤b₁<1/√2 and 0<σ₀≤σ₁<1, there is an explicit η_G>0, independent of Gaussian dimension, such that exactly I_G(v)=ψ(b) implies

    I_G(Q_σv)≤ψ(σb)−η_G.

Indeed H(x)=exp(−2ψ(√x)) has

    H″/H=atanh(r)²/r²−[r/(1−r²)−atanh(r)]/(2r³), r=√x,
    H″/H≥1−1/[2(1−x)]>0 (x<1/2).

A strong-convexity chord gap between 0 and b² pays the uniform difference between B_σ(ψ(b)) and ψ(σb). Analysis §4 gives η_G and the full algebra.

## Why the arbitrary-kernel theorem follows

Choose a fixed λ with ρ₁<λ<min{1,1/(√2a₁)}, and put σ=ρ/λ. I128's integrating factor pays the information of h=T_λu near ψ(λa) whenever the original deficit is small. Both λa and σ remain in compact ranges where G295-small applies.

I290's increasing diffuse transfer works at this unequal split. The spectral tail is λ^(2(d+1)); monotonicity gives actual polynomial influences at most λ max_i û(i); σ-noise multiplies degrees by σ^j and contracts L2. Fixed-degree Lindeberg replacement, Gaussian clipping, entropy and mean continuity, and exact Gaussian amplitude b=ψ⁻¹(I_G(v)) then contradict a diffuse sequence of vanishing deficit. Analysis §5 displays these bounds and the order of limits.

Thus there are β,η>0 such that increasing kernels with max singleton≤β have deficit≥η. In that sector d_a≤4 pays the linear estimate. I290 B290 pays the complementary marked-singleton sector. Its positive-time global entrance, original-information backward step, and spike-tolerant I131 L131 theorem are retained at their original scopes. Finally I131 Q131b transfers the increasing estimate to every arbitrary u. No Gaussian closeness assumption or inversion of noise is introduced.

## Exact remaining obligation for all rectangles

R295 also pays compact one-dimensional optimization. Bounded monotone functions are compact in Gaussian L2 by Helly selection and dominated convergence. OU output and information depend continuously on both the kernel and σ. Exact positive information constraints define a compact feasible set. Hence the dimension-free uniform G290 on all compact rectangles would follow from the following pointwise statement:

    Every nonconstant nondecreasing w:R→[−1,1] with
    0<I_G(w)<log 2 satisfies, for every 0<σ<1,
    I_G(Q_σw)<ψ(σψ⁻¹(I_G(w))).                    (U295, unpaid)

The non-strict version follows from the stipulated cube contraction by I290's conditional block-sum approximation. U295 is not proved here.

Strict EPI and scalar compactness give a uniform improvement over the EPI curve, but that curve can exceed the cube curve near large amplitude and correlation. The required reserve comparison is not supplied by nonattainment. Real analytic continuation was seriously investigated: the actual primary MMSE Proposition 8 and Appendix D impose complex nonvanishing/tail-ratio conditions, which the posterior bounds do not establish. Equality propagation to an earlier finite interval is valid; continuation to later low-information times remains unpaid. Ordinary LSI nonattainment still leaves I290's reserve F(I)−2I unpaid. Borell halfspace equality concerns a different functional.

## Contribution comparison and disposition

Borell, scalar EPI, Gaussian bottleneck bounds, Helly compactness, and Lindeberg are old machinery. The parent supplied the proposed route and conservative curvature lead. I128 supplies the ODE and original-budget bridge; I131 supplies compression and local/backward stability; I290 supplies all fixed positive singleton sectors and the diffuse Gaussian transfer. Those are credited dependencies, not reclassified as I295 contributions.

This round verifies the parent lead and completes the previously unpaid restricted regime into a global arbitrary-kernel theorem. It also replaces the unrestricted-dimensional Gaussian strictness obligation by a compact scalar pointwise one. It does not prove full S128 or establish worldwide novelty. The external Boolean/global/local comparisons authenticated in I290 retain their stated scopes; they were not replayed as a new exhaustive literature review. Parent contribution and acceptance gates remain separate.

Only assigned proof and evidence files were written. No subagents, live sibling reads, shared-index edits, numerical scans, staging, commits, or publication. Output hashes are supplied detached from the files.
