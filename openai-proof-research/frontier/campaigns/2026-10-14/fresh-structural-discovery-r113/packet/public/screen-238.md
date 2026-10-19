# 238 — a biased-rate feasibility screen

No target was frozen. The contemplated extension replaced every independent fair switch in the dyadic Thorp shuffle by an independent Bernoulli(p) swap, for fixed 0<p<1, and asked whether the O(d) physical-shuffle scale at N=2^d persisted. It does not when p≠1/2. The elementary calculation below is a pre-freeze exclusion, not a substantial contribution claim, and no changed-rate upper-bound target is nominated.

## Stronger contracts checked first

In *Optimal-order mixing of the Thorp shuffle*, `lem:path-cylinder` retains independent free coins after exposing paths; `lem:energy-memory` uses exact annihilation of centered mass by one full product of fair coordinate averages; the opposite-half argument then gives the recent-noise contraction. The source gives full-deck mixing, not just uniform one-card marginals.

Two stronger companions were considered. *Compatibility entropy and the spectrum of a Thorp sweep* has `tra:duality:weighted` for arbitrary nonnegative line weights and `tra:duality:moment` for the fair sweep's entire regular singular list. Those are stronger than uniform-line headlines, but the application still has a fair one-card/sparse-representation input. In *Random-subspace tests and trace smoothing for coordinate sweeps*, `prop:coarse-smoothing` and the sparse-row deformation retain the exact one-card uniform projection (proof.tex, opening sections). Arbitrary line weights in the first contract do not grant this latter property for biased switches. Not all twelve family companions were read: retained catalogue mapping and reading limits say exactly which were inspected.

Gaitonde–Mossel, [arXiv:2410.11136v2](https://arxiv.org/pdf/2410.11136v2), Theorem 3.1/Corollary 3.1 and the telescoping proof, compares products of orthogonal projections using their averaged gap. A biased two-site switch has eigenvalues 1 and 1−2p and is not that projection. Even in the projection case the comparison loses a scan-length factor. This primary was tested as a compatible general reduction, not treated as a sharp biased-shuffle theorem.

## Exact statistic and general calculation

Remove deterministic rotations as in the source. One sweep visits each coordinate matching once. A card retains the sign a(label)=(-1)^(label's first bit). Write c_x for the sign of the card at x, and define

    F = Σ_(x∈{0,1}^d) (-1)^(x_1) c_x.

Initially F=N. Every update in a coordinate other than 1 leaves F unchanged, pathwise. At a coordinate-1 pair (x,x+e_1), with x_1=0, its contribution is c_x−c_(x+e_1). Swapping negates this contribution. Set ρ=1−2p and r=|ρ|. Conditional on the deck immediately before this matching,

    E[F_new | deck] = ρ F,
    Var(F_new | deck) ≤ (N/2)·16p(1−p) = 8Np(1−p).

The second bound sums independent pair variances; each contribution has magnitude at most 2. Updates in the other coordinates do not affect this observable, so at sweep endpoints, with F_s after s sweeps,

    E F_s = Nρ^s,
    Var F_s ≤ ρ² Var F_(s−1) + 8Np(1−p)
            ≤ 2N(1−ρ^(2s)) ≤ 2N.

Here F_0 is deterministic and 1−ρ²=4p(1−p). This calculation handles p>1/2 as well as p<1/2, without invoking a positive-eigenvalue lemma outside its hypotheses.

Under a uniform permutation, the c_x form a uniformly chosen balanced sign vector. Thus E_U F=0 and E_U[c_xc_y]=−1/(N−1) for x≠y. Since the position signs sum to zero,

    Var_U F = N + N/(N−1) = N²/(N−1).

For p≠1/2, use the event sign(ρ^s) F ≥ Nr^s/2. Chebyshev's inequality on the chain and stationary laws gives the explicit lower bound

    TV(Law(Π_(sd)), Uniform(S_N))
      ≥ 1 − 8/(N r^(2s)) − 4/((N−1) r^(2s)).

For every fixed ε∈(0,1), if

    s ≤ (1−ε) log N / (−2 log r),

the right side tends to one as N=2^d tends to infinity. At sweep endpoints the rotating and physical frames agree. Consequently the physical mixing time has an Ω_p(d²) lower bound for every fixed p∈(0,1)\{1/2}. In particular, no constant number of sweeps can mix. The p=1/2 source is untouched: then ρ=0 and this persistent observable disappears after its first update.

This is the classical eigenfunction/second-moment method, compared with Wilson, *Mixing times of lozenge tiling and card shuffling Markov chains*, [arXiv:math/0102193v1](https://arxiv.org/pdf/math/0102193v1), §3.3 Lemma 5 and its proof. We use the displayed conditional variance recursion directly rather than importing that lemma beyond its stated eigenvalue restrictions. We claim no priority for the application. The finite enumeration in `diagnostics.py` checks the local moments and stationary variance only; the general proof is the calculation above.

No corresponding upper bound, cutoff, arbitrary-bias-array statement, or optimum-rate theorem is established. In particular, the obstruction is not used to advertise a solved full frontier problem or to rescue a narrower candidate.
