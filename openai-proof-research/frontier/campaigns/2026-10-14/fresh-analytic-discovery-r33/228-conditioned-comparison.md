# Conditioned comparisons: a paid soft version and the hard contour gap

Myeongjin Kang. Original prose CC BY 4.0. No nomination; the lemma below is a technical extension of the stipulated local moment operation, not a claim of a finite-range transition.

## Setup and soft block lemma

Use exactly the small cells C_i, constants D_0,B_0,M, source admissibility D_0>=8M, and finite-volume pair-interaction family of family228 `f:modified-energy`. All intra-small-cell core terms remain present; attractive row sums are <=M. Fix t and a compact parameter rectangle beta in [beta_-,beta_+], |h|<=H. Partition the finite collection of small cells into arbitrary blocks B. Write N_B=sum_{i in B} n_i and choose arbitrary V_B>0. Let F_B:[0,infinity)->R satisfy F_B(0)=0 and |F_B(x)-F_B(y)|<=K|x-y| with the SAME finite K. Multiply the ordinary grand canonical weights by

    exp(-sum_B V_B F_B(N_B/V_B)).                    (S1)

The functions may depend on volume and on the block, and can be nonsmooth. No beta factor is included in (S1); if it is, replace K by beta_+ K. The volume of a block is not required to be the chosen normalization V_B for this bound.

Claim: there is C_exp(t,parameter rectangle,K), independent of the volume, block sizes, normalizations, attraction ranges and permitted pair deletions/interpolations, such that

    E_F exp(beta D_0 n_i^2/4) <= C_exp

for every small cell i. In particular E_F n_i n_j<=C_1 with the same uniformity.

Proof. Since |sum_B V_B F_B(N_B/V_B)|<=K N, the source's quadratic total-count bound still proves finiteness of the partition function and of each exponential-moment numerator in each fixed volume. The empty global configuration has weight one. Thus the finite-volume maximum F_max of the cell exponential moments is finite before the maximum argument is used.

Condition on all particles outside cell i. Only the block containing i changes its penalty. Relative to the empty inside-cell configuration, the added penalty differs by at most K n. Divide the conditional numerator and denominator by the outside-only weight, including its block penalty. The denominator again contains the empty-cell term one. The source conditional energy estimate therefore yields

    E_F[exp(u_0 n_i^2)|outside]
      <= C_2(K) exp(beta G_i^2/D_0),
    u_0=beta D_0/4, G_i=sum_{j!=i} J_ij n_j,
    C_2(K)=sum_{n>=0} b^(3n)/n!
              exp[-7 beta_- D_0 n^2/16+(tH+beta_+B_0+K)n].

This constant is finite and >=1. The remainder of the source argument is unchanged, with eta=4M^2/D_0^2<=1/16: weighted Cauchy–Schwarz and Jensen give E_F exp(beta G_i^2/D_0)<=F_max^eta. Hence F_max<=C_2(K) F_max^eta and F_max<=C_2(K)^(1/(1-eta)). Mixed second moments follow by Cauchy–Schwarz. This proves the claim.

Keeping the same block penalties while interpolating pair interactions, finite-volume differentiation is still justified by the quadratic grand-series domination (with K N added). It follows that

    |log Xi_F(v_1)-log Xi_F(v_0)|
       <= beta C_1(K)/2 * sum_ij J_diff,ij.          (S2)

Thus deleting reference interactions across large boxes has the same O(R_0/s) normalized logarithmic error, with a K-dependent constant. This is a direct proof for soft restrictions and not an assumption of source truth for the new penalized model.

## Why this does not complete a hard phase/contour comparison

For an event A prescribing the block density in a closed interval bounded away from zero, emptying a single small cell can violate A. The conditional denominator in the above proof need not contain the empty-cell configuration. Dividing an unconditional estimate by P(A) introduces an uncontrolled loss depending on all prescribed blocks. This can be exponentially small in the number of blocks and is not a contour-area estimate.

One can approximate the hard event by F_B(d)=K dist(d,I_B). These are admissible soft penalties for each finite K, but C_2(K) and the resulting interpolation constant are not uniform as K->infinity. In fact this particular displayed series bound grows at least exponentially in a positive constant times K^2 for large K (choose an integer n proportional to K; log(n!)=O(K log K)). Consequently the calculation above does not justify the hard limit. This is a limitation of the bound, not a proof that a hard conditional moment estimate is false.

A sufficient next interface would control phase-restricted partition-function ratios uniformly in the shapes and number of constrained blocks, with errors supported near the actual phase interfaces, and then establish a three-phase Peierls estimate with two tunable parameters. Source pressure comparison does not supply either statement. No substitute target restricted to soft phases or a fixed grid is proposed.

## An additional elementary obstruction to importing continuum reflection positivity

For the attractive kernel alone, suppose the one-dimensional normal slice k(r) is continuous, compactly supported on [0,infinity), not identically zero, and the matrices [k(s_i+s_j)] are positive semidefinite for every finite family s_i>0. The diagonal condition implies k(r)>=0 for r>0. Let R be the positive supremum of its nonzero support. Choose r in (R/2,R) with k(r)>0, choose t with R/2<t<r, and put s=r-t>0. Then k(2t)=0 but k(s+t)>0. The two-by-two determinant is -k(r)^2<0, a contradiction. Continuity also excludes a function supported only at r=0.

This rules out one specific shortcut: a nonzero compact radial attraction cannot have the full continuum Hankel positivity used to obtain Gaussian reflection positivity by a positive cross-kernel decomposition. It does not rule out lattice reflection positivity, the primary boxed model, other reflection arguments for full Gibbs measures, or finite-range radial phase transitions.
