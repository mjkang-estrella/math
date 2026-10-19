# T238B125 — frozen full research target

Assume the pinned OpenAI theorem statements and operative proof contracts at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, in particular source238's conditional coordinate-sweep moment theorem under its exact hypotheses. External classical results are used only under their stated hypotheses.

For every real delta with 0<delta<1/2 there is a finite constant C_delta, depending only on delta and the absolute pinned-source constants, with the following property. For every integer d>=1, let N=2^d. At each integer physical time t>=1 and every x in {0,1}^{d-1}, choose in advance an arbitrary deterministic probability p_(t,x) in [delta,1-delta]. All coin tosses, across pairs and times, are independent. One physical update first swaps the cards at (0,x),(1,x) with probability p_(t,x), independently for each x, then rotates the d coordinates by (b1,...,bd)->(b2,...,bd,b1). This defines a possibly time-inhomogeneous random permutation process Pi_t on all N labelled cards.

For EVERY deterministic initial ordering, EVERY such infinite probability array, EVERY real epsilon with 0<epsilon<=1/4, and EVERY integer t satisfying

    t >= d * ceil(C_delta * (d + log(1/epsilon))),

we have total-variation distance

    ||Law(Pi_t) - Uniform(S_N)||_TV <= epsilon.

Logarithms here are natural. The constant is independent of d, epsilon, all probabilities in the array, and the initial ordering. No periodicity, spatial homogeneity, convergence, or finite description of the deterministic array is imposed. The array is not allowed to depend on realized cards or coins. All N cards and the entire permutation law are part of the conclusion.

Sharpness of the d^2 worst-case order at fixed error is included as a credited consequence of structuralr113: for every fixed p in (0,1) other than1/2 and every alpha in (0,1), put r=|1-2p|. In the homogeneous special case, for every integer sequence s_d>=0 satisfying s_d <= (1-alpha) log(2^d)/(-2log r), the total-variation distance at physical time d*s_d tends to1 as d tends to infinity, from a deterministic ordering. Thus fixed-error mixing in this homogeneous case has order Theta_p(d^2). This lower bound is not claimed as a new operation.

The target is the displayed full all-dimension, all-error, all-deterministic-array upper theorem with that sharpness statement. It may not be replaced by a one-card law, a fixed-size restriction, a subsequence, a homogeneous-only theorem, a near-fair hypothesis, a stationary/commuting approximation, a randomized scan schedule, or a conditional theorem with an unproved path-disintegration bridge. No cutoff profile, adaptive-probability theorem, dimension-uniform behavior as delta tends to0, or algorithm to evaluate C_delta is asserted.

This is a research scope freeze, not an author substantiality rating, independent gate, acceptance, nomination, or count assignment. The earlier detailed calculations are disclosed in prefreeze.md.
