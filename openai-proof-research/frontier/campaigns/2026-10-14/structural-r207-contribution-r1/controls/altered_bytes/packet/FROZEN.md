# R207 frozen author statement

Provenance: Codex / GPT-6 Astra / xhigh / default service tier. This is a discovery-stage author statement, not an assigned correctness/contribution/acceptance grade. Pinned Source331 and all its operative proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Frozen after operative reading of all seven companions, the recorded primary proof reads, guarded original-history reads, and the feasibility calculations in DERIVATIONS.md. No downstream formalization or manuscript is included.

## Compact-law criterion for one inhomogeneous product tree

Work over the real scalars. Let V=N^{<omega}, with root emptyset, so every vertex has countably infinitely many children and arbitrarily long finite paths exist. For every parent v in V let mu_v be a probability law on [0,infinity) with integral w dmu_v(w)=1. Let K be the closure of {mu_v:v in V} in the first Wasserstein metric

    d_1(mu,nu)=inf E|U-V|,

where the infimum is over couplings with these laws. Assume K is compact and

    rho_0 := inf_v integral |w-1| dmu_v(w) > 0.

On the countable product probability space take mutually independent W_{v,j}, j in N, with law mu_v. Thus siblings have the same law; different parents may have different laws. For z in V put P_emptyset=1 and let P_z be the product of the multipliers along the root-to-z path. Define X as the closed real linear span of all P_z in the probability L1 space, with its inherited norm ||.||_1.

For t>0 define

    Delta_X(t) = inf_{||x||_1=1} sup_{F closed linear, dim(X/F)<infinity}
                 inf_{y in F, ||y||_1>=1}
                 [ (||x+t y||_1+||x-t y||_1)/2 - 1 ].

Then X is a separable infinite-dimensional Banach space, and the following equivalence holds:

    Delta_X(t)>0 for every t>0
    if and only if
    mu((M,infinity))>0 for every mu in K and every finite M>0.

Equivalently, the inherited norm is asymptotically midpoint uniformly convex (AMUC, also in the usual maximum convention) precisely when every law in K is essentially unbounded. No assertion of reflexivity, Daugavet property, compactness in measure, or an FDD/basis is part of this statement.

Here is a law-dependent quantitative bound in the unbounded case. For independent W,W' of law mu set

    alpha_K = min_{mu in K} E|W-W'|,
    C_K = 1 + 2 sqrt(3)/alpha_K.

For r>0 define Theta_K(r) as the infimum of

    E( |sum_{i=1}^n a_i D_i| - r )_+

over every integer n>=1, every real coefficient list (a_i), and every list mu_1,...,mu_n in K, where all W_i,W_i' are mutually independent, W_i,W_i' have law mu_i, D_i=W_i-W_i', and the normalization is E|sum_i a_i D_i|=1. Then alpha_K>=rho_0>0, Theta_K(r)>0 for every r>0, and

    Delta_X(t) >= [t/(4 C_K)] Theta_K(4 C_K/t) > 0     (t>0).

In the bounded-limit case the conclusion is stronger than mere failure of the displayed equivalence: there exists t_*>0 such that Delta_X(t)=0 for every 0<t<=t_*. The maximum asymptotic midpoint modulus is also zero at all these radii. The law may occur only as a limit in K; it need not be assigned to a vertex.

Independently of which side of the equivalence holds, no equivalent norm on X is asymptotically uniformly convex. Precisely, if N is any norm on X and

    a ||z||_1 <= N(z) <= b ||z||_1     (z in X),   0<a<=b<infinity,

then its one-sided modulus

    delta_N(t) = inf_{N(x)=1} sup_{F closed linear, dim(X/F)<infinity}
                 inf_{y in F, N(y)=1} [N(x+t y)-1]

satisfies delta_N(t)=0 for every 0<t<=a rho_0/b.

All these assertions assume only the first moments written above. Multipliers may vanish. Compactness is in d_1, not merely weak convergence of laws, and the criterion concerns all laws in the closure, not only the laws actually assigned to vertices. The lower bound is uniform in centers and finite coefficient lists but depends on the entire fixed family K. It makes no claim of a universal lower bound over different compact families.

COPY CONTROL PERTURBATION
