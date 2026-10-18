# Family342 relative parametric compatibility: technical deduction, no nomination

Myeongjin Kang, no affiliation. Original prose CC BY4.0. Source truths at pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. This screen is a complete technical deduction, not a substantial campaign candidate. It was selected before proof, with the following full scope; no constant anti-invariant Betti number or fixed cohomology restriction has been added.

## Exact screened statement
Let X be a closed connected oriented smooth real four-manifold and B a compact smooth parameter manifold, possibly with boundary. Let J_b be a smooth family of orientation-compatible almost complex structures, each tamed by some symplectic form. Let A be a closed subset of B, and suppose a smooth family eta_b of closed J_b-compatible forms is specified on an open neighborhood U of A. Then there is a smooth family omega_b of closed J_b-compatible forms on all B agreeing with eta_b on an open neighborhood of A contained in U. For A empty no initial data are required. Cohomology classes are allowed to vary. The prescribed forms are closed along X; no assertion of closedness as a two-form on B times X is made.

## Proof, including jumping cokernels
Choose a smooth family g_b of J_b-Hermitian metrics, for example by averaging a fixed metric with its J_b-pullback. Write R_b for the orthogonal projection onto E_b=Lambda^-_{J_b}, whose elements are self-dual for g_b in dimension four. Fix closed smooth representatives h_1,...,h_N of a basis of H^2(X;R); they may be harmonic for one fixed auxiliary metric. No parameter-dependent harmonic basis is used.

On sections of E_b define

P_b u = R_b d d_b^* u + sum_i (R_b h_i) <R_b h_i,u>_b,

where the pairing is the real L2 pairing on X. This is an elliptic nonnegative self-adjoint operator of order two: the first term has the surjective-symbol property of R_b d and the second is finite rank smoothing. Its quadratic form is

<P_bu,u>_b = ||d_b^*u||_b^2 + sum_i |<h_i,u>_b|^2.

For a kernel element, elliptic regularity gives smoothness and d_b^*u=0. Self-duality gives du=0. Moreover <h_i,u>_b=integral_X h_i wedge u=0 for every i. Poincare duality then gives [u]=0, or equivalently one may express [u] in the h_i basis to get integral_X u wedge u=0. But u is self-dual, so this integral is ||u||_b^2. Thus u=0. Self-adjoint elliptic Fredholm theory gives invertibility H^{s+2}(E_b) to H^s(E_b).

This argument works for every b, irrespective of jumps in h^-_{J_b}. Local bundle identifications, openness of bounded invertibility, the inverse identity, and elliptic regularity give smooth b-dependence of P_b^{-1} on each Sobolev scale. Local choices agree because each inverse is unique. Compactness of B is only used for a finite local cover below, not for eliminating a hypothetical kernel jump.

Define a closed lift

D_b alpha = d d_b^* P_b^{-1} alpha + sum_i h_i <R_b h_i,P_b^{-1} alpha>_b.

Then d D_b alpha=0 and R_bD_balpha=alpha. It is a smooth parameter family of order-zero operators. The finite-rank term is essential: using d d_b^* alone misses the harmonic anti-invariant cokernel. Unlike a varying projection onto that kernel, this fixed-cohomology augmentation remains smooth at dimension jumps.

By source342 thm:main, for each b0 choose a compatible closed form sigma at J_b0. On a neighborhood of b0 set sigma_b=sigma-D_bR_bsigma. These forms are closed and invariant, and sigma_b0=sigma. Smoothness and compactness of X imply positivity on a smaller parameter neighborhood. Take a finite such cover and a smooth subordinate partition of unity rho_i on B. The sum omega_b^0=sum_i rho_i(b) sigma_b^i is closed along X, invariant, and positive, since all coefficients are nonnegative and sum to one.

Choose a smooth cutoff chi on B supported in U and equal to one on a neighborhood V of A; compactness and A closed allow V with closure in U. On U put omega_b=chi(b)eta_b+(1-chi(b))omega_b^0, and extend by omega_b^0 elsewhere. The formula is smooth because the cutoff has support in U. Convexity again preserves compatibility and X-closedness, and agreement holds on V. This proves the exact statement.

## Contribution comparison and limits
Source341 (October7), build/sections/05-families.tex, lem:compatible-family, already applies a smooth elliptic closed lift to a fixed compatible form, then patches with parameter partitions of unity. Its explicit rank-two kernel is smooth; our fixed H^2 stabilization removes the constant-kernel assumption by ordinary elliptic stabilization. Source342 (October6), build/sections/02-currents.tex, lem:lift, supplies the underlying closed lift. Its proof credits Lejmi2006 and Draghici-Zhang2012. The source pointwise theorem supplies all existence input. The relative cutoff adds only convex interpolation. Consequently the full screened statement is a technical transfer, not an unpaid substantial bridge. No campaign nomination or acceptance is requested.

There is no fixed-cohomology conclusion: the h_i correction changes class, and a prescribed class can fail compatibility. There is no claim of a symplectic form on the total parameter product. No constant h^-_J hypothesis is necessary. No restriction to a coefficient sphere is used. Removing those restrictions from the source family lemma does not itself establish substantiality.
