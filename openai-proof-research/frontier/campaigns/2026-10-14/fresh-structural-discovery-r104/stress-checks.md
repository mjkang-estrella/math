# Targeted normalization and interface checks

These are author checks, not independent review. Full frozen scope unchanged.

## Actual band traces

For the actual encoded first coordinate D_1+epsilon H_1, take the norm-continuous path D_1+s epsilon H_1, 0<=s<=1. With epsilon||H_1||<1/4 its k spectral clusters remain separated. Their Riesz projections vary continuously in operator norm. Two projections at norm distance less than1 are unitarily equivalent (polar decomposition of their intertwiner); subdividing the path therefore gives equivalence of each endpoint projection to E_ii tensor1. Its normalized trace is exactly1/k. Only after this argument is moment convergence used to infer the asymptotic matrix ranks. This avoids inferring the actual ranks from a mere perturbation-of-moments assertion.

The polar synchronization of these projections with the original scalar matrix units is norm-close to the identity, uniformly in the coefficient algebra. Tree blocks remain invertible between their corners by the Neumann inverse, since their zero-perturbation block is a matrix unit. Thus the actual polar-coordinate pair is D+O(epsilon), as used in the root truncation.

## Orbit metric and c_D

Take a Hermitian basis H_a of M_k orthonormal for tr_k, and a Hermitian basis K_b of M_d orthonormal for Tr_d. Then H_a tensor K_b has squared Tr_(kd) norm k. The corresponding unit Lie-algebra vector is (H_a tensor K_b)/sqrt(k). Its commutator image has exactly the same normalized scalar singular value as H_a under L. Thus every nonzero scalar singular value appears d² times, with no additional k or d factor, giving c_D^(d²).

For the stabilizer, I_k tensor K_b has squared norm k, so the group embedding multiplies its d²-dimensional Riemannian volume by k^(d²/2). For the normal fiber, V_a tensor K_b has pair norm sqrt(k), giving (epsilon sqrt(k))^(n d²). These are three different uses of the same normalized scalar metric; their factors must not be combined twice.

The logarithmic dimension terms are

 source: -(n/2)d² log d;
 orbit:  -((k²−1)/2)d² log d;
 output normalization: +(kd)² log(kd).

Since n+k²−1=2k², all log d terms cancel. The orbit contributes -(k²+1)d² log k/2 and the fiber contributes +n d² log k/2, which also cancel. The output log k survives as part of C_D. The k=1 formal check gives n=2, empty orbit, C_D=0 and the ordinary scalar scaling formula.

The bounded numerical diagnostic checks k=2,3,4 and d=1,2,3. It compares the full amplified commutator Gram spectrum to the scalar spectrum repeated d² times and separately records the exact cancellation of exponents. It is a normalization diagnostic, not a proof of global tube injectivity or microstate recovery.

## Coefficient action and adjoint placement

For an entry coefficient a tensor b the inserted derivative term is

 prefix * (E_ib tensor a) tensor (E_ci tensor b) * suffix.

Thus a is on the inner right side of the first-leg prefix and b on the inner left side of the second-leg suffix. This insertion commutes with both outer actions, hence the Leibniz rule holds. Applying arbitrary outer multiplication to an already defined derivative would not have this property and is not used.

Directly, on E_ij p the unweighted Delta_a,bc trace contraction is delta_ib delta_jc/k² times the entry contraction. Pairing against E_cb xi_a/k under tr_k tensor tau gives exactly the same expression. Hence the leading score coefficient is V_aj/(epsilon k²), not 1/(epsilon k) or 1/(epsilon k³). Nonconstant inserted coefficients use the standard entry adjoint product rule; the absolute differentiated Neumann series ensures its domain and L² bounds. Matrix-unit equivariance is built into the w_bc relation and remains valid for inserted entry coefficients because all entry coefficients commute with scalar matrix units.

The diagnostic k=2,3,4 verifies the normal coarse Gram identity and its annihilation by J*. It does not test existence of conjugates by finite matrices (which would be an invalid diagnostic).

## Relative entropy and the original limsup

Actual primary reads: Shlyakhtenko math/9812079v1, Definition2.3 and Remarks2.4/Propositions2.7–2.8 (text65–165), Theorem2.19 and proof/Corollary2.20 (270–365), Theorem4.1 and its stated hypotheses in Section4 (410–605). This is the supremum-over-conditioning-models relative entropy, with the original limsup, not an ultrafilter definition or a joint-minus-conditioning entropy. Its fiber inclusion gives chi(H)>=chi(H|T).

Only the particular case needed here is used: T is a finite semicircular tuple, scaled by fixed sqrt(U)>0, and is free from A=X+sqrt(U)S. It has bounded matrix models in EVERY sufficiently large size. The free-relative equality chi(A|W*(T))=chi(A) therefore retains every source subsequence: uniform asymptotic freeness of bounded deterministic A models with independent GUE T, followed by averaging over T, provides a conditioning model whose good A fiber has a proportion tending to1. No coincidence of two unrelated limsup subsequences is required. The actual Theorem2.19 states this equality; the all-size semicircular models also make the requisite subsequence point explicit in this application.

The power series H_epsilon(A,T) and its inverse are constructed in a common strictly larger multiradius by the contraction in matched-volume-attempt.md F. Coefficients lie in W*(T), and the variables A and H remain self-adjoint. The Jacobian differs from identity by O(epsilon) in projective norm, which dominates the represented operator norm. Its logarithmic determinant trace has absolute value at most n times O(epsilon). Theorem4.1 therefore applies with the same original-limsup convention. It does not imply or substitute for a nonmicrostates change-of-variables theorem.

## Current status

The previously identified Fisher upper-continuity concern is bypassed by the exact free normal/orbital decomposition. The proposed matched-volume argument supplies a concrete treatment of all ranks and original matrix-size limsup. The remaining author task is to consolidate the proof with every uniform reconstruction estimate, primary attribution and packet identity. No independent review or completed gate is asserted by these checks.
