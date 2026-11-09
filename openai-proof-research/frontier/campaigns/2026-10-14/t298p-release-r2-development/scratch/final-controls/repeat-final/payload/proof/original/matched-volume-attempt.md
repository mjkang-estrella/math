# Matched normal-tube volumes: full upper step under construction

Author proof attempt toward the unchanged scope. The coarse Fisher construction has reduced the remaining task to this volume statement. This note gives the proposed full argument, with the uniform recovery/truncation lemma made explicit for scrutiny. It is not an independent proof/contribution verdict or a nomination.

Fix k, D=(diag(1,...,k), tree adjacency), n=k²+1, and a normalized-trace orthonormal normal basis V. Write E_epsilon(X)=D+epsilon sum_a V_a X_a. Let ||X_a||<=R. All constants may depend on k,R,D, but never on matrix size. Epsilon is sufficiently small, fixed before moment accuracy is sent to zero.

The desired volume formula is

 chi(E_epsilon(X)) = k^-2 chi(X) + (n/k²) log epsilon + C_D + O_(k,R)(epsilon).       (MV)

Here chi is the original cutoff/limsup entropy. For our source chi(X) is finite. The constant C_D is independent of X and epsilon. The two inequalities, rather than equality of a limit as matrix size varies, suffice.

## A. Uniform global normal tube

At size N=kd the base orbit is U(kd)/(I_k tensor U(d)). The normal fiber is V tensor Herm(d). The associated normal bundle uses the conjugation action of U(d) on all coefficient matrices. Its map to the ambient pair space is

 [U,Y] -> U(D tensor I_d+Y)U*.

For ||Y||op small, this map is injective on the associated bundle, uniformly in d. Here is the intended quantitative proof, extending finite-entropy-chart.md. The finite coefficient derivative at Y=0 is an isomorphism from the orthogonal complement K_d of I_k tensor Herm(d), plus the normal space, to the pair space. Its inverse has both an operator-norm bound and a Hilbert-Schmidt bound independent of d. On a small operator-norm ball, differentiation of exp(iK) gives the same bounds for the perturbation of this derivative. Integration along segments proves local injectivity, as in that note.

To pass to global injectivity, two representations of a pair with normal displacements of norm at most r have a transition unitary U with ||[U,D_s]||<=2r. The separated diagonal entries of D_1 imply that every off-diagonal block of U has norm O_k(r). The tree edges of D_2 imply that its diagonal blocks differ by O_k(r). Thus U is O_k(r) close to I_k tensor a unitary V: first take the average diagonal block, then its polar part. In a neighborhood of that subgroup, the map (K,V)->exp(iK)(I_k tensor V), K in K_d, has an analytic inverse of uniform operator-norm radius. This follows from the bounded direct-sum projection onto K_d and its complement and the exponential power series (or its quantitative contraction proof); all bounds are finite coefficient bounds independent of d. Reducing by V now places the two representations in the local injectivity chart. Hence they coincide in the associated bundle.

At a normal displacement ||Y||op<=epsilon C_R, the differential differs from the zero-section differential by relative Hilbert-Schmidt operator norm O_(k,R)(epsilon). This follows from ||[K,Y]||_HS<=2||Y||op||K||_HS. The normal connection only changes the block form by a triangular shear of determinant one. Thus the volume Jacobian relative to base-orbit volume and Euclidean normal-fiber volume is between exp(-C epsilon d²) and exp(C epsilon d²).

Let A_d be the Riemannian volume of the base orbit in the unnormalized Hilbert-Schmidt metric on pairs. If c_D is the product of the k²−1 positive singular values of H->(i[H,D_1],i[H,D_2]) on normalized scalar Hermitian coefficients, then

 A_d = c_D^(d²) Vol(U(kd))/[k^(d²/2) Vol(U(d))].

The Lie-group volumes use the unnormalized Hilbert-Schmidt metric. The denominator scaling k^(d²/2) comes from the embedding V->I_k tensor V. Standard unitary-group volume evaluation gives, with c=3/4+(1/2)log(2pi),

 log A_d/d² = -((k²−1)/2)log d -((k²+1)/2)log k +(k²−1)c+log c_D+o(1).

Only this convergent asymptotic, shared between endpoints, is needed. It also follows directly from Vol(U(l))=(2pi)^(l(l+1)/2)/(1!2!... (l−1)!) and Stirling summation.

## B. Lower bound, all source subsequences retained

A bounded source microstate set Gamma_d(X) is invariant under simultaneous U(d) conjugation. The global associated bundle over this fiber is injectively mapped to microstates of E_epsilon(X), after the usual choice of source moment parameters. The linear map from the n coefficient matrices to Y has real Jacobian (epsilon sqrt(k))^(n d²), because V is orthonormal for normalized tr_k whereas ambient volume uses Tr_(kd).

Consequently

 Vol Gamma_(kd)(E_epsilon(X))
 >= A_d (epsilon sqrt(k))^(n d²) Vol Gamma_d(X) exp(-C epsilon d²).

Every subsequence of source sizes realizing its original limsup gives a subsequence kd of output sizes. No ultrafilter or replacement of limsup by liminf is used. Substitution of the preceding A_d asymptotic and of both entropy normalizations gives the lower inequality in (MV), with

 C_D = log k + ((k²−1)/k²)c + (log c_D)/k².

In particular the log d terms and the fiber/orbit log k terms cancel exactly.

## C. Uniform recovery after removing vanishing rank

The following is the precise upper-step lemma to justify, not a mere appeal to closeness of moments in operator norm.

For fixed small epsilon and any desired source moment parameters and any theta>0, sufficiently accurate bounded microstates Z of E_epsilon(X) in arbitrary size N have a projection P of rank kd, with kd>=(1−theta)N, such that PZP is in the global normal tube and its recovered normal coefficients are source microstates with the desired parameters and a fixed cutoff R' independent of N and theta. The cutoff can exceed R. The parameter theta is sent to zero after N->infinity, at fixed epsilon.

Construction:

1. The actual first coordinate has k separated spectral bands around 1,...,k. Take those spectral projections in a matrix microstate. The complement has rank o(N), and each band has rank N/k+o(N). These assertions follow from moment convergence and bounded cutoff by approximating continuous functions which are one on the bands and zero on their separating neighborhoods; the actual spectral law has no mass in those neighborhoods.

2. On each tree edge, the actual band-to-band block of the second coordinate is a perturbation of the identity and has all singular values in a fixed interval, for example [1/2,2] after epsilon is reduced. Use the polar partial isometry of the corresponding matrix block, restricting to singular values in a slightly larger fixed interval. The excluded initial/final spaces have rank o(N), by the same bounded continuous functional-calculus argument applied to the squared singular-value operator. Start at one root band. Along the finitely many tree paths, pull back the domains of these partial isometries and intersect them in the root. The common root space has dimension N/k−o(N). The path maps restricted to it are isometries with pairwise orthogonal ranges in the k bands. They therefore define exact matrix units on their sum. There is no cycle condition.

3. Pull the compressed Z entries back to the root by those isometries. Their joint normalized moments converge to the polar-coordinate entries of the actual E_epsilon(X). This follows by continuous functional-calculus approximation to each bounded truncated polar map and by the rank estimate: changing or compressing bounded matrices on o(N) dimensions changes every fixed normalized trace word by o(1). In the actual law the polar coordinate pair differs from D by O_(k,R)(epsilon) in operator norm.

4. For each of the finitely many real and imaginary Hermitian parts of these root entries minus the scalar entries of D, cut away the spectral subspace where its magnitude exceeds twice its actual O(epsilon) norm bound. Each removed rank is o(N): use an even moment of arbitrarily high fixed degree, then the microstate accuracy, or a continuous cutoff separated from the actual spectrum. Intersect these good root subspaces and restrict ALL path isometries to that one intersection. Matrix units remain exact. Each new compressed entry is bounded in norm by the chosen threshold; hence the entire compressed pair is O_(k,R)(epsilon) close to D in operator norm. The total lost rank is still o(N).

5. Apply the uniform normal-tube inverse from A. It has a convergent noncommutative power series locally, composed with the bounded polar-coordinate operations above. Its coefficients have a fixed cutoff R'. Its joint moments are the source moments: for the actual encoded pair, normal-tube uniqueness recovers the original normal tuple up to a common root unitary. Polynomial approximation on the uniform operator-norm domain transfers this assertion to microstates. Thus desired source moment accuracy is obtained by sufficiently accurate output moments.

The rank estimates in this construction are uniform over sufficiently accurate microstates, by the explicit functional-calculus/polynomial estimates. They do not require that a whole microstate be close in operator norm to the base orbit. The second root truncation is essential for precisely that reason.

Remaining scrutiny point: verify the normal-tube analytic inverse in A with the same uniform radius used in steps4–5, and verify all root pullbacks use only the truncated polar maps, so no inverse on small singular values has been introduced. These are construction-level obligations, not a source theorem being assumed.

## D. Volume cost of the discarded blocks and arbitrary sizes

Assuming the lemma in C as proved by its construction, put r=kd and l=N−r<=theta N. A rank-l orthogonal complement can be represented by an N-by-l isometry. Such frames lie in the unit ball for operator norm in a real normed space of dimension 2Nl. Volume packing in that normed space gives an eta-net of cardinality at most (1+4/eta)^(2Nl); passing from frames to projections changes only the constant. Thus all rank-r projections can be covered with logarithmic cost O(Nl log(C/eta)).

Replacing P by a net projection changes the compressed pair, after unitary identification, by O(R_out eta) in operator norm. At fixed epsilon choose eta small enough that it remains in the same normal tube. The inverse changes the normal coefficients by O_(epsilon,k,R)(eta), so its effect is absorbed into a relaxation of the prescribed source moment parameters and cutoff. This avoids thickening a source microstate set by an uncontrolled measure estimate.

For each fixed net projection, the two remaining Hermitian matrix blocks have real dimension M=2(N²−r²). The original cutoff bounds their Hilbert-Schmidt norm by C R_out sqrt(N). Their Euclidean volume is at most the M-ball volume with that radius. Stirling yields

 log Vol_remaining <= -(N²−r²)log N
                      + C (N²−r²)[1+log(R_out)+log(N²/(N²−r²))].

The compressed r-by-r pair has the normal-tube volume upper bound from A, with the source microstate volume at size d. The orthogonal block decomposition of Hermitian space uses its induced Euclidean metric, so its Lebesgue measure factors; no unaccounted power of N arises. Summing over possible ranks costs only log(N+1).

After division by N² and addition of the two-variable normalization log N, the log N terms cancel. The total remaining error is bounded by

 C[theta log(C/theta)+theta log(C/eta)]

plus vanishing terms and the source moment relaxation. Take N->infinity first. Because d>=(1−theta)N/k, all these d tend to infinity and the ordinary limsup bound for source volumes applies to every one of them. Then send theta->0, followed by eta->0 (or choose theta log(1/eta)->0). Finally send the source moment tolerances to zero. This yields the upper inequality in (MV), with the SAME C_D as in B. No residue class of N is dropped and no liminf source entropy is introduced.

## E. Noisy endpoint and the remaining integration

At fixed U>0 the exact normal/orbital decomposition in unconditional-score-construction.md writes the noisy pair as D+epsilon(V A+O T), where A=X+sqrt(U)S and T is free orbital Gaussian noise. Analytic normal straightening gives a coefficient tuple H_epsilon(A,T)=A+O(epsilon), by a noncommutative power series with derivative in A equal to I+O(epsilon) in projective tensor norm, uniformly on a fixed larger radius. For fixed T it has an inverse power series with the same property, by contraction. The first-order orbital displacement is removed by K=O(epsilon), leaving the normal coefficients unchanged to first order.

Shlyakhtenko's actual relative-entropy Theorems2.19 and4.1 imply

 chi(H_epsilon(A,T)) >= chi(H_epsilon(A,T)|W*(T))
                       >= chi(A)−C_(k,R,U)epsilon.

The coefficient algebra W*(T) is embeddable and free from A. The hypothesis of Theorem4.1 is an invertible power series on a radius strictly larger than the coefficient norms, not just a formal inverse; the uniform contraction above is intended to supply exactly that. Its logarithmic Jacobian trace has absolute value O(epsilon). Apply B to H_epsilon, and D to X. Their C_D terms cancel, giving

 chi(Z_epsilon+epsilon k sqrt(U)S_pair)−chi(Z_epsilon)
 >= k^-2[chi(X+sqrt(U)S)−chi(X)]−C_(k,R,U)epsilon.

Combining this with the established candidate Fisher-increment estimate would give

 liminf_(epsilon->0) [chi*(Z_epsilon)−chi(Z_epsilon)]
 >= k^-2[(chi*(X)−chi(X))−(chi*(X+sqrt(U)S)−chi(X+sqrt(U)S))].

The last source gap tends to zero as U->infinity: Gaussian smoothing supplies the lower bound n/2 log(2pi e U) for chi, while covariance supplies the upper bound n/2 log(2pi e(U+C_X)) for chi*. This uses embeddability of X, supplied by the source construction. Hence the frozen strict pair target would follow once the volume/recovery and analytic-inverse details above survive scrutiny.

This is now a concrete full proof route, not a switch to a weaker target. It is not yet sealed as a completed candidate.

## F. Explicit analytic normal solver and its uniform majorant

Here is the promised solver in A and E. Work in the real self-adjoint part of M_k(A), with K in the kernel complement of the scalar-matrix commutator. Let P_o,P_v be the fixed finite coefficient projections onto the ordinary orbit and normal subspaces. Their norms on operator-norm coefficient arrays, and the norm of L^-1 on the orbit, are finite constants depending only on k,D. Set

 G(K,W)=P_o(exp(-iK)(D+W)exp(iK)−D).

Its expansion is P_o W−L(K)+R(K,W), after choosing the corresponding sign convention for L. The exponential series gives, on ||K||,||W||<=r,

 ||R(K,W)|| <= C(||K||²+||K||||W||),
 ||R(K,W)−R(K',W)|| <= C(||K||+||K'||+||W||)||K−K'||.

The same inequalities hold in the absolute noncommutative power-series majorant norm: replace each finite coefficient matrix by its coefficient norm and each monomial by the product of variable radii. Consequently

 K=L^-1 P_o W+L^-1 R(K,W)

is a strict contraction on ||K||<=2||L^-1 P_o||||W|| for a radius chosen only from these constants. Iteration starting at zero constructs a convergent noncommutative power series in W. Its coefficient majorant converges on a strictly larger radius than the one used for the actual coefficients. Differentiating the contraction equation in the power-series norm gives bounded first derivatives, and a second derivative bound on any smaller radius. These arguments apply unchanged in every M_d(A), because the scalar coefficient maps and multiplication bounds are uniform.

With W=epsilon(V A+O T), the first-order term K_1 is entirely determined by T, since P_o V A=0. The normal part of the conjugated pair therefore equals epsilon V A+O(epsilon²). Projecting onto V and dividing by epsilon gives H_epsilon(A,T)=A+epsilon R_epsilon(A,T), with the absolute coefficient norm of R_epsilon and its A derivative uniformly bounded on the fixed larger radii. For fixed T, the inverse A=H−epsilon R_epsilon(A,T) is another strict contraction, on a ball with a fixed positive radius margin around the coefficient bounds. It yields both inverse identities by uniqueness, with convergent coefficient power series. Thus the hypotheses of the actual relative change-of-variables theorem are supplied by an explicit convergent construction.

The local normal-chart inverse in A is the same contraction with a general W. The global uniqueness reduction uses only the finite coefficient almost-commutation argument already given. In particular neither analytic inversion nor derivative estimates are inferred from a dimension count.

## G. Additional volume checks

1. In C.4 the coefficient cutoff can be chosen with strict slack relative to the actual spectrum. For each Hermitian coefficient H whose actual norm is at most a>0, a continuous function vanishing on [-a,a] and equal to one outside [-2a,2a] bounds the discarded rank after functional-calculus approximation. If an actual coefficient is identically zero, choose a small fixed positive a of order epsilon, not a zero threshold. The finitely many rank losses add. Compression to the intersection bounds ||QHQ|| by 2a since Q lies in the good spectral subspace; invariance of Q under H is unnecessary.

2. In C.2, path maps are defined only on good singular subspaces. At each tree step intersect the root with the pullback of the next good initial subspace. A partial isometry maps orthogonal complements without increasing the lost dimension. Thus after finitely many steps the total loss is at most the sum of the excluded singular ranks plus the initial band-rank discrepancies. All paths restricted to the final root are genuine isometries. No product of unbounded inverses occurs.

3. A projection net in D is legitimate even though the recovered projection depends on the microstate. If ||P−Q||<eta<1/4, the polar part of QP+(1−Q)(1−P) is a unitary within C eta of the identity carrying P to Q. Conjugating the microstate changes its compressed pair by at most C R_out eta. The uniform analytic inverse therefore sends it to a slightly relaxed source microstate set. This accounts for the entire union without choosing a measurable recovery map or using a Jacobian for that map.

4. Lebesgue measure splits orthogonally into the r-by-r principal Hermitian block and the remaining Hermitian coordinates. The latter include cross blocks with their induced factor-two metric. The Euclidean-ball bound uses that induced metric, so there is no missing cross-block factor depending on N. Fixed metric constants contribute only O((N²−r²)) to the logarithm and vanish with theta.

5. For each fixed source accuracy and epsilon, first choose eta small enough for the relaxed source accuracy. Then choose the output moment accuracy so theta is arbitrarily small. This gives the order N->infinity, theta->0, eta->0, source accuracy->0. There is no need to bound a microstate neighborhood uniformly as epsilon->0: epsilon is fixed throughout this process and is sent to zero only after both entropy estimates are established.
