# T298P: a finite free-entropy gap for exactly two variables

Proposed author theorem, conditional only on the stipulated pinned source theorems and the classical interfaces explicitly identified below. No independent proof or contribution gate has passed. The full target was frozen before unified proof assembly; its SHA256 is recorded in scope-status.json and progress.json.

## Statement and source input

There is a von Neumann algebra with faithful normal tracial state and exactly two bounded self-adjoint elements Z_1,Z_2 such that

 -infinity < chi(Z_1,Z_2) < chi*(Z_1,Z_2) < infinity.

The entropy chi is the original operator-norm-cutoff limsup-over-matrix-sizes microstates entropy, with unnormalized Hilbert-Schmidt Lebesgue volume. Neither conditioning on scalar matrix units nor an ultrafilter replaces it.

Pinned source298 supplies a bounded n-tuple X with finite gap g=chi*(X)−chi(X)>=1/2, where n=2^64+1. Its construction X=C+sqrt(h)S has h>0, hence finite Fisher information, and has bounded matrix models, hence is embeddable. Set k=2^32, so n=k²+1. The actual introduction, conventions, signal construction and terminal block witness were read; no audit of the stipulated source theorem is intended.

We prove the following stronger transfer assertion for this input: if E_epsilon is the normal-slice encoding defined below, then

 liminf_(epsilon->0) [chi*(E_epsilon(X))−chi(E_epsilon(X))] >= g/k².       (1)

Every sufficiently small positive epsilon has finite microstates entropy. Thus (1) implies the stated strict inequality for some positive epsilon. No claim that the pair generates its ambient algebra is needed.

## 1. The normal encoding and uniform geometry

Let D_1=diag(1,...,k), and let D_2 be the real adjacency matrix of a spanning tree. Their common commutant is the scalars. The map H->(i[H,D_1],i[H,D_2]) has rank k²−1 on scalar Hermitian matrices. Choose a real orthonormal basis V_a of its orthogonal complement for the pair inner product sum tr_k(A_s B_s). There are n=k²+1 basis vectors. Put

 E_epsilon(X)_s = D_s tensor1 + epsilon sum_a V_as tensor X_a.

At size kd, the orbit tangent and normal fiber have dimensions (k²−1)d² and (k²+1)d², summing to the full pair dimension2k²d². All finite coefficient projections and inverse tangent maps have bounds independent of d, both in operator norm and Hilbert-Schmidt norm.

The global associated normal bundle over U(kd)/(I_k tensor U(d)) is injectively mapped to pairs in a fixed operator-norm tube by [U,Y]->U(D+Y)U*. To see global uniqueness, a transition unitary between two representations with small normal displacements almost commutes with both D_s. The diagonal separation of D_1 makes its off-diagonal blocks small; the tree edges make its diagonal blocks close to a common unitary. It is therefore close to the stabilizer. The local inverse then applies. That local inverse follows from the fixed finite coefficient tangent inverse and the exponential series, with a uniform contraction radius; its explicit equation and majorant are given in matched-volume-attempt.md F. The same inverse is a convergent noncommutative power series on a strictly larger radius than the coefficient norms used below.

The normal-bundle volume Jacobian, relative to base-orbit volume and Euclidean normal-fiber volume, is exp(O_(k,R)(epsilon)d²) when ||Y||<=C_R epsilon. Indeed the differential perturbation is [iK,Y], bounded in Hilbert-Schmidt norm by 2||Y||||K||_HS, relative to an inverse of uniformly bounded norm. Singular values are consequently within1+O(epsilon), in real dimension2k²d².

## 2. Matched original-limsup volume estimate

For every bounded n-tuple A with finite chi, the preceding encoding satisfies

 chi(E_epsilon(A)) = k^-2 chi(A) +(n/k²)log epsilon+C_D+O_(k,R)(epsilon).       (2)

We give both the normalization and the arbitrary-size upper step, because a local lower chart alone is insufficient.

Let c_D be the product of the nonzero scalar tangent singular values. Its amplified value is c_D^(d²). With group volumes in the unnormalized Hilbert-Schmidt metric, the base-orbit volume is

 A_d=c_D^(d²) Vol(U(kd))/(k^(d²/2)Vol(U(d))).

The stabilizer metric contributes k^(d²/2); the normal coefficient map contributes (epsilon sqrt(k))^(nd²). The unitary volume formula and Stirling give

 log A_d/d²=−(k²−1)log d/2−(k²+1)log k/2
             +(k²−1)c+log c_D+o(1),
 c=3/4+(1/2)log(2pi).

For completeness, the group-volume recursion follows by projecting U(l) to its first column: the quotient sphere has its ordinary metric multiplied by2 in its2l−2 horizontal directions and by1 in the phase direction. Its volume is therefore2^(l−1) times the unit sphere area, namely(2pi)^l/(l−1)!. Starting at U(1) gives the stated product formula.

The global normal bundle over a source microstate set has volume between

 A_d (epsilon sqrt(k))^(nd²) Vol Gamma_d(A) exp(±C epsilon d²).

For the lower bound every subsequence of source matrix sizes is retained as output sizes kd. Entropy normalization cancels all log d terms and gives

 C_D=log k+((k²−1)/k²)c+(log c_D)/k².

For the upper bound take arbitrary output size N. Sufficiently accurate bounded microstates admit a corner of rank kd=N−o(N) in the global normal tube, whose recovered coefficients are prescribed source microstates with a fixed cutoff. Here is the recovery construction.

The actual first coordinate has k separated bands, each of trace exactly1/k: along D_1+s epsilon H_1 the band projections are norm-continuous and equivalent to the original rank-one scalar projections. For matrix microstates, the complementary spectral mass and the band-rank discrepancies are o(N). On each tree edge the actual band compression of the second coordinate is invertible between its corners, uniformly separated from zero. Truncated polar maps of the corresponding matrix blocks exclude only o(N) singular directions. Pull their good domains back along the finitely many tree paths and intersect them in a common root space. The restricted path maps are isometries onto orthogonal band subspaces and give exact matrix units on a corner of rank kd=N−o(N).

The pulled-back coefficient moments converge to the actual polar-coordinate law. All functional calculi here are bounded and continuously approximable on the good spectral intervals; outside those intervals the excluded rank is o(N). Compressing bounded operators on o(N) dimensions changes each fixed trace word by o(1). Now cut away, in the common root, the bad spectral subspaces of each real and imaginary entry deviation from D, using a threshold strictly larger than its actual O(epsilon) norm. Intersect these finitely many good root subspaces and restrict every path map to that intersection. The total rank loss stays o(N), while the compressed pair is now O(epsilon) close to D in operator norm. The analytic normal inverse recovers the source law: in the actual encoded algebra, normal-tube uniqueness returns A up to a common root unitary. Polynomial approximation to the uniformly convergent inverse transfers every prescribed source moment condition. No invariance of the root under all coefficients is needed for the norm bounds on their compressions.

Finally union over possible corners costs negligible normalized volume. A rank-l complement has an operator-norm eta-net of projections with cardinality at most(C/eta)^(2Nl), by normed-space volume packing of N-by-l isometric frames. Nearby projections are intertwined by a unitary within C eta of the identity; thus replacing a corner by a net corner only relaxes recovered source moments by O_(epsilon)(eta). The complementary pair blocks have real dimension2(N²−k²d²) and Hilbert-Schmidt radius C_R sqrt(N). Their Euclidean-ball volume, together with the projection net, costs at most

 C[theta log(C/theta)+theta log(C/eta)]

after entropy normalization, where theta=1−kd/N. The log N terms cancel with those of the retained block. At fixed epsilon and source accuracy choose eta small, then send N->infinity and theta->0, then eta->0 and the source tolerance to zero. Since d>=(1−theta)N/k, the source limsup upper bound applies to every retained d, not just one residue class. This proves the upper inequality in(2). Full estimates, including the projection identification and root truncation slack, appear in matched-volume-attempt.md C,D,F,G and stress-checks.md.

## 3. Unconditional Fisher information with orbital coefficients

Let U=(U_a) have finite conjugates xi_a and be free from a bounded orbital tuple T. Set Z=D+epsilon(V U+O T), where O is an orthonormal orbit basis. Then

 Phi*(Z) <= Phi*(U)/(epsilon²k⁴)
             +C_(k,R)epsilon^−1(1+Phi*(U)).                         (3)

This is unconditional. Here are its algebra and domain checks; the complete series bounds are in unconditional-score-construction.md.

In the coarse bimodule define w_bc=sum_i E_ib tensor E_ci. These commute with the scalar matrix units. The vectors W_a,bc=(V_a1 w_bc,V_a2 w_bc) are orthogonal, of squared norm1/k. They span the orthogonal complement of the range eta->([D_1,eta],[D_2,eta]), whose kernel has dimension k². The dimensions are k²(k²+1) and k⁴−k². This supplies an actual inverse on the full coarse pair space.

Normal entry derivations vanish on T and the scalar matrices and send U_a to w_bc. They have adjoint E_cb xi_a/k at1 tensor1. Coefficients are inserted on the INNER legs of the derivative, commuting with its outer bimodule actions; arbitrary outer multiplication is not used. Add inner derivations P->[P,eta]. The map from epsilon times the normal generator values and eta to their values on Z is the finite inverse above plus an O(epsilon) bounded coefficient perturbation. Its Neumann series converges in projective tensor norm. Differentiating a degree-l summand costs at most l, so its differentiated series converges too. The entry adjoint product rule and the bounded partial-trace adjoint of an inner derivation therefore give legitimate L² adjoints. Their projection onto W*(Z) gives unconditional conjugates.

The constant normal projection yields leading scores

 Xi_j^0=(epsilon k²)^−1 sum_a V_aj xi_a,
 sum_j||Xi_j^0||²=Phi*(U)/(epsilon²k⁴).

The remaining score norm is at most C_(k,R)(1+sqrt(Phi*(U))). Squaring and using projection contraction proves(3). The inner term supplies precisely the orbit component missing from the leading scores' linear tests.

## 4. Exact free-noise decomposition and matched increments

A scalar free standard semicircular pair over M_k(M) is represented by2k² standard free coefficient semicirculars divided by k. Orthogonal rotation into the normal and orbital bases gives, EXACTLY at time t=epsilon²k²u,

 Z_epsilon+sqrt(t)S_pair
 =D+epsilon V(X+sqrt(u)S_normal)+epsilon O sqrt(u)S_orbit.

The normal tuple U(u)=X+sqrt(u)S_normal is free from the orbital tuple. Its conjugates remain conjugates relative to that tuple. Thus no Fisher upper semicontinuity or exposure of a separate hidden X is needed. For fixed u in[0,U_0], coefficient norms are uniformly bounded and Phi*(U(u))<=Phi*(X)<infinity. Integrating(3) with the free heat-flow entropy identity gives

 chi*(Z_epsilon+epsilon k sqrt(U_0)S_pair)−chi*(Z_epsilon)
 <=k^-2[chi*(X+sqrt(U_0)S)−chi*(X)]+O_(U_0)(epsilon).       (4)

For the microstates increment, analytically straighten the noisy pair into the normal slice. The normal solver has first-order K depending only on the orbital tuple; the resulting coefficients are H_epsilon(U,T)=U+epsilon R_epsilon(U,T), with bounded coefficient derivative and a convergent inverse power series on a larger multiradius. Shlyakhtenko's relative microstates Theorems2.19 and4.1 apply with the coefficient algebra W*(T): it is embeddable and free from U. The relative entropy is the supremum-over-conditioning-models original-limsup version, and its fiber inclusion bounds it above by unconditional entropy. Therefore

 chi(H_epsilon(U,T))>=chi(U)−O_(U_0)(epsilon).

The semicircular conditioning tuple has all-size bounded models; this application loses no source limsup subsequence. Applying the lower half of(2) to H_epsilon and its upper half to X cancels the SAME C_D and gives

 chi(Z_epsilon+epsilon k sqrt(U_0)S_pair)−chi(Z_epsilon)
 >=k^-2[chi(X+sqrt(U_0)S)−chi(X)]−O_(U_0)(epsilon).          (5)

Only a relative MICROSTATES change-of-variables theorem is used here. The nonmicrostates estimate is the separately proved coarse score construction.

## 5. Strictness and finiteness

Since chi<=chi*, the gap at time zero is at least the difference between the microstates increment(5) and nonmicrostates increment(4). Letting epsilon->0 gives

 liminf gap(Z_epsilon)>=k^-2[g−gap(X+sqrt(U_0)S)].

For large U_0 the last gap tends to zero. Indeed embeddability and the Gaussian relative-entropy lower bound give chi(X+sqrt(U_0)S)>=n log(2pi e U_0)/2; covariance gives chi*<=n log(2pi e(U_0+C_X))/2. Their difference tends to zero. This proves(1). Choose U_0 with the source noisy gap below g/2, then choose epsilon small enough to absorb the finite O_(U_0)(epsilon) terms. The resulting pair has positive gap. Its chi is finite by(2), and chi* is finite above by bounded covariance and below by chi. This proves the full frozen assertion.

## Boundaries

This is an author-assembled full proof, awaiting separate independent proof and contribution reviews. All estimates are for fixed gigantic k; no useful quantitative epsilon or low-dimensional numerical witness is claimed. The diagnostics check finite coefficient identities and metric multiplicities only. There is no formal proof, manuscript, acceptance, or count change. Source bodies and external primary bodies remain private.
