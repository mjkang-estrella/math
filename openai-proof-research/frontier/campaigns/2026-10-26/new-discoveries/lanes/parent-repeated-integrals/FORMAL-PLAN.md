# Full source formalization, credit0

Primary namespace: RepeatedIntegrals. Pinned Lean4.34.1/mathlibd13f23b7.
The preliminary source/math/novelty/eligibility review passed; it certifies no
Lean endpoint. Preserve the old freeze and parent reconciliation in reviews/.

MomentDefs.lean fixes the common interface: MomentSpace n = Fin(n+1)->R,
densityMoments integrates t^i*rho over0..1, GoodDensity means a global smooth
strictly positive density on[0,1] equal1 on neighborhoods of both endpoints,
and smoothMomentSet is its actual image. No cone/smoothness premise is silently
assumed. SourceDefs.lean states the original C^n monotonicity and one-sided
endpoint data using iteratedDerivWithin on[0,1]. GoodWitness asks for a global
smooth extension with exactly the requested jets, a stronger witness convention
that is harmless only when actually constructed.

Required components, none yet claimed complete:

1. Convexity and openness of smoothMomentSet for every n. One useful proof uses
   compact interior bump times the monomials: its moment Gram matrix is positive
   definite because a nonzero polynomial cannot vanish on an interval. This
   avoids approximation of a Vandermonde determinant. Another valid route is
   independent localized bumps. Signed small perturbations preserve positivity
   and endpoint germs; use the invertible finite-dimensional moment map.
2. Every nonnegative multiple of the moment curve belongs to the closure of
   smoothMomentSet, using interior bump approximation and a positive baseline
   with endpoint germ1 and arbitrarily small integral.
3. Separation plus positivity of nonzero nonnegative polynomials against a
   nonzero atomless Stieltjes measure puts its moment vector in the open image.
   Equivalently prove the full closed moment-cone/interior identification. The
   first route can avoid separate compactness/closedness of all moment measures.
4. For the original witness f, extend g=D^n f constantly outside[0,1], build
   its finite atomless Stieltjes measure, and prove the kernel/factorial identity.
   No differentiability of g itself is available; Fubini or genuine Stieltjes
   integration by parts is required, not ordinary integration by parts for g.
5. Iterated primitives of the constructed rho give the literal global smooth
   witness and all jets. Prove the anti-triangular moment-basis transform is an
   invertible continuous linear map and identify SourceW with its open image.
6. Closed all-n endpoint SourceConjecture371768, strict replay of every type and
   axiom report, manuscript, independent final review, deterministic packet,
   fresh extracted replay. Abstract model results alone earn no discovery credit.
