# Beta-content monotonicity: proposed complete mathematical proof

Status: **research only, credit0**. Mathematical reasoning below is not yet independently reviewed. The full convex-hull/probability source endpoint is not formalized in Lean. Do not count an analytic helper with a geometric monotonicity premise as a complete source proof.

## Exact source and mandatory nearest prior

Kabluchko–Steigenberger, *Beta Polytopes and Beta Cones: An Exactly Solvable Model in Geometric Probability*, arXiv2503.22488v1, actual PDF retrieved October26,2026, SHA256 e731e331f1d295993e897f42d4b039108a6c8c228c1d503b9558e3be4d628c63. Section6.2, Theorem6.8 defines expected beta-content as P[Y_beta in conv(X1,...,Xn)], with independent Xi distributed according to their individual beta_i≥−1. Conjecture6.15 printedp52 asserts increase in beta for fixed beta_1,...,beta_n. Work in its d≥2,n≥d+1 setting; beta−1 denotes the uniform sphere law, not a Lebesgue density. Source remark notes boundary content0 and the Wendel limit. All relevant actual statements were read in PDF text; sourcep52 Conjecture6.15 and Remark6.14 were rendered and visually inspected October26,2026.

Full live MathDB367740 snapshot SHA256 cd940d3dbec49ff6d6f9be943e56dfd3116864ee35cfa677eac3987e92d0e89c: open, progressnull, solutions/human_solves/model_attempts/replies/comments/formulations/attachments all empty. Do not infer novelty from this alone.

**Closest prior read in full for the relevant argument:** Ignacio Cascos, *Depth functions based on a number of observations of a random vector*, Working Paper07-29, September2009v2, Proposition6, pp8–9 (internal numbering). Actual author-hosted PDF retrieved despite web-tool403; SHA256 edf8b32c16ce40428981d0cb6c8ab78f06d96a0acc804772357f73dc1cfc5a8a. URL https://halweb.uc3m.es/esp/Personal/personas/icascos/eng/ws072907v2.pdf (same bytes at lowercase esp path). It proves ray-monotonicity of coverage by k IID absolutely continuous angularly symmetric observations, using entering/exiting facets, and credits Liu1990Theorem3 for simplex depth. Its identical-distribution hypothesis and absolute-continuity hypothesis do not literally cover mixed beta_i or sphere laws. Its proof is the direct methodological predecessor of the product version below; it must receive explicit credit. No claim of a new facet method or a new IID theorem is appropriate. Full source-conjecture novelty still needs a serious citing/later-literature review; no absolute priority claim.

## 1. Independent heterogeneous symmetric coverage is ray-monotone

Let d≥2,n≥d+1 and let X1,...,Xn be independent Rd-valued random vectors. Suppose each law mu_j is centrally symmetric about0 and assigns0 mass to every proper affine hyperplane. Put K=conv(X1,...,Xn). Claim: for every unit e and 0≤a<b,

P[a e in K] ≥ P[b e in K].

The hyperplane-null condition implies the usual general position almost surely: the hull is full dimensional and simplicial, the two fixed endpoints avoid its boundary, and the fixed segment crosses no face of codimension≥2 and no tangent facet. For the last assertion one can adjoin the fixed ray direction and endpoint to each finite determinant test; condition on all but one relevant random point and use hyperplane-nullness. These details must be expanded and formally proved, not assumed, in a Lean implementation.

For a d-element index subset S, condition on x_S=(X_i)_(i in S). Let C_S be the event that the relative interior of conv(x_S) meets the open segment (a e,b e), and let H_S be the halfspace bounded by aff(x_S) that contains0. Configurations whose hyperplane contains0 have probability0. On C_S, the direction of increasing radius goes from H_S to its complement. The simplex conv(x_S) is an EXIT facet precisely when every remaining X_j belongs to H_S; it is an ENTERING facet precisely when every remaining X_j lies outside H_S. General position ensures uniqueness of the relevant facet at each crossing. Convexity ensures at most one entry and at most one exit along the segment.

Write p_j(x_S)=mu_j(H_S) for j outsideS. Central symmetry and hyperplane-nullness give p_j≥1/2: H_S contains an origin-centered closed halfspace of mass1/2. Independence yields the conditional exit probability product_(j outsideS)p_j and entry probability product_(j outsideS)(1−p_j). Therefore each exit integral dominates its entry integral. Sum over ALL d-element S; no binomial multiplicity or identical-distribution assumption is used. Since entry and exit indicators satisfy

1_[a e in K] − 1_[b e in K] = number_of_exits − number_of_entries,

integration proves the claim. A segment that enters AND exits contributes zero to both sides, so the argument does not assume the entry and exit events are mutually exclusive.

This is the heterogeneous product extension of Cascos Proposition6, replacing his common-law power by a product of different halfspace probabilities and retaining the explicit sum over S. The boundary sphere case needs only hyperplane-nullness, so it is included.

## 2. Apply to the actual beta polytope

For beta_j>−1, the beta law has density proportional to (1−||x||²)^(beta_j) on the open unit ball, hence is centrally symmetric and hyperplane-null. For beta_j=−1, uniform sphere measure in d≥2 is also centrally symmetric and hyperplane-null. Consequently all source parameters beta_j≥−1 satisfy part1. Rotational invariance of their product law shows that h(r)=P[r e1 in K] is independent of direction. It is nonincreasing on[0,1].

If Y_beta is an independent beta point with beta>−1, its squared radius T_beta has density proportional to t^(d/2−1)(1−t)^beta on(0,1). Thus E Cont_beta(K)=E[h(sqrt(T_beta))]. If beta2>beta1>−1, the density ratio f_beta2/f_beta1 is a positive constant times (1−t)^(beta2−beta1), strictly decreasing. Therefore T_beta2 is stochastically smaller than T_beta1, and the nonincreasing function h(sqrt(t)) has larger expectation under beta2. This proves the source monotonicity for all finite beta>−1. For beta=−1, the test point is on the sphere and the expected content is0 (no sampled vertex equals the independent test point, and a convex combination of distinct unit-ball points has norm1 only when all contributing points coincide on the sphere). Every other content is nonnegative, completing the endpoint.

## 3. Strict increase (if the source means strictly increasing)

The coverage h is continuous on[0,1]: for each fixed r, P[r e1 on boundaryK]=0 follows from the finite facet/determinant argument; bounded convergence gives continuity along r. We have h(1)=0 and h(0)>0. The latter follows from Wendel's formula, which only requires independent centrally symmetric hyperplane-null vectors (not identical laws); alternatively choose d+1 small neighborhoods of a regular simplex centered at0, each of positive beta/sphere probability, assigning the remaining points arbitrarily. Thus h is not almost-everywhere constant on(0,1).

For beta2>beta1>−1, under the beta1 law, both g(t)=h(sqrt(t)) and w(t)=(1−t)^(beta2−beta1) are nonincreasing, and w is strictly decreasing. The identity

2 Cov(g(T),w(T)) = E[(g(T)−g(T'))(w(T)−w(T'))]

is strictly positive because g is nonconstant and the beta1 density is positive throughout(0,1). Dividing by E[w(T)]>0 proves strict increase. At beta1=−1, positive probability of a hull containing a ball around0 and positive probability of a finite-beta test point lying in that ball give strictly positive expected content. Thus the proposed conclusion is strict throughout[−1,infinity).

## Outstanding gates

- Check source dimensions and every geometric general-position assertion directly and independently; visually inspect actual sourcep52 and priorpp8–9.
- Serious novelty screen, especially any non-IID coverage-monotonicity theorem and any resolution of Kabluchko–SteigenbergerConj6.15; the IID case is already classical and receives no separate credit.
- A complete Lean proof of the literal random-polytope/beta-content endpoint. Geometry and measurability cannot remain hypotheses at the final theorem. Analytic covariance/likelihood helpers alone do not satisfy this gate.
- Independent review, manuscript, rendered PDF and final extracted proof-packet replay. Discovery count remains0 here.

## Additional source comparison and finite validation

The companion Gusakova–Kabluchko, *Sylvester’s problem for beta-type distributions*, arXiv2501.00671v2(June2,2025), was retrieved in actual primary HTML. It studies identical-law beta/normal/beta-prime Sylvester probabilities and explicit angle formulas. Its full text contains no monotonicity statement; it does not state the heterogeneous coverage lemma or resolve Conjecture6.15. URL https://arxiv.org/html/2501.00671v2 . This comparison is bounded and does not replace a full citing-corpus review.

The independent-sign finite experiment in check_signed_coverage.py passed on150generic planar clouds, n3..8, all12600signed hulls, using integer orientations and exact Fraction ray intersections. The complete reproducible input/output is in signed-coverage-check.json. This verifies a finite combinatorial shadow of the proposed facet-count argument on open radial intervals only; no universal theorem, continuous-law bridge, novelty or Lean endpoint follows from the experiment alone. Boundary spikes for discrete distributions are excluded by the hyperplane-null hypotheses in the proposed continuous theorem.
