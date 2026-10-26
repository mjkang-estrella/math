# Independent review of the additive-minimum taxicab strengthening

Date: 2026-10-26. Reviewer: polynomial lane. Author: matrix lane. Reviewed argument: `../matrix/taxicab-strengthening/PROOF.md`, SHA256 `963a8dbea43f786e35634af9c88fb4a71eb669153f2b5e772f96bb126240e266`.

## Verdict

**ACCEPT the mathematical argument as written.** I found no missing case or incorrect identity. The proposed inequality

    2(A+B+C) ≥ 3(u+v+w+min(u,v,w))

follows from the stated caps and weighted barycentric hypotheses, including zero lengths. The explicit L1 geometry bridge supplies these hypotheses with the source's supporting-line distance convention, in every orientation. The interior equality configuration is correct and proves the additive coefficient is sharp when the coefficient of the sum is held at3/2.

**Formal verification is pending for this strengthening.** This is a review of the complete mathematical proof, not a claim that the new scalar theorem or its integration has passed Lean. The older geometry bridge has passed its separate pinned audit. A final formal/paper review must bind the eventual files by their own hashes.

**Novelty assessment: substantive candidate strengthening, not demonstrated absolute priority.** No matching additive-minimum bound was located. There is a nontrivial algebraic argument beyond applying a classical theorem to an already known matrix family. Nevertheless, the closest2018 normed-plane primary paper remains unavailable in full; the new term's absence from search results cannot exclude it or other unindexed literature. The claim should remain one strengthened341671 candidate, not an additional discovery for the coefficient, equality example, scalar abstraction, or each normed plane.

## Independent algebra and sign audit

I independently expanded all central polynomial identities using exact symbolic arithmetic and checked the implications by hand. The symbolic checks returned zero for the derivative formula, quadratic coefficient, threshold sum-of-squares identity, averaging identity, factorization, both final-case identities, and the common-delta increment. The following sign and domain checks are necessary and do hold.

1. Positive A,B,C give positive denominators A+u,B+v,C+w. Clearing them transforms F≤1 into H≥0 with exactly

       H=ABC−Avw−Buw−Cuv−2uvw.

   The factor multiplying1−F is the positive product of those denominators. This is not an independent assumed cubic condition in the weighted theorem.

2. H and all the opposite caps are invariant under simultaneous permutations of (A,u),(B,v),(C,w). Thus relabeling0≤u≤v≤w is legitimate even though it does not sort the vertex lengths. The definitions y=w−v,a=A−w,b=B−w,c=C−v are nonnegative by the actual opposite caps. Substitution in the threshold equality yields2(a+b+c)+y=6u exactly.

3. The polynomial h(t) is quadratic because its cubic terms cancel. Its quadratic coefficient is b+c−4u. The threshold implies b+c≤3u, hence this coefficient is at most−u≤0. The derivative at t=u is the stated D. The displayed identity for12D is valid modulo the threshold equation; every square and every remaining product has nonnegative magnitude. In particular the products yb and ya have the required signs. Therefore D≤0. For t≥u, h(t)−h(u)=(t−u)(D+q(t−u))≤0.

4. The reduction t=v→u subtracts v−u from all three lengths and changes the side distances to u,u,u+y. The resulting lengths are u+y+a,u+y+b,u+c. They are nonnegative, retain their required caps, and have the correct new threshold sum. No negative length or out-of-domain intermediate tuple is introduced.

5. With the first two side distances now equal, averaging the first two lengths changes H by C(A−B)²/4≥0. The averaged length s remains at least w; C remains at least u. The new threshold is4s+2C=9u+3w. The factorization H=(s+u)[C(s−u)−2uw] is correct, and s+u≥0.

6. In the case3w≤8u, the first identity gives a nonnegative expression because w−u≥0 and25u−9w≥u≥0. In the complementary case3w≥8u, one has5w−13u≥u/3≥0. With d=s−w≥0, every term of the second identity is nonnegative. These two cases cover the equality boundary too. No division by u is used, so u=0 is included.

7. If the target inequality fails, increasing each length by delta=(T−S)/3>0 reaches the threshold and preserves the caps. In the increment formula, AB−uv≥0 follows from v≤A,u≤B; AC−uw≥0 follows from w≤A,u≤C; BC−vw≥0 follows from w≤B,v≤C. The cubic delta³ is strictly positive and the other terms are nonnegative. Hence the shifted H is strictly positive, contradicting the threshold result H≤0. This strictness argument covers possible equality in the original cubic condition.

8. For arbitrary nonnegative lengths, the weighted relation gives u≤a(A+u). Adding epsilon>0 to A preserves u≤a(A+epsilon+u), because a≥0. Dividing by the positive denominator yields the ratio bound. The three ratios sum to at most a+b+c=1, so the positive-length theorem applies to the perturbed lengths. A hypothetical positive gap is contradicted by epsilon=gap/12, because the perturbation contributes only6epsilon=gap/2. This proves the exact limiting claim without assuming a continuity theorem or a missing positive-length case.

## Geometry and sharpness

The supporting geometry assumptions are endpoint caps and the opposite-side barycentric estimate. The existing explicit L1 module proves both. They are also mathematically valid in a normed affine plane: use a point on the opposite segment determined by the barycentric weights, homogeneity, and the definition of distance to the supporting line. A paper may explain that generality, but the current audited geometry module is explicitly L1; do not imply that an arbitrary-norm Lean bridge has been checked.

For P=(0,0), vertices (3,0),(0,3),(−3/2,−3/2), the weights(1/4,1/4,1/2) are strictly positive and their weighted sum is P. The triangle has nonzero oriented area determinant18. Each vertex has L1 distance3. The opposite affine line equations may be scaled to

    3x−y+3=0,  −x+3y+3=0,  x+y−3=0.

Using the published L1 line formula, their distances from P are1,1,3. Thus both sides of the strengthened assertion equal18. The minimum is1>0; this is a true interior equality, not a limiting boundary example. If the additive term's coefficient were greater than3/2 while the sum coefficient remained3/2, this configuration would violate the proposed larger bound.

The new inequality is strictly stronger than the old three-halves estimate whenever all three side distances are positive. The old estimate alone does not yield the additive term. For this example the old lower bound on the sum of vertex distances is7.5, whereas the strengthened bound is9, attained exactly. Sharpness of the original three-halves coefficient by itself is prior work and must still be credited separately.

## Prior-art review and precise limitations

The source remains Petrović–Malešević–Banjac2020 Conjecture1, with distances to supporting lines defined by equations(5)–(6); see the [published primary PDF](https://files.ele-math.com/articles/jmi-14-84.pdf). The original paper proves a restricted-position result and leaves the arbitrary-orientation statement conjectural. That is positive historical evidence that the intended unrestricted target was not being treated there as an already available consequence. It does not establish what happened later.

The closest prior work is Mostafa Ghandehari–Horst Martini2018, [DOI10.1556/012.2018.55.2.1392](https://doi.org/10.1556/012.2018.55.2.1392). Its full primary body could not be obtained through public author/repository sources. Abstract metadata says it extends Erdős–Mordell to normed planes and spaces, without supplying the theorem constants or additive terms. No conclusion about the absence of the present term is justified by that abstract. The earlier `taxicab-prior-art-review.md` records the search and the2024 survey's precise limitations.

Independent searches for Erdős/Erdos-Mordell combined with minimum/min, normed/Minkowski/Banach, taxicab, strengthening, and the three-halves coefficient found no matching additive-minimum assertion. The directly inspected2020 source has no such term. The2024 survey's summary of the2018 estimate is weaker than the old three-halves result for the standard L1 unit ball, which is corroborating context; it is not a complete inventory of the2018 paper. Euclidean improvements are not automatically relevant: ordinary Euclidean Erdős–Mordell already implies the new expression in that special metric because the sum of three nonnegative distances is at least three times their minimum.

Unlike the uncounted Vandermonde packet, I have not found an explicit older structural theorem for this exact scalar constraint set that makes the additional term immediate. The threshold reduction and its two sum-of-squares cases provide substantive new mathematical content within the reviewed argument. This supports presenting it as a candidate new sharp strengthening with the stated prior-art qualification. It does not support an absolute worldwide-priority claim or author contact without authorization.

No external messages were posted, no shared tally was edited, and no regulator numerical evidence was transferred into this proof claim.
