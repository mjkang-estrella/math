# I209 reading, failed routes and validation record

2026-10-12. Final record. Written mathematics only: no research code, parameter scan, numerical experiment, test suite or subordinate agent.

## Reading sequence and boundaries

Read AGENTS.md and sources/upstream.json. Used sources/CONTENTS.md only to locate result 100; the initial broad catalogue display was truncated and is not represented as a full read. Used sources/preprints-tree.json only for exact companion paths. Read the four companions' actual retained introductions, all listed ruled-set sections, the angular cubic-buffer statement and proof, and the four newly retained sections listed in the literature note. Read the complete existing Bezdek–Litvak 2009v1 PDF, with an additional page 2–4 extraction to recover the initially truncated display. The I201 literature note was used as a source locator, not as a substitute for primary statements.

The user supplied I203 report, analytic record and initial parent nomination were read from the task message. No I203 live proof or contribution review was read. No other live task output was read. The supplied I201 report and disposition were treated as task context. No historical truth audit or replay of accepted results was undertaken.

## Route A: what failed and why

1. A globally affine trace-free field tangent to both wedge walls is forced to have form V=b(r,b), hence det DV=-b^2. An elliptic affine rotation cannot simply replace the original field while preserving these walls.
2. Continuing radial homogeneity past the nilpotent endpoint creates elliptic expansion. For -1<m<0, its positive determinant area has radial exponent 2m-1 and diverges at the apex, even while the projection-gain integral is finite. Ignoring this term produces a false gain.
3. The explicit mixed field p=1/2 (m=-1/2) is new geometry relative to the paid p>=1 construction. For fixed cutoff d, the analytic record proves inverse labels, positive wall factors, complementary caps and the two closed tip covers. Its finite realization is conditional on I203. The exact coefficient-one penalty and physical projection gain give F_d/a^4=-1/2+(29/30)z+c(1/z-1), z=d/a and c=2/(3sqrt(3)). AM-GM proves F_d/a^4>3/10 for every 0<z<=1. The old multiplier two would only worsen it.
4. A fixed cutoff leaves normalized tip excess 6d^2. A vanishing cutoff cannot simultaneously make the ordinary tip cost o(tau^2) and keep the derivative uniformly small. Even a better tip treatment would leave the positive determinant penalty unresolved. These failures do not rule out every elliptic field.
5. Taking a convex hull of a rotating sweep is not a cover. No such inference was used. The actual mixed-field cover accounts for each point by inverse labels or an explicit tip cylinder.

The missing upper-route ingredient is a different nonlinear field or geometry whose determinant-positive mass, caps, transitions and tips can all be paid while obtaining a substantial new finite-cover constant. No improved upper constant is claimed.

## Route B: successful lower bound and attacks checked

The first quadratic density 3/2-|x|^2 gave lower constant 3/(5sqrt(2)). It was superseded during written optimization by 19/10-|x|^2 and sqrt(15)/9. Neither the earlier constant nor the optimizing certificate is counted as a separate finding.

Potential failure points were checked explicitly:

* The midpoint of a chord need not be perpendicular to the radius. The integral identity uses the midpoint itself; the odd cross term integrates to zero. No perpendicular-midpoint assumption occurs.
* Endpoint barycentric products are nonnegative. They give the universal bound |m|^2>=l^2/4-1/2. Opposite-edge endpoints with disjoint supports attain it, and realize every length in [sqrt(2),2]. Thus the claimed line supremum is global and exact, not merely a calculation on symmetric lines.
* An equivalent direct expression is l[a+1/2-l^2/3-2 sum_i r_i s_i], where r,s are the barycentric endpoints. This independently reproduces the cubic upper bound and its equality case.
* The density is nonnegative everywhere on the tetrahedron (at the optimum it is at least 2/5), supported on the whole body, and measurable. Empty, tangent and boundary lines cause no exceptional integral problem.
* Tonelli applies to arbitrary measurable bases and nonnegative density. No assumed common cylinder direction, convex base, packing property or disjoint cover is needed.
* The moment calculation is elementary: each barycentric coordinate has second moment 1/10 and mean squared physical radius is 3/10.
* Tetrahedral averaging preserves the numerator and decreases the denominator of the certificate ratio. All invariant quadratics are radial. Both signs of the radial quadratic coefficient and the constant case are checked. The optimality is over polynomial densities of degree at most two, not every possible density and not every cover.
* General affine transformations do not preserve absolute sum-of-areas divided by minimum projection. No arbitrary-tetrahedron or directionwise enhancement is asserted.

The exact lower bound is independent of I203. Its finite-cover proof has no approximation error. The known angular upper construction is used only as accepted comparison and not rebuilt or counted again.

## Administrative limits

Partial report, analytic attempt and reading/literature records were written early and then updated. Only authorized I209 outputs and four fully read pinned source copies were written. A Bang primary-PDF request returned HTTP 403; no failed download remains in the source directory. Source scope and detached hashes are explicit. I31's SHA-256 is unchanged at d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a. No staging, commit, publication, shared-index edit, ancestor edit, snapshot or seal occurred. Both acceptance gates remain with the parent.
