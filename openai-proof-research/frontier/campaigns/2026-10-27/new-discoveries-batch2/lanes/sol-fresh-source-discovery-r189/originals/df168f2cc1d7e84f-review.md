# R2T independent contribution review, round 1

Myeongjin Kang; no affiliation. Original review prose CC BY 4.0; original review code MIT. Private research review; third-party rights retained.

**Verdict: TECHNICAL.** This is neither DUPLICATE nor a proof verdict. The full proposed R2T conclusion is stronger than either pinned theorem statement and is not stated in the external primary bodies read. Relative to the stipulated bounded-core source, however, its additional operation is a finite recursive application of the same shell construction, followed by elementary affine optimization and two uses of the same local persistence argument. That falls below this campaign's substantial-new-mechanism gate. No count award is recommended; the campaign remains 5/10 unless the parent separately accepts another result.

## Exact object and scope

Candidate SHA256 `7392c10ee88ba844ae2115cb48bbeff0ba8aaf40641bae42b818825d12778230`; frozen scope SHA256 `e595c73286a91733d95e3dc46800e1e51ed0af8d290490ffb93058815c5f79c2`; author seal SHA256 `a30af383bfa83f5855d1bb83acc981ae9b6308af37a715dc71c3c8294d6f8144`. These match the brief. The reviewed claim is ONE bounded continuous radial pair potential on R3, stable for all configurations including coincidences, with tail O(r^(-3-1/32)); finite canonical limit for all positive beta and density, under beta-independent Lebesgue measure and 1/N!; and TWO fixed inverse temperatures in (31/32,33/32) and (41/32,43/32) producing strict finite one-sided beta-derivative jumps at EVERY density in ONE interval centered at 2p. Same potential, same interval, same two temperatures. It asserts at least two jumps, no phase classification or finite range.

I did not replace this by a two-triple picture, two separately tuned potentials, or distinct-density Gibbs coexistence. The separate full proof review has not been used as evidence for contribution. The stipulated source truths at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are not audited.

## Decisive comparison with the actual bounded-core proof

Let B denote the seven-section bounded-core manuscript. Its main theorem supplies one common temperature throughout a density interval. Its proof already supplies all the hard analytic operations used by R2T:

| R2T operation | Exact antecedent | Assessment |
|---|---|---|
| Continuous bounded shell core, near-equilateral clique bound | B foundations, f:core and f:shell-graph | Same construction; apply the Gram obstruction twice |
| Clique bound to quadratic occupation control | B foundations, f:stability and reproduced Motzkin–Straus maximization | Replace clique size4 by16 and D0 by t²/32; no new inequality |
| Canonical limits for all densities, local moments, mass continuity | B f:canonical-bounds, f:grand-tail, f:thermodynamics, f:moments, f:perturbation, f:tail-pressure | Same hypotheses after changed coercivity constant |
| Rooted free-component integration and removal of all bad-pair endpoints | B initial, i:bare-pressure, equations i:rooted-count, i:removal-pointwise, i:removal-factor | Repeat the root integration at one extra level; unchanged deletion mechanism |
| Optimizing all mixed components | B initial, i:cluster-rates | A two-variable affine endpoint maximization in place of a one-variable one |
| Quadratic attraction, exact active supports and branch separation | B k:transform-properties, k:active-parabola, k:subdifferential, i:limiting-transform, i:initial-separation | Same square completion and secants, with an inactive-plane gap |
| Quantitative physical range comparison | B k:range and its complete proof | Same box deletion, moments, kernel rows and Jensen square; no new rate |
| One fixed algebraic-tail potential retaining corners | B m:one-step, m:schedule, m:propagation, m:pressure-ball, m:tail | Two disjoint local neighborhoods; take finite maxima/minima of constants |
| Same-density canonical temperature jumps | B m:canonical-corner and final theorem proof | Same horizontal slicing and partial conjugacy at each limit point |

The entry on mixed components deserves an explicit reduction, not a label. It is the entire potentially new operation.

## Parameterized reduction of the nested-shell step

Keep the source outer shell ell=exp(-t). Add an inner shell s=exp(-c t), with any fixed c>19/4, rather than first specializing to c=6. For sufficiently large t, 2(1+Delta)s<ell and 2(1+Delta)ell<1.

In a good clique, the relation “equal label or inner-shell distance” is transitive: the triangle inequality puts the endpoints of two inner edges below ell, so the good endpoint pair must be inner. Each class has at most4 members by B's existing Gram lemma. Representatives of the classes have all distances in the outer shell, so that SAME lemma bounds the class count by4. This is the source shell obstruction on the quotient as well as within a class. It is an exact partition, not a conjectural assertion that preferred clusters dominate.

For k classes and M particles, 1<=k<=4 and k<=M<=4k. The source root integration at the outer level gives ell^(3(k-1)); repeating it within classes gives s^(3(M-k)). The exponent is therefore

    E(k,M)=M h-3(k-1)-3c(M-k).

For fixed k its maximum over M occurs at k or4k. For either endpoint it is affine in k, so its maximum occurs at k=1 or4. The four possibilities are

    h, 4h-9, 4h-9c, 16h-(9+36c).

Because c>1, the third is dominated. Thus the candidate's complete optimization is one further level of the source affine-endpoint argument. Mixed cluster sizes cause no extra variational obstruction. The upper label count still has a finite set of component types and the same K! denominator; finite type constants disappear after normalization by t. The source bad-endpoint removal estimate is literally unchanged. For the matching lower bound put inner tetrahedra at the outer tetrahedron's vertices: s/ell→0 keeps all cross-class edges inside the existing outer plateau margin. The same rooted displacement coordinates have triangular Jacobian one. No new packing theorem or entropy estimate is needed.

Write B_c=9+36c. Applying the identical source mass A=3/(2p) gives planes

    L_m/p = m h-b_m+(3/4) beta m²,
    m=0,1,4,16; b_m=0,0,9,B_c.

The first triple 0,1,4 remains at (beta,h)=(1,-3/4). Its fourth plane has value p(180-B_c). The second triple 0,4,16 occurs at

    beta=(B_c-36)/144=(4c-3)/16,
    h=9/4-3 beta.

Its omitted m=1 plane has value (9p/4)(1-beta). Both gaps are strictly negative exactly for c>19/4. Thus there is an open parameter range producing the two isolated triples; no delicate tuning or new stability principle is involved. For c=6, B_c=225 and the second point is (21/16,-27/16), exactly R2T.

The slopes lie on the same source parabola v_m=((3/4)pm²,pm). The interiors of triangles {v0,v1,v4} and {v0,v4,v16} have density projections (0,4p) and (0,16p), respectively. Every density in (0,4p), in particular2p, is the density of an interior point of each triangle. The candidate's positive barycentric weights are one explicit choice. The source robust-triangle lemma therefore supplies small balls centered on that same density. This does not require the triangles themselves to overlap in the full slope plane. Their horizontal slices yield the common interval after taking the smaller radius.

Finally the source persistence is local, uniform on fixed compacts and already uses one explicit schedule satisfying finitely many strict summable-loss inequalities. Apply it in two disjoint neighborhoods with common worst constants, select a subsequence in the product of two compact parameter balls, and use its canonical-corner lemma twice. The physical potential remains one potential throughout. This is a valid distinction from summing two completed source potentials, which would not justify either phase guarantee. But the correct way used here is still a finite parallel application of the existing local theorem, not a new interaction-decoupling method.

These reductions explain why the stronger physical conclusion is a technical extension. The decision does not rest on a demand that new mathematics be complicated: rather, the candidate's indispensable new steps are precisely triangle-inequality equivalence, repeated source root integration, affine endpoint maximization, and finite simultaneous use of the existing persistence. There is no further unsupplied operation after those reductions.

## Companion and external primary bodies

The divergent-core companion's introduction, Theorem thm:main, and construction section also supply one common critical point on an interval, for a different potential and o(r^-3) tail. Its model shell-graph proof and kac.tex free-pressure proof use the same tetrahedral/root-count mechanism. It is an antecedent, not an exact duplicate, and its divergent core does not satisfy R2T's boundedness. Detailed read extents are in reading.md; I do not claim to have read all of its remaining analytic proofs.

He–Jauslin–Lebowitz–Peled, [arXiv2510.24825v1](https://arxiv.org/pdf/2510.24825v1), equation1.13 physically deletes reference interactions between fixed boxes and replaces the attraction by boxwise constants. Section1.2.3 Theorems1.2–1.4 and Section1.3 Theorem1.6 establish mean-field approximation and fixed-beta distinct-density Gibbs coexistence for that model. The actual Theorem2.1 proof obtains phase selection by the Dobrushin–Shlosman criterion, ergodic decomposition, tightness and connectedness. These operations do not realize the nested radial microscopic diagram, nor do the stated conclusions give R2T's same-isochore two-temperature derivative jumps. The general box model allows broad single-site free energies; that flexibility does not remove the physical radial-pair restriction.

Lebowitz–Mazel–Presutti, [cond-mat/9809145v1](https://arxiv.org/pdf/cond-mat/9809145v1), equation2.2 retains a repulsive FOUR-BODY term in addition to the attractive pair term. Theorem2.1 gives two distinct-density Gibbs states for beta in an interval and a tuned chemical potential. Section3's coarse-graining scheme and equations3.1–3.10 produce a quartic mean-field free energy and its double well, then invoke Pirogov–Sinai perturbation. This is continuum coexistence and mean-field preservation antecedence, not an exact duplicate of a bounded radial pair potential with two canonical temperature corners. A range of beta supporting chemical-potential coexistence does not mean two beta-corners at one fixed density.

Bounded live searches returned these primary records and simulation-oriented multiple-transition examples, including Hertzian spheres and two-scale Jagla models. Abstracts and search extracts were not used to assert a theorem or operation overlap. No worldwide-priority claim follows. The decisive TECHNICAL evidence is the explicit source-relative reduction above, so lack of an exact external duplicate does not promote it to PASS_SUBSTANTIAL.

## Eligibility, limits and disposition

Targeted searches of the three campaign ledgers and the existing i[0-9]*.md iteration reports found no earlier developed family228 radial-temperature chain outside the present R2T record. Earlier family262/P3R development is a different family and is not used as an exclusion here. Generic numeral228 hits include the unrelated iteration I228; tetrahedral cylinder-covering and kinetic radial-potential work are unrelated. The initial overly broad search was truncated and was not used to infer absence; the corrected title/operation/family searches are recorded in eligibility.json. This is a bounded project-history screen, not a proof that no incidental mention exists.

The full R2T result remains a useful new-to-this-project technical extension if the independent proof gate passes. Neither its complete frozen statement nor its proof is altered by this review. No proofPASS is awarded here, no old theorem is challenged, and no paper/Lean/release/count gate is authorized. Preserve the candidate and the separate mathematical review; do not count it among the requested substantial results on the evidence now presented.
