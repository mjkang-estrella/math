# Frozen minimum-side refinement: independent formal/source review

Date: 2026-10-26. Reviewer: polynomial lane. Candidate341671 only.

**Verdict: mathematical PASS; exact-source coverage PASS; fresh formal replay PASS. Novelty HOLD remains a separate gate. No discovery count is authorized or changed by this report.**

The new scalar, generic cubic, combined ordinary-interior theorem, and both coefficient-optimality statements are correct. There is no unresolved mathematical bridge or assumed strengthening in the main endpoint. This verdict binds the six frozen source hashes below. A provisional older combined file failed on an unknown lemma name; the author corrected that compile issue before freezing. The final bytes were independently recopied and replayed successfully.

## Exact reviewed sources and replay

Candidate directory, from the `new-discoveries/` root: `candidates/taxicab-strengthening/`.

| Module | Declarations | SHA256 |
|---|---:|---|
| StrengthenedScalar |12|`d13d8acacabf3edc1866be81ebdab0fed6565b18692864204aec10c9c26b1cf2`|
| GenericCubic |2|`e8c765a0183a77d1b7bc10850a87d78eda48c09e278e827ffea7e17c4a86da7d`|
| TaxicabGeometry |32|`b8a8ec0fc3c3f67f351ad28b2417dbdaec10946aea5f749f205c11e5973160f0`|
| StrengtheningAlgebraReview |7|`d3552ba401dbc82e1e0312a2429e3841fbd1f9ae191bd5e8927fe21fcef6441d`|
| StrengtheningGeometry |9|`fcb5118c73c0a58dea0a69f3671ff0310bcc8c738aaf374c0125d3542e9f6c68`|
| RefinedTaxicab |6|`1ff61ae87f1fc80c6ffbc825fee0b454c41c4dd8de90952b7a55edfa09d502cb`|

Fresh isolated copies and the complete68-declaration receipt are in this lane's `review-strengthening-combined/build/verified/audit.json`. I used `new-discoveries/verify_candidate.py`, the frozen candidate manifest, Lean4.34.1 commit `5045d0056413266e57c625dcd7c365b10e377c52`, and the pinned2026-10-14 mathlib/dependency packages. The verifier independently checked dependency revisions and tracked cleanliness, compiled with warnings treated as errors, and printed every declaration's axiom dependencies.

Result: **PASS,68 declarations, only `propext`, `Classical.choice`, `Quot.sound`.** There are no forbidden proof tokens, custom axioms, admitted lemmas, unsafe proofs, or native evaluation. The scalar module was additionally replayed alone: `review-strengthening-scalar/build/audit.json`, PASS12 declarations, same three standard axioms.

All seven manifest endpoints were checked: `StrengthenedTaxicab.generic_cubic`, `StrengthenedTaxicab.scalar_strength_weighted`, and `RefinedTaxicab.convexHull_bound`, `refined_interior_bound`, `source_conjecture_341671`, `outer_coefficient_sharp`, `minimum_coefficient_sharp`.

## Scalar theorem and all boundary cases

I read the complete frozen scalar proof. `scalar_strength_weighted` quantifies all six nonnegative lengths/distances and three nonnegative weights summing to1. Its six caps and three weighted inequalities are exactly the geometry's outputs. It assumes neither a fraction-sum inequality nor the desired cubic sign as a missing geometric bridge.

`cubic_of_fraction` clears positive denominators correctly. `threshold_sorted` obtains nonnegative slack variables from the right caps. `derivative_nonpos`, `reduce_equal_sides`, `symmetrize_lengths`, and `equal_side_product_bound` implement the independently checked threshold/square argument. The two final cases exhaust the real order relation. The common positive offset yields strict contradiction without discarding equality cases. `scalar_strength` explicitly handles all six permutations of the paired vertex/side variables; each call passes the correctly permuted caps. The weighted theorem introduces a positive gap divided by12, so it includes zero vertex lengths, zero side distances, and zero barycentric weights without dividing by them.

`GenericCubic.generic_cubic` is in namespace `StrengthenedTaxicab`. It separately proves the written paper's more general nonnegative-length cubic criterion, including all six orderings. It does not introduce an unproved assumption into the geometric theorem: that theorem uses the weighted result, whose geometric assumptions are established directly.

For independent mathematical details and the exact symbolic identity checks, see `taxicab-strengthening-review.md`, bound to the matrix lane's PROOF.md hash `963a8dbea43f786e35634af9c88fb4a71eb669153f2b5e772f96bb126240e266`. The new Lean proof matches that argument.

## Main geometric statement and source correspondence

`RefinedTaxicab.refined_interior_bound` has exactly these input assumptions: arbitrary coordinate points A,B,C,P in `ℝ×ℝ`; nonzero signed doubled area; and P in the ordinary topological interior of the closed convex hull of the three vertices. It concludes

    (3/2)*(r_a+r_b+r_c+min(r_a,min(r_b,r_c))) ≤ R_A+R_B+R_C.

It assumes no orientation normalization, vertex-distance positivity, ratio bound, or barycentric coefficients supplied by the caller. The stronger `convexHull_bound` extracts nonnegative weights from membership in the ordinary closed convex hull and proves their sum and point identity using distinctness. `barycentric_bound` invokes the actual line-distance estimates and then the complete weighted scalar theorem. The area hypothesis implies distinct vertices, ensuring each supporting-line denominator is positive. Degenerate triangles are not silently used for an interior example.

Vertex distances are the explicit L1 formula `|x|+|y|`; opposite-side distances are the explicit affine line quotient by `max(|alpha|,|beta|)`. These are the conventions of [Petrović–Malešević–Banjac2020](https://files.ele-math.com/articles/jmi-14-84.pdf), equations(4)–(6). I previously independently downloaded and visually checked that published primary PDF, including Conjecture1 on printedp1318. The formal side coefficients vanish at both endpoints and cannot both be zero for distinct endpoints. This supplies the full source definition bridge, not a substitution of Euclidean distances or closed-segment distances.

The product type's ordinary topology appears only in convex-hull/interior predicates. Its default maximum norm is never substituted for the explicit L1 distance. Those topology predicates represent the ordinary planar closed triangle and interior, so this use does not change the metric inequality.

`source_conjecture_341671` derives the exact old conjecture by proving the minimum of the three actual side distances nonnegative. It is a consequence of the same stronger candidate, not an additional outcome.

Authorship transparency: the inherited32-declaration `TaxicabGeometry` module was originally authored by this polynomial lane in an earlier assignment, and is byte-identical to its earlier audited version. I do not label my review of my own inherited geometry as a new third-party mathematical review. The new scalar and combined modules were authored elsewhere and independently reviewed here; the inherited geometry's separate parent/matrix review is the third-party check for that component. The fresh complete replay in this report covers all six modules regardless of authorship.

## Both coefficient-optimality statements

The witness module uses the exact points P=(0,0), A=(3,0), B=(0,3), C=(−3/2,−3/2). The area, L1 vertex sizes(3,3,3), and supporting-line distances(1,1,3) are checked by rational kernel arithmetic. `strictly_interior` proves ordinary topological interior directly: the open coordinate square with both coordinates between−1/4 and1/4 is contained in the convex hull, using explicit nonnegative barycentric coordinate formulas for every point in that square. Thus it does not merely assume the witness lies inside or use relative interior of a degenerate set.

`outer_coefficient_sharp` states that every K>3/2 fails for the entire refined expression `(sum of side distances + minimum)`, at that fixed strictly interior nondegenerate witness. `minimum_coefficient_sharp` states that every K>1 multiplying the minimum inside the fixed outer3/2 also fails there. Both strict inequalities are correct: the vertex sum is9 and the refined bracket is6; the minimum is1. These theorems concern coefficients in the refinement. The witness's old, unrefined vertex/side ratio is9/5, so these statements must not be misdescribed as a new proof of sharpness of the old three-halves coefficient alone.

## Paper scope and remaining gate

I read the mathematical draft `main.tex`, SHA256 `fe150cb87615c6dfebb6bcb771ab7103788fb1189bd14894c635498b39c3fb20`. Its theorem, proof, source conventions, closed-triangle extension, and sharpness statements agree with the frozen formal development. Its formal-status prose still says final integrated review is in progress; that can be updated after this report. Such a status/bibliography formatting update is not a new mathematical change. No PDF build or visual QA was performed here.

**Novelty remains HOLD.** The earlier mathematical/prior-art review found no matching additive-minimum bound, but the full2018 Ghandehari–Martini primary body is still unavailable. A kernel proof certifies correctness, not historical novelty. This report does not remove that hold, assert absolute priority, create a second count for the old conjecture, or authorize external posting.
