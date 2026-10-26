# Independent taxicab candidate review

Date: 2026-10-26. Reviewer: matrix lane. Reviewed packet: `candidates/taxicab-three-halves/`. No candidate artifact was edited.

**Mathematics, exact-source scope, and frozen Lean: PASS. Strict novelty: HOLD, provisional.** I found no mathematical or formal objection. The outstanding issue is a theorem-by-theorem comparison with the inaccessible full Ghandehari–Martini2018 paper. I located no prior unrestricted three-halves proof, but do not certify its absence. Sharpness and the particular examples receive no discovery credit.

## Source fidelity

I read the published2020 Petrović–Malešević–Banjac paper, including the introduction, equations(4)–(6), restricted-position theorem and concluding Conjecture1. I independently rendered and visually inspected printed pp1301 and1318. The conjecture on p1318 concerns every interior point of every triangle. Equation(5) defines point-to-line taxicab distance as the absolute affine line equation divided by the maximum absolute coefficient; equation(6) uses the full supporting lines of the sides. Thus `lineDistance`, `sideDistance` and `norm1` match the actual source. There is no side-segment substitution or Euclidean perpendicular-distance substitution.

The explicit signed area excludes collinearity; `source_conjecture_341671` assumes this nonzero area and membership in the ordinary topological interior of the ordinary real convex hull. The product topology on ℝ×ℝ is the usual plane topology. The proof applies to arbitrary coordinates and uses no rotation reduction. The closed-convex-hull theorem is a valid strengthening, including boundary points. The source claim is not being replaced by a coordinate-position special case.

The independently refreshed live MathDB API for UUID `8dc03ea7-b114-4d76-b534-a090179e20f0` has zero solutions, comments, replies, model attempts, human solves and formulations. Its exact statement agrees with the retained snapshot apart from irrelevant state fields. Live API SHA256: `3c2b701ada3831360ab0392808dda85cbcd77e4b41b08f6981e4f28577f53e42`; statement-string SHA256: `57bacbe150219090cea833cddf3646206e5e7987f723051270e1f36af645f55a`. An open database label alone is not a novelty certificate.

## Mathematical audit

The scalar proof is sound. After sorting the three vertex lengths, the coordinate caps become(B,A,A). The threshold slice has deficits summing to D with0≤D≤A≤B, so its three displayed vertices really exhaust the deficit simplex. Each vertex lies in the nonnegative box. Concavity of x/(a+x) implies the required lower bound from those three vertices. I independently checked the cleared-denominator identities at V1 and V2 and their signs. The V3 estimate is immediate. Scaling a purported violation strictly reduces at least one fraction while placing the point on the threshold slice, giving the asserted contradiction. The six permutation cases preserve the opposite-side pairing.

The weighted extension correctly handles zero vertex lengths: perturbing each length by a positive epsilon yields the ratio hypotheses, and the explicit contradiction epsilon avoids a missing limiting argument. The barycentric line identity and the dual L∞/L1 inequality prove all geometric hypotheses. No positive barycentric coordinate is divided out, so boundary cases are covered. No circular use of the desired inequality occurs.

The sharpness family has vertex sum3+epsilon and side-line sum2−epsilon. For0<epsilon<1 its barycentric coordinates are positive, and the explicit open-set proof places it in ordinary interior. The selected epsilon defeats every coefficient greater than3/2. The fixed triangle has nonzero area, independently proved. This is a correct supplement and is explicitly credited as prior sharpness rather than another discovery.

## Independent frozen compilation

I copied the three frozen source files into fresh temporary directory `/tmp/taxicab-independent-lean-bgpsx_1z`, excluded all candidate-adjacent object files, and compiled Scalar, TaxicabGeometry, TaxicabErdosMordell, then a generated all-declaration check module. Lean4.34.1 was invoked with `-DwarningAsError=true` against the assigned2026-10-14 package build path. All four invocations succeeded. All55 local definitions/theorems/lemmas/abbreviations were checked individually with `#print axioms`; the observed set is exactly `propext`, `Classical.choice`, `Quot.sound`. No holes, extra assumptions or compiled decision procedures were found. The main ordinary-interior theorem and the optional sharpness endpoint both pass.

Frozen SHA256 bindings:

- `formal/Scalar.lean`: `be0cf4d9b241434e87fb65ea0f5216f7386f86d550ac1dfde40925aa24948498`.
- `formal/TaxicabGeometry.lean`: `b8a8ec0fc3c3f67f351ad28b2417dbdaec10946aea5f749f205c11e5973160f0`.
- `formal/TaxicabErdosMordell.lean`: `c52b5bbd194ed87bda9c5ead3c9196efa9732f21c89588ddf79bbcd428d46013`.
- Reviewed `main.tex`: `9613a844441eb15cea76c4d60cc902edb486aea4a9b6ad05753f0c9ec871186f`.
- Published2020 source PDF: `18c64799f9f65b475588324851e43abf409ad00d3222b2e7bad022db636070a4`.

The temporary receipt is `receipt.json` in the stated directory. Parent's independent dependency-pin verifier remains the authoritative release replay; this review performed no git operations.

## Novelty investigation and qualification

I searched exact/accent-varied titles; the2018 DOI; authors with Mordell, PDF, repository, universal, barycentric, normed/Minkowski/Banach and3/2; unrestricted taxicab conjecture/proof/2026; and Erdős-ratio terminology. I checked the2018 publisher/Crossref record, ResearchGate record, author/repository search results, OpenAlex locations and citation records, and current nearby literature. OpenAlex supplies no open full-text location for2018; its citation indexing is visibly incomplete and is not evidence that no later work exists.

The closest source is [Ghandehari–Martini2018](https://doi.org/10.1556/012.2018.55.2.1392). The accessible abstract announces a normed-plane extension but does not specify the optimal constant. The publisher was inaccessible and the ResearchGate record offers only a full-text request. I did not infer its full theorem statements from the abstract. The2020 paper explicitly cites2018 yet still poses the unrestricted taxicab result; this is meaningful positive historical evidence, though not a logical exclusion of an overlooked implication.

[Kurusa2024](https://doi.org/10.1007/978-3-031-43510-2_7), §7.3.4, reports a radius-ratio lower bound from2018 and credits its Figure3 with an L1 configuration of ratio3/2. This supports the paper's prior sharpness attribution and does not supply the missing universal lower bound. The official Springer bibliography has an incorrect DOI attached to reference34; the candidate correctly uses the actual2018 DOI instead. Do not use Kurusa's ambiguous strict-convexity/side-distance conventions as a separate counted correction or rely on the malformed square-root rendering of a readable copy.

I also screened the publisher summary of [Tran2026](https://doi.org/10.1080/0025570X.2026.2653460), which describes trigonometric refinements of the classical inequality; it does not announce the unrestricted taxicab result. No directly competing unrestricted proof was located.

The candidate argument in fact uses only a norm and affine-line distance facts. Therefore an earlier universal three-halves theorem for normed spaces would subsume the taxicab result; checking this stronger possibility is essential, rather than searching only the word “taxicab.” The2018 full body remains the material unresolved comparison. I recommend retaining the packet as mathematically and formally verified, with strict novelty acceptance pending that comparison. Appropriate current wording is that the packet proves the stated source conjecture and that no earlier unrestricted proof has been located; an unqualified first-in-literature claim is not justified by this review.
