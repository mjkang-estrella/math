# CDF098 independent scoped formal audit r1

**Verdict: PASS_SCOPED_SUPPORT.** The authenticated implementation proves the advertised finite metric-cover, packing, transfer, dyadic, segment and count interfaces. Fresh compilation and independent negative controls pass. This verdict does **not** formalize or independently recertify the complete CDF098 theorem, does not confer manuscript approval, and changes no campaign count.

Author of record: Myeongjin Kang, no affiliation. Original review prose CC BY 4.0; original code MIT. The auditor authored the separate CDF098 manuscript, but did not author CDFLocal, its controls or its build/mutation runners. The implementation agent previously authored the contribution review; this relation is preserved, not relabeled independent implementation review. The present verdict follows inspection and a fresh copied-package replay, not the manuscript's judgment or the author's reported success.

## Fixed target and authenticated bytes

The original target is unchanged: one universal finite integer Lambda works for every infinite-dimensional real Banach space B, producing a Lipschitz image Gamma of [0,1] which is Lambda-doubling for the restricted ambient norm at every scale and has no finite-distortion bi-Lipschitz embedding into any finite-dimensional real normed space. Gamma is fixed before the target dimension or distortion. No injectivity, simple arc, quasiconvexity or witness-cardinality bound is substituted.

- Formal output-manifest SHA256: `510548427d70b08ff90285e1ec90ba71cb29905a5ba674ce37902a6ff789cbef`.
- CDFLocal.lean SHA256: `1e4c558e4cd26e07094a06a40574a77b3453542c8b353311d211a81bdf578fdf`.
- coverage.json SHA256: `93bdc661ea244ec2621b1f4bbe70627945a913936fa4f35fa0e2ad30a50ba2af`.
- Author scope SHA256: `bb115b9c504b9e5d8e3f62d841bc16095049f23719a47eb13d18d253ed1741c5`; candidate SHA256: `24c5d7055f19b48bac26451a87896845756865eeeba5d0502e1f7982ccb6f39a`; author manifest: `f417cfd409e18a34c97f488fb10ebfa25f1b09b5fc4ff323c53c71cf71262c85`.
- Prior full-proof manifest: `543aba870bfb7237dcd95e2d03fd40e644350b7acbc9aa43cb90c08553a80dda`; contribution manifest: `42befbcdc270f6802d47080dfba86ef105dcd9316a237324eb0a4a5355f4c691`.

The 75 formal payloads were authenticated against the externally supplied manifest before copying into `private/formal`. All experiments were confined to this review directory. The copied baseline remains unchanged; replay evidence is in its explicitly unsealed `.replays` subtree, which is itself covered by this review's final outer inventory. The upstream pin remains fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The source theorem is stipulated, not audited or imported as a new Lean axiom.

## Exact declaration and semantic audit

All 39 public declarations are enumerated below: nine definitions and thirty support theorems. Every exact type has a matching `#check @...` and `#print axioms ...`. The fresh output was compared byte-for-byte with the authenticated type report. All source proof bodies were inspected; the arguments below were assessed independently of the earlier manuscript.

| Declarations | Actual operation and audit finding |
|---|---|
| `Covers`, `CoverBound`, `DoublingBound` | Actual Finset centers, distance <= radius, cardinality bound, positive-radius **closed** balls. In subtype metric spaces the centers are actual subset points. These definitions do not name a graph or replace ambient distance by path distance. |
| `covers_mono`, `refine_cover`, `iterated_cover` | Restriction/radius enlargement; finite biUnion composition with N*M bound; induction supplies D^q centers at r/2^q. The zero-halving case uses the original center. Classical selection is explicit; no finiteness of the ambient type is assumed. |
| `recenter_pullback` | Filters live original centers and chooses one preimage representative in A per live center; image cardinality is bounded by the original count. The returned centers are in A. Triangle inequality costs 2Kr, with K>=0 and the stated inverse metric inequality. Empty sets and duplicates are harmless. It does not presume original centers were already in A. |
| `packing_bound`, `doubling_packing` | Select a center for each separated point, then prove the induced map injective. Strict separation s<dist and 2t<=s are essential: two points sharing a center would satisfy dist<=2t<=s. The doubling specialization assumes positive R, finite p, containment in the original ball and the exact scale inequality. |
| `doubling_transfer` | For f:beta->alpha, requires forward 1-Lipschitz and backward K-Lipschitz metric comparisons, K>=0 and 4K<=2^q. It pulls a beta-ball into an alpha-ball, iterates and recenters; 2Kr/2^q<=r/2 is proved. This is a genuine cover theorem, not count arithmetic alone. |
| `subset_doubling` | Instantiates transfer with subtype inclusion, K=1, q=2. Gives D² doubling for every metric subset. |
| `bilipschitz_doubling` | Requires a surjective map and dist(x,y)<=dist(fx,fy)<=2dist(x,y). A chosen inverse supplies the transfer hypotheses with K=2 and q=4. Gives D⁴; it neither produces a Dvoretzky map nor assumes an inverse is canonical. |
| `dyadic`, `dyadic_gap` | Defines 1/2^k and proves the index-gap inequality by monotonicity of powers. |
| `dyadic_window_card` | For an explicitly finite index set t in (L,U] and U<=2^q L, chooses its minimum and embeds t in an integer interval of length q. The lower endpoint is strict. Even q=0 is handled by contradiction; there is no missing positivity premise because the occupied-window hypotheses provide what the argument uses. |
| `intermediate_scale_count`, `high_scale_count`, `cluster_scale_count` | Specializations return 8,4,5. The high-scale proof expands the closed lower bound (h-r)/2 into the strict window with lower endpoint (h-r)/4 before applying the generic theorem. This is a safe four-scale bound. **Finite t is an input**, not a conclusion about the infinite cluster family. |
| `quarterGrid`, `quarter_grid_bounds`, `quarter_grid_cover` | Five parameters 0,1/4,1/2,3/4,1. Every t in [0,1] has a selected parameter within 1/4. Branches and endpoints are covered. |
| `segment_cover` | Maps the finite grid along an affine lineMap, proving center membership on the actual segment and at most five centers. The exact lineMap distance formula and dist(x,y)<=2r give radius r/2. Degenerate r=0 segments work. This is **five**, not a formal proof of the manuscript's two-center optimization; five suffices for its safe counts. No ball-intersection endpoint extraction is formalized. |
| `parent_edge_projection` | Actual normed-space affine segment displacement: theta in [0,1], parent distance <=2s imply horizontal displacement <=2s. |
| `edge_height_window` | Scalar hypothesis abs((1+theta)s-h)<=r, s>=0 and theta in [0,1] imply (h-r)/2<=s<=h+r. Ambient Hilbert membership has not been converted into this hypothesis inside Lean. |
| `endpoint_group_diameter` | Actual metric triangle inequalities give strict 2a+2b grouped diameter from two endpoint errors and two center distances. |
| `fine_group_bound`, `bottom_group_bound`, `fine_edge_bound` | Exact rational/squared-distance algebra. The latter two **assume** the needed squared-distance estimates. They do not establish Hilbert orthogonal-product identities or construct groups. |
| `cluster_separation`, `meeting_cluster_scale` | Actual metric triangle inequalities: a-b<=dist(u,v), point-root errors a/100,b/100 and b<=a/2 yield 97a/200 separation; two points in the same r-ball yield a<=400r/97. Identification of u,v with points on a unit-vector ray is external. |
| `low_count`, `high_count`, `graph_count` | For natural D>=1, establish the polynomial bounds. `graph_count` takes N and **assumes** one of the required case-count inequalities; it does not prove that a graph has such a cover. This is honestly represented in coverage.json and README. |
| `sourceLambda`, `witnessD`, `graphDelta`, `curveLambda`, `constant_identities`, `curve_count` | Preserve 76800, D=76800²=5898240000, Delta=256D^10=256 lambda^20, and Lambda=10+6Delta^8. Final safe count 6+5Delta^8<=Lambda is exact natural arithmetic. No optimization claim. |

## All eleven semantic controls

`recentered_pair` instantiates the representative cover on {-1,1}; `recenter_factor_one_false` proves radius one is impossible with a single representative from that pair. `strict_packing_pair` explicitly applies the packing theorem, although its final equal-cardinality inequality by itself is a weak test. Its companion `nonstrict_packing_obstruction` gives the meaningful radius-one/weak-separation counterexample.

`three_scales` applies the finite-window theorem to indices {0,1,2}; `widened_window_obstruction` records the excessive cardinality under the widened bound. The latter alone does not state all window-membership conditions; those conditions are checked in the adjacent instance and exact rational diagnostic. The full fresh mutant is also tested.

`segment_instance` and `segment_zero_instance` instantiate actual segment covers including the degenerate endpoint. `cluster_constant_tight` supplies real points 99/50,101/100 near roots 2,1 attaining 97a/200; `fine_radius_obstruction` takes r=1,s=1/64,d=1/32; `low_count_tight` takes D=1. These are meaningful exact controls, not numerical sampling of the universal geometric theorem.

## Independent execution and negatives

One fresh build of the copied final sources passed. All four modules were copied into a new temporary build directory. CDFLocal.olean and Controls.olean were newly compiled there; the type-report imports resolved through that temporary directory first. No author support objects were copied or used, and temporary objects were removed. Thirty support theorems, thirty-nine declarations and eleven control theorems have reports. No warnings, sorry/admit, unsafe, native_decide or added axioms occur. Standard kernel dependencies are limited to propext, Classical.choice and Quot.sound.

All six fresh proof mutants were rejected, with every failure output inspected:

1. Recenter factor two removed: a genuine unsolved ring equality 2Kr=Kr remains.
2. Weak packing separation: linarith cannot contradict dist<=s and s<=dist.
3. Dyadic width multiplied by an extra two: the index-range contradiction fails at linarith.
4. Fine-edge radius strengthened to r/64: linarith fails at the claimed inequality.
5. Cluster coefficient raised to 1/2: linarith fails with the unchanged metric hypotheses.
6. Low-count coefficient lowered from 81 to 80: omega reports an arithmetic counterexample; D=1 is the exact witness.

These failures are at proof goals, not parser/import/unknown-name/type errors. A mutation failure alone does not establish falsity; the independently inspected exact witnesses above explain why each strengthened contract is false.

An independently invoked child actually printed `SOME FAIL` and exited zero. The checked wrapper rejected it with nonzero status and an `exit=0` diagnostic. This tests execution, not merely the wrapper's predicate. Separately, an isolated baseline copy accepted the correct anchor, rejected the wrong anchor, rejected an extra member, rejected changed source bytes, rejected missing source, and accepted again after restoration. Those controls never modified frozen or active implementation files.

## Explicit exclusions and trust boundary

The following remain unpaid by this formal package: net/parent existence, graph realization in Hilbert space, connectedness and root radius, finite abstract edge-length sum, Hilbert projection/product formulas, bottom-height partition, all-regime exhaustion and cover assembly, finite witnesses, normalization and Dvoretzky existence on whole spans, shrinking placements, finiteness/least index and single-cluster handling for the infinite family, spine covers/tails, graph tours, compactness, the Lipschitz limit, Hausdorff length, norm equivalence, and the final nonembedding contradiction. In particular **graph_count is conditional**, finite cluster index sets are supplied, and no full CDF098 theorem is present. The coverage and README accurately acknowledge these limits.

Lean 4.34.1 reports commit 5045d0056413266e57c625dcd7c365b10e377c52. The compiler binary hash is in the fresh receipt. All nine dependency revisions were independently compared to lake-manifest.json; mathlib is d13f23b723b8a846827a245b89c10fc7d3f11612. Their tracked source trees are clean. The compiler, standard library, runtime and preexisting dependency object cache remain trusted inputs: they were not rebuilt, signature-verified, or exhaustively byte-authenticated. No cache writes or network fetches were performed. This is ordinary scoped kernel checking under that explicit environment, not source-to-binary reproducibility.

There are no blocking findings for **PASS_SCOPED_SUPPORT**. The complete frozen target remains governed by its separate written proof and manuscript gates. Nothing in this audit claims worldwide novelty, publication, acceptance of another gate, or a count increase.
