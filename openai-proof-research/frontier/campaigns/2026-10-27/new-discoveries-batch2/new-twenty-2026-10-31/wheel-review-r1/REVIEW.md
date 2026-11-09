# Independent adversarial review of MathDB 371637

Recommendation: **reject campaign credit**. The formula and the formal proof pass the mathematical and technical checks, but gate E fails: the claimed new lower-bound contribution is a routine corollary of the source's own Lemma 4.2. Root alone decides acceptance. No credit is awarded by this review.

## Decisive objection: source Lemma 4.2 already gives the dual bound

Write m = 2t + 1, let I be independent in the Cartesian wheel square, let n = |I|, and let a and b count its two mixed hub layers. The actual statement of [source Lemma 4.2](https://arxiv.org/html/2511.18747v1#S4) is

n ≤ tm + 1 + (1 − t)a.

Apply the same lemma after interchanging coordinates:

n ≤ tm + 1 + (1 − t)b.

Adding immediately gives

2n + (t − 1)(a + b) ≤ 2(tm + 1) = 2(2t² + t + 1).

The left side is **exactly** the candidate's weighted independent-set sum: every vertex initially contributes 2, and each mixed vertex contributes an extra t − 1. This includes independent sets containing the hub-hub vertex, without any extra case. Thus the entire proposed dual inequality follows by adding two inequalities already in the source. Multiplying coverage and summing then gives the candidate's lower bound with total vertex weight 2(6t² + 7t + 3). The source's observed profiles furnish the matching upper bound as described below.

This is stronger evidence than merely saying the new matching argument looks elementary. It identifies an existing primary-source lemma and an explicit two-line deduction that makes the new simultaneous-deletion proof unnecessary for this endpoint. The source's remark before Conjecture 7.3 that generalizing the small-t extremal LP points suffices does not eliminate this subsumption. Nor does the fact that the source still labels the result a conjecture establish mathematical significance under the campaign's stricter rule.

The reviewer-created `replay/formal/ReviewSourceCorollary.lean` kernel-checks the displayed implication as an arithmetic lemma. It deliberately takes the two printed Lemma 4.2 inequalities as hypotheses; it is evidence for the subsumption objection, not an independent new formal proof of source Lemma 4.2. The full candidate remains separately replayed without those hypotheses. Source Lemma 4.2 is used in the paper's t ≥ 2 setting. The additional t = 1 case is K4 □ K4 and routine. It provides no campaign credit.

## Gate A — PASS: source and definition fidelity

Read the MathDB raw statement and both cached and live arXiv bodies. The live abstract page still lists v1, and the live body displays Conjecture 7.3 with numerator 6t² + 7t + 3 and denominator 2t² + t + 1. The source defines W_n as C_n joined with K_1 and its product adjacency is Cartesian, not strong or tensor adjacency. Its surrounding nontrivial odd-wheel range is t ≥ 2; the displayed conjecture and copied MathDB statement omit a separate range. The formal t ≥ 1 is a legitimate extension to C3 joined with a hub. It must not be advertised as covering t = 0 or undefined cycle conventions.

`Foundation.lean` uses Option (ZMod m): none is the hub, some i is a rim vertex. `rimAdj` explicitly excludes equality and requires a difference of ±1. For m = 3 this makes the rim K3 and the wheel K4, as required. `wheelSquare` uses mathlib's `boxProd`, so edges change exactly one coordinate along a wheel edge. `Independent` excludes adjacency between every distinct selected pair. `FractionalColouring` gives nonnegative real weights on all independent finsets, including the empty finset, and coverage at least 1 at every vertex. Duplicate indexed upper-family sets have their weights added by `indexedColouring`; they are not incorrectly treated as distinct independent finsets in the definition.

`fracChromatic` is the real sInf of feasible total weights. The potentially dangerous empty or unbounded set conventions do not enter: `singletonColouring` proves feasibility, and nonnegativity proves boundedness below before either infimum inequality is applied. `Target` quantifies every natural t ≥ 1 with exactly the advertised equality. No residual independent-set bound or existence assumption occurs in the endpoint. A stale Foundation comment saying no proof is claimed is merely stale documentation; Final proves the proposition.

## Gate B — PASS: ordinary mathematics

The submitted proof is correct even though it is unnecessarily elaborate for the endpoint. For the hub case, a = b = 0 and the rim contributes at most mt vertices by independent cycle fibres, giving 2 + 2mt. With one mixed layer empty, the surviving fibres give r ≤ t(m − a) or t(m − b); the weight is at most 2mt + (1 − t)a or its transpose, below the target cap.

For two nonempty mixed layers, the deletion-cycle component argument has a paths, whose orders sum to m − a. The number o_A of odd paths has parity m − a, whereas a has opposite parity, so o_A ≤ a − 1. Each product of paths has independence number the ceiling of half its order, by an edge matching and the larger checkerboard class. Summing gives 2r ≤ (m − a)(m − b) + (a − 1)(b − 1).

The formal proof instead anchors a near-perfect cycle pairing at a deleted vertex. Deleting A fixes both endpoints of every pair meeting A. Every newly fixed point outside A maps injectively to A minus the anchor, hence at most a − 1 remain. The product pairing first uses a nonfixed second-coordinate partner and uses the first-coordinate pairing only in a fixed second-coordinate column. Its fixed set is the product of the two fixed sets. The union/intersection count 2|I| ≤ |S| + |Fix| is valid. No independence hypothesis on the deleted sets is silently needed by this matching construction.

The final arithmetic is especially transparent:

F(a,b) = 2t − (t + 1)(a + b) + 2ab
       = −(t − a)(b − 1) − (t − b)(a − 1) ≤ 0.

The upper families are actual independent sets. P0 uses a difference in an alternating t-subset of the odd cycle, plus the hub-hub vertex. P1 deletes one row and one column and takes either checkerboard parity on the remaining even path square. P2 deletes translates of an alternating t-subset; the remaining coordinates are t odd representatives and the endpoint 2t. Taking pairs whose endpoint roles agree gives t² + 1 rim vertices. A remaining rim edge changes the endpoint role, proving independence.

The exact indexed weights are 1/m for each of m P0 shifts, 1/(2mD) for each of 2m² P1 indices, and 1/D for each of m² P2 indices, where D = 2t² + t + 1. Their class incidence counts are respectively (m,0,t), (0,2m,4t²), and (0,mt,t² + 1), per vertex in the hub, mixed and rim classes. Weighted coverage is exactly 1 in each class. Total weight is 1 + m/D + m²/D, the target fraction. These constructions generalize profiles already supplied by the source.

Independent computations use newly written pure Python with exact rational arithmetic, no submitted solver output or third-party solver dependency. Every pair A,B of independent cycle subsets is enumerated. For nonempty A,B the actual complement grid is constructed, bipartiteness checked, and maximum matching found by augmenting paths to compute its exact independence number. Empty-side maxima follow the cycle-fibre bound with alternating-shift attainment. Hub profiles use the same toroidal attainment. The three-variable orbit LP is solved by enumerating basic primal solutions and checking exact rational primal and dual feasibility and equality, not by accepting floating-point solver status. This suffices for the full fractional LP by averaging under rim symmetries and coordinate interchange, even when those are only a subgroup of the full automorphism group at t = 1.

For t = 1, 2, 3, 4 the exact results are 4, 41/11, 39/11, 127/37. Every enumerated profile also satisfies both printed source Lemma 4.2 inequalities. `receipts/independent-lp.json` records the profiles and rational certificates. `receipts/independent-coverage.json` checks every family index, every graph edge within each selected set, every vertex's exact coverage, and total for t = 1 through 6. `receipts/pairing-check.json` checks the anchored deletion construction for every nonempty deleted set through t = 6, and o_A ≤ a − 1 for all independent deleted sets. These computations supplement, rather than replace, the uniform proof.

## Gate C — PASS: fresh strict Lean replay and complete local audit

The source zip hash is f92bef69b502dd3d06b644891e284891b52687f73981022c2141312c3019aa3a. Extraction was into a new empty review-local directory after rejecting absolute paths, parent traversal, symlinks and precompiled olean/ilean members. The local proof sources are verified against the supplied source manifest. Read-only input hashes are recorded before and after.

All 14 proof modules were freshly compiled with Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, `-j1 -DwarningAsError=true`, using the assigned read-only package cache. All 14 were independently passed through leanchecker. The initial leanchecker invocation failed to find lean on PATH; this environmental failure is retained under `logs/initial-check-Foundation*`, corrected by adding the pinned bin directory, and the full checker sequence then succeeded. A first numerical script failed because system Python lacked numpy; it was replaced by the dependency-free exact implementation, with the failed log retained.

Reviewer audit modules enumerate constants by originating module, including generated and private declarations. They print each name, module, full elaborated type, body presence using `value? (allowOpaque := true)`, declaration kind, unsafe/partial flags and transitive axioms. Every proof/definition has a body. The only absent-body declarations are the FractionalColouring inductive, constructor and recursor, which are normal kernel primitives, not added axioms. All local declarations are safe and nonpartial; the only transitive axioms are propext, Classical.choice and Quot.sound. No added axiom, sorry, admit, native_decide, ofReduceBool or hidden weakening was found. Source scans and the full declaration index accompany the logs.

`ReviewRestatement.lean` independently expands the target into the infimum of actual fractional-colouring total weights on the Cartesian product and derives it directly from target_proved. The underlying graph and colouring definitions were separately inspected as described in gate A. Reviewer-created negative controls attempt False, an incorrect t = 1 value and removal of the range hypothesis; all are rejected for substantive type/proof failures. These controls do not constitute a complete consistency proof but check that the endpoint is not an all-purpose axiom or unconditional range surrogate.

Each substantive Lean, checker, HTTP and computation subprocess was run in a systemd MemoryMax=6G scope, with two-CPU affinity, CPU limit 120 seconds, wall limit 140 seconds, sampled private RSS limit 6 GiB and MALLOC_ARENA_MAX=2. Receipts retain peak memory and wall time. Shell/tool orchestration is separate from these bounded subprocesses. No background work is left at handback.

## Gate D — QUALIFIED_PASS for bounded explicit-prior-proof search; subsumption objection remains

Live registry roots were resolved exclusively with `/commits/HEAD`, then immutable tree and raw URLs. OpenAI remains 4eaee87548250b2682affda7d05d947c05554bae. Omega advanced to 8cc0a208f4a45c037444c8de3360f7d30bcd0f60. The authors' code remains 87de114bc0e72e9317f73855d752a4f6c1836328. The current preprints, D5 and Problems subtrees were screened by path and their responses checked for truncation. The two wheel-related D5 files and one Problems file were fetched and inspected; they concern HIV wheel dynamics and the thirty-wheel sieve, not this problem. This is a path screen and selected body review, not a full registry body search.

All six author repository files were fetched at the pinned head. The README and square profile program were read in detail. The square code is a fixed-size NetworkX graph plus binary Gurobi profile optimization and a reduced LP, with no parametric proof. The cube and fourth-power programs have different targets and were only screened for scope; no author program was executed. Other branches remain unread.

OpenAlex returned zero indexed citing works. Clow's author search and broad wheel/fractional and ultimate-independence searches were screened; the latter broad searches have substantial irrelevant results and cannot establish absence. Pragada's author search, a Kumar/wheel query, and the complementary wheel/chromatic query timed out and were not retried. All forbidden/previously denied routes in TASK.txt were avoided. No browser, author contact, registry mutation or publication occurred.

Actual introductory/definition sections of 2610.13852, 2607.19817, 2609.00210, 2607.05961 and 2607.22915 were inspected. They concern respectively distance graph powers, energy versus independence, local Caro–Wei bounds, t-perfect colouring with odd-wheel t-minors, and oriented chromatic bounds. None of those inspected statements resolves this Cartesian square formula. Later author works outside these sections, older ultimate-independence literature beyond the source's quoted results, unnamed registry bodies, code branches, and unindexed works remain unread. The known W5 value is explicitly prior art, not part of the claimed contribution.

No separately published explicit uniform proof was located in this bounded search. This qualified search verdict does **not** clear subsumption: the source Lemma 4.2 deduction above is the material prior-result objection, independent of whether another paper has written it out.

## Gate E — FAIL: routine corollary under the campaign standard

The full uniform matching formalization is technically useful and correct. It is not evidence that this endpoint requires a new significant mathematical insight: adding the source lemma in the two orientations gives exactly its entire lower-bound inequality. The source already has the LP reduction, active profiles and target formula. Promoting the formula to a short corollary with explicit uniform upper constructions may merit a correction or formalization note, but the campaign expressly excludes routine corollaries and mere formalizations. The source's own conjecture label cannot override that rule.

Next action for root: preserve the certificate as a verified formalization, award zero new-discovery credit, and reconcile this explicit source-lemma objection before any acceptance claim. If disputed, review the two oriented Lemma 4.2 applications and the identity weight(I) = 2|I| + (t − 1)(a + b); no new large computation is needed.
