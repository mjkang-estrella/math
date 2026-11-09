# Expanded corpus r181

No qualifying new solution was found. All 20 reserved IDs have exact-provenance dispositions in `results.json`: six are excluded by prior/source results and fourteen are parked. Credit is zero. `CANDIDATE.md` records the negative candidate verdict. No Lean endpoint, partial surrogate theorem, or Lean packet is proposed.

This was a bounded investigation with primary definition recovery, selective theorem/proof-body reading, literature searches before computations, current registry screens, and sustained finite searches on three routes. It is not an exhaustive literature review or a claim to have resolved the parked problems. In particular, it did not settle every source gap or push every finite route past the authors' verified range. The grid computation only reproduced a known case; coupled-colouring degeneracy remained inconclusive on many instances.

## Dispositions

| ID | Verdict | Decisive evidence or remaining gap |
|---|---|---|
| 349645 | Parked | Coupled list colouring of partial 3-trees; merged faces prevent a subgraph-monotonicity shortcut. Stacked/deleted-edge diagnostics below. |
| 349656 | Parked | Exact Slow Nim boxes computed; semilinearity needs a global invariant, not finite P-position data. |
| 349708 | Prior proof | Hujdurović et al., arXiv:2108.03943, Theorem 3.4, including direct-product proof, read. |
| 349881 | Parked | Fujino Conjecture 1.21: source's weaker 2d bound does not imply d+1. |
| 350049 | Parked | Source attributes the conjecture to 1982. An unknown global additive constant cannot be refuted by an isolated finite SRG. |
| 350069 | Parked | No violation in exhaustive tournaments through order 8 or structured local searches through order 14. |
| 350318 | Source proved | Das–Jana Section 2 explicitly proves Conjecture 1.1; proof body read. |
| 350439 | Prior refutation | Bernstein–Walsh Theorem 12, including the Vámos rank-2 obstruction and parallelism contradiction, read. |
| 350518 | Parked | Source Theorem 1.8 equates this to Albertson–Berman; exact stacked cases do not resolve it. |
| 350520 | Parked | Genus rotation-system search only reached a known planar case; meaningful next cases remain too large for raw enumeration. |
| 350624 | Parked | Finite-grid minimax searches found no violation; no valid continuum inference or uniform denominator theorem. |
| 350638 | Prior proof / paraphrase issue | Alon et al. Theorem 5 proves fixed-k oriented-graph NP-completeness. Fixed-k tournament inversion instead has a quadratic algorithm. Reduction paragraph read. |
| 350662 | Parked | Fractional-weight edge-appending step in the analytic weight-bound argument remains unproved here. |
| 351078 | Parked | Current September 2026 v3 retains Conjecture 69. Existential delta and n0 rule out fixed-small-instance refutations. |
| 351124 | Parked | Protected adjacent cyclic-tiling family; no source-ingredient or empty-range endpoint claim. |
| 351193 | Parked / definition correction | Source L is the branch-resolving quantity, not leaf count; 2025 citer restores c>=2. No source-scope violation found. |
| 351194 | Parked | Exact edim, zero forcing and cycle-rank checks found no violation. |
| 351288 | Source refuted | Source Theorem 1.5 and actual proof give an accumulation point at 1/4, contradicting finite CRG determination. |
| 351460 | Prior refutation reported in source | Source Theorem 2 explicitly cites infinitely many Špacapan counterexamples; no independent replay of that construction claimed. |
| 351463 | Parked | Full weighted PL/PH structures and finite surgeries exceed the proved vertex-scaling cases. |

## Exact computational coverage

All mathematical computations ran serially through `scripts/limited.py`: two CPU affinity slots, CPU limit 120 seconds per process, wall watchdog 140 seconds, sampled process-group RSS ceiling 6 GiB, 12 GiB address-space ceiling, and `MALLOC_ARENA_MAX=2`. Sampling does not rule out unsampled RSS transients. Full completed mathematical run logs and receipts are in `logs/`. Build-attempt retention limits are disclosed in `outputs/tool-failures.txt`.

* **350069, tournaments:** every labelled tournament of orders 5, 6, 7; every order-8 tournament represented after fixing vertex 0's outgoing neighbours to an initial segment (16,777,216 representatives, covering all isomorphism types). All k from 5 through n were checked using the complete permutation orbit of C_k. At order 8, maxima for k=5,6,7,8 were 12,18,2,1. Every maximizer encountered was isomorphic to the distinguished C_8. The `witness` value in exhaustive logs is stale when `noncanonical=0` and must not be interpreted as a witness. A second mechanism used 24 starts at each n=9..14 and k=5,7,9, half random and half perturbed carousel, at most 30 improving steps. Across 432 starts, no induced count exceeded the baseline; local searches do not establish uniqueness or global optimality.
* **351193/351194, graphs:** all labelled connected graphs of orders 3..7 were generated (counts 4,38,728,26704,1866256). The paired test restricts to c>=2. Trivial universal n-1 bounds discharge many graphs; 5,520 order-6 and 265,755 order-7 graphs required explicit resolving-set calculations. Source L counts terminal legs minus one at branching vertices. Zero forcing was computed by exhaustive initial sets and exact closure. No violation. Separately, exact dim/edim/Z were computed for 112 sorted theta length triples up to 8 and all 729 K4 edge-length assignments in {1,2,3}; no violation. Trees/unicyclic graphs are not claimed covered by the paired c>=2 run.
* **350624, fractional games:** all nonempty hypergraphs on 2 and 3 labelled vertices, and 166 inclusion-antichain hypergraphs on 4 vertices, were evaluated at increments 1/q for q=1,2,3,4. The second run included every one of the 32,767 nonempty 4-vertex hypergraphs, completing q=1,2,3 with no positive gap over the integer game. It was killed at wall 140.015 seconds during q=4 and was not restarted. The partial log is retained; no completed JSON exists for that capped run. Restricting BOTH players to a grid is neither a certified lower nor upper bound on the real-weight game. The source's rational-value theorem supplies no uniform denominator bound. An exact PLCR envelope implementation would be needed for a real certificate.
* **349645/350518, embeddings:** generated all labelled stacking histories modulo identical stored embedding states through n=8: 1,1,3,15,105,945 states at orders 3..8. Tested all connected zero-, one-, and two-edge deletions, totaling 176,594 instances across these orders. The coupled conflict graph had degeneracy at most 6. Degeneracy <=5 supplies a sufficient six-list guarantee only on those instances; degree-6 cores remain inconclusive. Exact robust connectivity of stacked triangulations was obtained by connected-dominating-set enumeration and maximisation of requested leaves. Minima at n=4..8 were 3/4,2/3,2/3,2/3,1/2. These are not all planar triangulations.
* **350520, grid:** all 331,776 cyclic rotation systems of G(1,1,2), whose parameters are path lengths, were enumerated. Genus histogram: 0:2, 1:232, 2:10002, 3:121140, 4:200400. Minimum 0 is a known planar case, not a new improvement.
* **349656, Nim:** full dynamic programming for sorted positions, n=5..8, k=2..4, coordinates through 14 for n<=6 and through 10 otherwise. Exact position/P-position/transition counts are in `outputs/nim.json`. The uniform shift-by-two ansatz fails; that does not refute semilinearity.

The source reports computational evidence for carousel small k and metric small orders, but the exact verified finite ranges are not established uniformly from the inspected passages. No claim that all these computations exceed those ranges is made. Global-constant, asymptotic, protected-adjacent, and analytic targets received source-backed dispositions instead of inappropriate finite refutations.

## Sources, registries and credit limits

`raw/` preserves each exact corpus line including newline. `extracted.json` records chunk SHA-256, one-based line, raw-line SHA-256 and statement SHA-256. `sources/` stores current arXiv abstract pages/PDFs, selected published/citing PDFs, exact URL/status/UTC/SHA-256 receipts, and registry downloads. Downloaded content was treated as data; no downloaded program was executed. Network requests used TLS verification and a deny-host redirect guard. No denied routes were retried.

Lean Pool HEAD: `01db1d7049cf9668bda1e9e106875ee1278b43e6`; its `LeanPool/projects.yml`, candidate files and full tree were screened. Current Omega HEAD: `da33b587a42cb6d443481d45fa83806c9cfecf68`; complete nontruncated D5 and Problems listings were fetched and screened. OpenAI/math HEAD: `4eaee87548250b2682affda7d05d947c05554bae`, unchanged from the inherited complete-preprint snapshot. No matching target statement was identified in the bounded screens; unrelated keyword hits are retained rather than silently discarded.

Exactly eight spaced GitHub repository searches were attempted. All responses had the same SHA-256, total count 65,458, and generic Lean repositories, despite distinct query URLs. They are uninformative and do **not** clear GitHub prior art. The query ceiling was respected. `outputs/registry-screen.json` records the queries, hashes, heads, hits and limits. No parked route has novelty clearance.

Six exclusions require no Lean work. The other fourteen have unresolved mathematical gaps. No strong lead, literal Lean endpoint, manuscript or formal replay is claimed. The C compiler driver `leanc` was used only to compile C diagnostics; neither `lean` nor `leanchecker` was run. No upstream rebuild claim is made. No git, shared-ledger edit, child agent, browser tab, account action, upload, external message or author contact occurred. No background process remains.

Reproduction instructions: `scripts/REPRODUCE.txt`. Principal machine-readable handoff: `results.json`. Candidate verdict: `CANDIDATE.md`. File hashes: `outputs/manifest.json`.
