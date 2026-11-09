# r172 research report — no new solution

All 20 reserved IDs have literal, provenance-preserving entries in `results.json`. No new proof or refutation survived. Discovery credit is zero; campaign counts are unchanged. There is no Lean packet because no complete new ordinary endpoint was established.

## Decisive dispositions

- **375830:** excluded by an existing public Lean proof. At Omega HEAD `46927cc328c58a872092e1d1c3bf102e48fa0426`, `MiuraResolution.result` proves the original uniform residual degree assertion. Read its actual endpoint proof and target dossier. The polynomial is chosen before both dimensions; the split and original high-region quantifiers are retained. The external project was not rebuilt here.
- **368916:** excluded as proved in the source's own Theorem 7. Read its contraction/extension induction, not just the abstract.
- **368928:** excluded as resolved in the January 2026 source update. v1 Conjecture 8.1 becomes a consequence of v2 Proposition 8.1, whose hook-count argument was read. If 2^m ≤ n < 2^(m+1) and n > 16 c², then c√n < n/4 < 2^(m−1), so the proposition applies to every fixed-c generic shape.
- **367197:** excluded from discovery investment because v2 Conjecture 14 is absent from v3. No reason for the removal is inferred. A related public Omega regular-cover construction was read, but it is not represented as a complete literal refutation on its own.
- **367260:** historical parked duplicate of the original r40 investigation. Its substantial prior computations and failed induction routes were reopened and retained.

The other 15 targets are parked, with exact source passages, actual coverage, and unresolved lemmas in `results.json`. Six have analytic or class-level algorithmic quantifiers for which a small finite instance would not settle the statement. The dHp source already proves k ≤ 7, so its first uncovered regime starts at |X| = 73. The higher-dimensional Bruhat map, general affine Paper Boat profiles, arbitrary-girth cubic noncontainment, and torus genus minimality require semantic or structural machinery not completed here. Zero finite enumeration is claimed for those routes.

## Reproducible mathematical work

**376401:** `degree-search.json` records 85,672 structured family/parameter checks for families consisting of k-sets with at least j elements in an initial block of size (s+1)j−1. Coverage: k = 2..18, s = 1..8, all nontrivial degree levels, and six specified n-values at and above the threshold. Integer exponents 1, 2, 3, 8 and the proposed positive-part input are checked exactly; fractional exponents are explicitly floating diagnostics. No violations.

`intersecting-search.json` exhausts all 23,936 inclusion-maximal intersecting triple systems on 8 labeled vertices, testing degree level 1 at exponents 1, 2, 3, 4, 8 and the hinge input. No violations. This is not all real exponents. Some tested parameter ranges are already source theorems, so these are checks, not improvements.

`matching-random.json` adds 600 greedy maximal matching-number-at-most-two triple families at each n = 13, 14, 18, seed 172. The construction forbids every new edge disjoint from an existing disjoint pair. Exact degree powers and hinge sums found no violations. This is randomized family coverage, not exhaustive enumeration.

**368018:** `pebbling-search.json` covers all connected labeled simple graphs of orders 2..4 and a recorded sample of order-5 diameter-2 graphs: 97 graphs, 198,116 configurations. `pebbling-extended.json` covers all connected labeled order-5 diameter-2 graphs and the specified order-6 diameter-2 sample: 473 graphs, 1,708,883 configurations. All total-demand-2 targets reached exact thresholds within the recorded totals, with every resolved flag true. No violations. The two sweeps overlap; their counts must not be called distinct graphs or configurations. No demand-total-3 or larger coverage is claimed.

**375825:** `pf-search.json` covers all complete multipartite graphs encoded by integer partitions of orders 2..10 with at least two parts, and every source path parameter t = 3..n: 795 cases. Exact boundary ranks over F₂ and F₃ agree in every case. This detects no 2-versus-3 torsion discrepancy; it neither proves all integral homology is free nor proves a wedge homotopy type. The source uses paths on t vertices, not t edges.

**368113:** `latin-search.json` checks all prescribed total n−1 multiplicity vectors on cyclic group tables of orders 2..9 and XOR group tables of orders 4 and 8. A documented group-translation reduction fixes the omitted row. No obstruction was found. No broad Latin-square enumeration or novel mechanism is claimed.

**368650:** `torus-search.json` computes the bicolored components and best cyclic color order of the permutation-graph model for n = 4..7. It reproduces the source genus values. It is not a manifold realization proof or global genus-minimality certificate, and has zero independent credit.

`validation.json` independently checks the multipartite longest-path formula against direct path search, compares the threshold-family degree formula to direct set-family enumeration, checks three homology sanity cases, and verifies all raw record hashes and resolved pebbling thresholds. Diagnostics remain outside Lean.

## Sources, public registries, and limitations

Exact raw corpus lines retain their terminating newline, one-based chunk line, chunk SHA-256, raw SHA-256, and UTF-8 statement SHA-256 in `extracted.json` and `raw/`. Source HTML and parsed text are retained. `outputs/fetch-*.json` contain dated URL/status/hash receipts; `version-history.txt` records every source's live arXiv version history. Earlier arXiv versions were fetched and target passages compared. This is selective body review, not a claim that every proof in every version or every citing work was read.

`outputs/registry-screen.json` records `/commits/HEAD` for all three registries, all eight spaced GitHub repository queries, the complete Lean Pool metadata/candidates scope, author/ID screens, and actual body matches. Lean Pool HEAD is `01db1d7049cf9668bda1e9e106875ee1278b43e6`; OpenAI/math HEAD is `4eaee87548250b2682affda7d05d947c05554bae`. Omega and OpenAI root recursive trees were truncated, so separate complete D5/Problems and preprints subtrees were obtained. Do not interpret root-tree nonmatches as global clearance. GitHub's two Paper Boat metadata hits were unrelated repositories. General web searches were bounded supporting leads, not a comprehensive bibliographic audit; no novel result is certified by an absence of hits.

All numerical jobs ran serially under `scripts/limited.py`: two CPUs, CPU 120 s, wall 140 s, sampled process-group RSS limit 6 GiB, and MALLOC_ARENA_MAX=2. Logs and receipts are retained. The watchdog samples rather than enforcing a kernel cgroup, so transient overshoot is not excluded. No Lean was run. Two lightweight capped HTTP metadata jobs briefly overlapped before the earlier job's completion was explicitly collected; no numerical, solver, or Lean jobs overlapped. This sequencing imperfection is retained rather than claiming flawless process serialization.

No git, child agents, browser tabs, account actions, messages, uploads, shared ledger changes, or writes outside this lane were performed. No dependency installation was performed. No denied route was retried and TLS verification remained enabled. `CANDIDATE.md` gives the parked route rankings and honest credit/formalization risks.

The finite-search requirement is not fully implemented for every structurally finite target: in particular 367882 and 368769 lack source-faithful engines, and 367149's first unknown regime is beyond the proposed small-instance sizes. These are explicit coverage gaps, not positive results or novelty clearance. The lane does not claim the brief's suggested several-hour investigation duration or a completed literature review. No acceptance is requested on the strength of this bounded pass.
