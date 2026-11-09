# Expanded corpus r115

**No new qualifying solution. Exactly 20 ID-keyed dispositions are in results.json. Credit is zero. No shared files or campaign counts were changed.**

The strongest lead was independently rediscovered prior art. Local search found an explicit 70-bag path decomposition of J(8,4) with maximum bag size 41, hence pathwidth and treewidth at most 40. The source conjectures the value 43. An independent implementation checked all 70 vertices, all 560 edges and the bag interval condition. However, the primary 2014 INRIA report by Coudert, Mazauric and Nisse, **Table 15, printed page 47**, already lists J(8,4), 70 vertices, 560 edges, **pw = 40**. This rules out discovery credit for both 362081 and 362082, which share one source conjecture. The actual primary PDF and dated hash receipt are retained.

Other exclusions: 361699 conflicts with its source's own Example 3, which explicitly prints binary [4,2] orbit counts (4,1,1); 362343 is proved in source Theorem 5.2 and previously by Yao; 362622 is exactly current-source Theorem 3.1, whose proof was read. Historical work on 371184 was found, retained and that route stopped.

## Actual searches

- **361508:** every n = 1 through 40 and r = 1 through 64, using exact hook-length LIS distributions and bounded-uniform convolutions. All Hilbert coefficient sequences are unimodal. Totals equal n! r^n. Source range was n <= 20, r <= 4.
- **361699:** binary dimension-3 codes at lengths 6 through 28 by Burnside under GL(3,2); binary and ternary dimension-2 codes through length 100 by projective column multisets. All tested inequalities hold except the already printed binary [4,2] failure. Zero columns are included.
- **361594:** all even signed involutions generated at n = 4,5,6,7, giving 44,156,752,3256 vertices. MILP with subtour cuts was inconclusive after 61 rounds at n = 6. A second exact edge-exchange method found full Hamilton cycles at n = 6 and 7, beyond the source's n <= 5 constructions. These are only positive parameter instances; no universal proof or formal Cayley-generator bridge is claimed.
- **361906:** 33,179 random ten-point grid samples, with 4,141 in general position and hull size 6. One passed a necessary staircase condition and was skipped. All 945 pairings were tested for each of the other 4,140 sets: 3,912,300 pairings, with no qualifying decomposition. This does not cover all ten-point order types.
- **362081/362082:** random elimination in eight Johnson graphs, followed by vertex-separation local search in J(8,4), J(9,4), J(10,5). The first certificate was independently verified and then excluded by the 2014 prior table.
- **370124:** powerful arrays enumerated for all end-clique/path/end-clique K-chains through 7 vertices at q = 1 and on 8 and 9 vertices at q = 2. All X(1^t,q) evaluations for t = 0 through n agree. These specializations do NOT determine the full symmetric function; no full coefficient comparison is claimed.
- **371156:** primitive sets with min 0, max d, 3 <= d <= 25, 3 <= k <= min(d+1,8), and h = 1 through 16; no failure. The source's diameter divides out the gcd, unlike MathDB's max-minus-min. Nonprimitive progressions only expose a wording defect. Conjecture 5.1 occurs in v1 but is omitted in the current version; omission is not a resolution.
- **361786:** generating subsets enumerated at (n,s) = (6,4),(7,4),(8,3). The implementation fails calibration: it returns 11 at (6,4), whereas source Example 4.13 reports 17 before reflection. These are unvalidated diagnostic counts, not certified coverage or a realizability result. The mismatch and debug conditions are retained.

No finite computational coverage is claimed for the undecidability, spectral-lift, Stanley asymptotic, Dirac or Steklov assertions. General simple topological drawings and the next unenumerated extremal triple-array families were not searched; their input/model gaps are explicit in results.json. The investigation is bounded, not exhaustive literature clearance or exhaustive technical coverage of every family.

## Lean status

lean/Johnson.lean uses actual four-element subsets of Fin 8, intersection-cardinality adjacency, standard finite path decompositions (coverage, edge coverage, interval bags), and pathwidth as the infimum of attainable widths. Strict single-thread compilation passed, proving pathwidth <= 40, the source formula equals 43, and the negation of the source's all-parameter pathwidth equality. It does not prove exact pathwidth or equality of pathwidth and treewidth.

The endpoint and decomposition print only propext, Classical.choice and Quot.sound. This is a formalization of a known result, not a campaign candidate. No fresh extraction, leanchecker or all-local-declaration audit was performed after novelty failed. No accepted Lean packet or full upstream rebuild is claimed. All Lean calls used -M3500; dependencies were read-only. A broad Mathlib import was RSS-killed; narrower imports with -j1 compiled successfully in about 17 seconds. See logs/lean-single.*.

## Provenance and process

raw/ preserves the exact JSONL lines including newline. extracted.json records one-based chunk lines and chunk/raw/statement hashes. Sources have dated URL/status/hash receipts. Both GitHub /commits/HEAD endpoints were checked: OpenAI 4eaee87548250b2682affda7d05d947c05554bae; Omega ddeafbc85f06ddade64bc7aab47c37698ecd7fe6. Complete nontruncated D5, Problems and OpenAI preprints trees were fetched and path-screened. Path screening is not proof-body or global novelty clearance. The decisive prior-art exclusion relies on the actual primary paper.

Tableau HTML returned 404; the public arXiv PDF succeeded. Citeseer returned 404 by direct HTTP and later 403 through web fetch; no subsequent Citeseer request was made. The independently requested primary HAL PDF succeeded. No denied ScienceDirect route, arXiv search API, browser tabs, external messages, author contacts, uploads or git operations were used. No shared ledgers were edited.

Numerical calls used scripts/limited.py, at most two CPU affinities, CPU 120 seconds / wall 140 seconds and sampled RSS monitoring around 6 GiB. Receipts are not a strict cgroup or transient-memory guarantee. The g++ spawn failed because it was absent from PATH; no compiler process ran and the code search was completed in Python. Two low-memory searches briefly overlapped; the first staircase run was stopped and restarted, with receipts retained. No heavy solver/Lean processes were deliberately overlapped. No lane background jobs remain at handback. Independent review and root acceptance were not performed.
