# Expanded corpus r190 research report

No qualifying new solution or strong lead was found. All 20 reserved IDs have individual records in `results.json`: eight are already proved/refuted, one was removed from the author's later version, and eleven remain parked. No discovery credit, campaign-count change, Lean endpoint, or novelty clearance is claimed.

## Prior resolutions and withdrawal

| ID | Disposition and decisive primary evidence |
|---|---|
| 334519 | Already refuted: Cambie–Jooken, arXiv:2311.05542, Theorem 3.2, a 32-vertex 4-regular girth-at-least-5 graph beats the cage for every fugacity greater than 37. |
| 334569 | Already proved: Admasu–Sehgal, arXiv:1806.03774, Theorem 3.3 and Remarks 2–3 explicitly confirm Tóth's degree conjecture. |
| 334829 | Withdrawn under brief's rule: Conjecture 2.10 in v1 / 2.3 in v2 is absent from v3. The non-spherical manifold in v3 is not asserted to refute a sphere claim. |
| 334889 | Already proved: Alec Sun, arXiv:1907.06623, Theorem 1.11 determines the exact threshold. |
| 334926 | Already proved: Alishahi–Meunier, arXiv:1704.02921, Theorem 1 and its explicitly printed implication. Publisher PDF also retrieved. |
| 330095 | Proved in the cited one-page source itself: Haase, Theorem 4. |
| 330160 | Already proved: Ahmadi–Shafaeiabr, arXiv:2108.10042, Theorem 1 lists and treats all eleven trinomials. |
| 330268 | Refuted in the cited source itself: Leopardi, Theorem 3, for every m at least 4. |
| 330331 | Proved in the cited source itself: Sudakov–Volec, Theorem 2, stronger than the printed Shearer conjecture. |

## Sustained finite routes

**373247, signed complete graphs.** The source's incidence palette and sign convention were used. After switching the star at vertex 0 to positive, all 2,097,152 signatures on K8 were covered by 2,520 distinct templates. Each template consists of a zero-colored perfect matching and three balanced spanning 2-factors. Around a cycle, propagation of an incidence color is consistent precisely when the product of edge signs is positive; each vertex then sees both signs of that color. This explains the semantic bridge, but is not a Lean proof. A further 700 sampled signatures at each of orders 10, 12, 14 and 16 also passed. These samples use seven densities, 100 signatures per density, seed 190. No failure, universal construction, or full-scope theorem resulted. The n=8 statement alone would be a parameter instance, with zero campaign credit. The additional MathDB reference arXiv:1610.01676 retrieves an unrelated geometric graph-decomposition paper.

**329942, modular p-free sets.** The literal quantifier is too weak to express the substantive nonpower discussion: choosing a different known modular set for each exponent is uncredited wording work. The search therefore followed the source's discussion of finding cardinalities outside all powers, without claiming that a fixed-prime example solves every odd prime. Exhaustive DFS over all subsets containing zero, with modular AP-freeness and increasing-prefix coverage pruning, completed these cases:

| Prime p | Modulus N | Qualifying sets | Cardinalities |
|---|---|---|---|
| 5 | 11, 17, 23, 49 | 0 in each case | none |
| 5 | 25 | 14 | 16 only |
| 7 | 49 | 44 | 36 only |

The p=5, N=49 run visited 263,227 nodes; p=7, N=49 visited 9,856. The source's Example 6.6 was independently checked against the search conventions and passes. The p=5, N=75 run reached the 140-second wall cap and was killed. It has no completed coverage result and was not restarted. Repeated-residue AP conventions on composite moduli remain a fidelity limit; these diagnostics are not certified mathematical classifications.

**330178, unsigned zero-sum flows.** The search found labels in {-2,-1,1,2} for 200 samples on even orders 6–24, including 180 distinct labelled graphs. Separate verification confirms degree 5, 2-edge-connectivity, and zero incident sum at every vertex in all 200 samples. No counterexample or all-order structural proof was found. The oriented-flow interpretation was not used.

**334564, bounded representation.** All 262,144 ordered pairs of edge subsets of K3,3 admit a perfect matching respecting both upper quotas. Maximum deficit in this experiment was zero. An isolated finite deficit could not refute the conjecture because c(m) is existential; a negative result would require unbounded deficits at fixed m.

**334318.** The five simple 5-edge-connected graphs up to isomorphism on at most seven vertices (K6 and K7 minus a matching of size 0–3) realize every required Z3 boundary in an orientation search. This excludes neither larger simple graphs nor multigraph obstructions.

## Parked mechanisms and limitations

The other parked IDs are 334235 (uniform symbolic semilinear reduction beyond h=8), 334453 (finite attainment over an unbounded nonempty locally constrained graph class), 329603 (generic spherical rigid-circuit stress-sum lemma in dimension at least 3), 329855 (DCA construction preserving both P1 and P2), 329971 (uniform subcritical infinite-graph probability estimate), and 330175 (noncrossing colorful geometric simplex partitions). No exhaustive DCA, generic-rigidity, or geometric-configuration search was completed. These gaps are explicit rather than filled with surrogate certificates. Small DCA orders and low-dimensional rigidity cases already in the sources are not new leads.

All listed versions of the 20 main arXiv sources were acquired with retained receipts. Selected statements and adjacent arguments were compared, rather than every proof in every version. The published Doryn PDF was retrieved: its Conjecture 20 retains the zigzag assertion. Publisher and citation-neighborhood review remains incomplete for several parked targets. The Lancaster download returned a directory page, not the requested manuscript. The institutional DCA PDF is v1, not independently authenticated typesetting. ScienceDirect, Crossref, MathDB and the arXiv search API inherited denied routes were not retried. Web search results are preserved separately; they are not HTTP-status receipts or worldwide novelty clearance.

## Public proof registries and history

`outputs/registry-screen.json` records fresh /commits/HEAD observations:

- Lean Pool: `01db1d7049cf9668bda1e9e106875ee1278b43e6`.
- Omega: `4a2bbb5e2aef76e05a1db56572da1ea06ba0a2b9`.
- OpenAI/math: `4eaee87548250b2682affda7d05d947c05554bae`.

Lean Pool's actual `LeanPool/projects.yml` and every candidates/ blob were fetched at the pinned commit and screened. The initially requested root projects.yml returned 404 and was retained; the actual tree supplied the correct path. Eight spaced GitHub repository searches, each an arXiv ID plus lean, returned zero repositories. They do not constitute exhaustive author/name/code searches. Current complete Omega D5/Problems and OpenAI preprints path listings were fetched. Broad keyword matches are retained; relevant displayed matches were unrelated. Proof bodies were not exhaustively inspected, and no candidate has registry clearance.

Historical ID searches across the research tree found three numerical false positives and no target-specific prior disposition. This is not complete title/alias history clearance. The campaign and inherited ledgers were read without changes; compact accepted/excluded summaries are in `logs/context.log` and snapshots in `outputs/context-*`.

## Reproduction and resources

Run scripts from this lane using `python3 -I scripts/limited.py UNIQUE_LOG_NAME python3 -I scripts/SCRIPT.py ...`. Log names must be new: the wrapper opens logs exclusively. Download receipts also must have new names. No source download is executed. All writes were confined to this lane, and no git, browser, account, messaging, upload or child-agent actions were used.

The wrapper restricts affinity to two CPUs, CPU to 120 seconds, wall to 140 seconds and sampled process-group RSS to 6 GiB, with MALLOC_ARENA_MAX=2. RSS is sampled, not a cgroup guarantee. One numerical search ran at a time. Metadata and HTTP operations are light. The N=75 cap and the unavailable networkx/g++ exploratory attempts are retained in logs; the actual searches use only Python's standard library. No packages were installed. No Lean process was run because no full-scope endpoint survived. No background process remains.

Main artifacts: `results.json`, `CANDIDATE.md`, `outputs/registry-screen.json`, `outputs/intake.json`, `outputs/versions.json`, `outputs/*` numerical records, `sources/*` immutable bodies and receipts, `raw/*.jsonl`, `scripts/*`, and full `logs/*`. These are research dispositions with candid remaining gaps, not 20 technically exhausted or novelty-cleared solutions.
