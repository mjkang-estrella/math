# expanded-corpus-r219

No new mathematically significant solution or literal Lean endpoint was obtained. All 20 reserved records have ID-keyed dispositions in `results.json`: **9 excluded, 11 parked, 0 proposed for acceptance**. No campaign count or ledger was changed.

## Exclusions worth retaining

- **375093**: arXiv:2606.04854 Theorem 2.4 already proves the normalized Artemev identification.
- **375205**: arXiv:2606.10885 Theorem 1.1 already proves Hegedüs, even for all prime-power balance parameters.
- **375277**: Moore arXiv:2608.09649 Theorem 1.2 and Mirabi arXiv:2608.11736 Theorems 1.1/3.2 independently prove the one-point extension. Actual theorem and proof bodies were inspected.
- **375522**: arXiv:2606.24016 **v2** removes the periodic conjecture and prints its counterexample in Section 6/Figure 3: the quotient by `⟨(9,0),(-3,1)⟩` has 12,321 spanning trees, exceeding 11,664 for the standard nine-vertex torus. Do not rediscover or augment it.
- **375561**: current public Omega `DemoStrongPeriodBoundRefutation.result` refutes the literal unrestricted bound at the singleton. This is also a smallest-order correction, independently ineligible under campaign standards.
- **375685**: Ohba is the Noel–Reed–Wu theorem.
- **375777**: the current source explicitly refutes the printed stability conjecture using its own family and identifies the slip before Theorem 1.14. Neither that example nor the correction is creditable.
- **376070**: prior OpenAI/math family 013 states the complete Ostmann theorem. The nonnegative-integer theorem subsumes positive summands. Primary scope and manuscript introduction/preliminaries were read. Comparator challenge files are intentional statement placeholders, not independently replayed proofs.
- **376299**: Chen arXiv:2607.25412 Theorem 1.2 explicitly refutes Hoàng using an infinite family of MNPD graphs with a bisimplicial vertex.

## Sustained finite routes

**375704, length-area transferal.** The exact target is generic full row rank of the polynomial Heron Jacobian, with triangle row `(-x+y+z, x-y+z, x+y-z)`. Hall necessity, the source's stronger sufficient edge choice condition, its banana calculation, and the cited Lew–Nevo–Peled–Raz Conjectures 9–10/Example 11 were inspected. The cited example does not itself refute this target: the independent length Jacobian and its composition with a fixed-dimensional distance-rigidity map are distinct.

`transferal.py` checked all 15,504 selections of 15 triangles from the 20 triangles on six vertices. Of these 15,264 admit an injective edge matching; no persistent rank defect was found over `F_65521`. Additional reproducible samples on nine and twelve vertices contained respectively 875 matching-admissible selections out of 1,000 and 6,165 out of 10,000, again with no persistent defect. A second assignment is tried after an initial deficient modular evaluation. These are exact modular diagnostics, not a uniform proof. Smaller face families and all larger orders were not exhaustively covered. The missing result is either a uniform nonzero maximal minor under Hall or an explicit family with an identically deficient Jacobian.

**376344 / 376345, rigidity.** Source Conjectures 9.1–9.2, the edge-transitive/bridgeless positive results, Example 7.5, and the cited weaker-connectivity zeolite obstruction were screened before generation. We did not augment the printed obstruction. In 1,000 independently generated unions of `K4` on 12 vertices, 561 were six-connected and all had full rigidity rank modulo 65,521. For line graphs of switched simple four-regular base graphs, 956 of 1,000 base-order-eight samples and 941 of 1,000 base-order-twelve samples were six-connected; all those line graphs had full rigidity rank. Six-connectivity for these line graphs was tested by vertex-splitting max flow. The line graphs have orders 16 and 24. Sampling may repeat isomorphism classes and is not uniform. Ordinary rigidity is only a necessary condition for the global rigidity target; no generic stress certificate or global rigidity conclusion is claimed.

**376357, acyclic separators.** The source's printed cyclic-neighborhood families and discharging arguments were read first. Exhaustive labeled generation below the conjectured arc threshold covered 33,696 minimum-outdegree-two candidates at order five and 25,000,000 at order six. At order six, 1,961,980 passed the minimum-indegree filter, 1,720 passed cyclic in/out neighborhoods, and 810 were strongly connected. Every one had an acyclic separator. Zero counterexamples. Additional generation tested 10,000,000 order-seven and 5,000,000 order-ten samples with `3n-4` arcs; respectively 16 and 0 survived all local/strong filters, and no counterexample survived the full separator test. The order-ten sampler was therefore weak, not substantive clearance at that order.

A second route encoded **all** acyclic separators as SAT constraints. For each partition `U,W,S` with nonempty `U,W` and each topological order of `S`, a clause requires an arc from `U` to `W` or an arc violating that order. A sequential counter enforces at most `3n-4` arcs. At order seven, CaDiCaL returned UNSAT: 620 variables, 16,004 clauses. At order eight, the run with 986 variables and 120,850 clauses was killed by its 120-second CPU limit **without a verdict**. The partial DRAT output is retained and is not a proof. The order-seven DRAT output is also retained but has not been independently checked or formalized. This bounded result does not resolve the reserved conjecture.

## Other parked records

375850, 376096, 376097, 376183, 376276 and 376277 are the deep classical cycle-cover/Cayley counting and existence problems warned about in TASK. They received compact source-backed dispositions; no discovery computation is claimed. 376179 is a Baire-typical norm/dense-coloring problem, for which finite graph checks do not encode the quantifiers. Their precise remaining targets appear in `results.json`.

## Provenance, prior art and limits

`raw/` preserves each exact corpus line including its newline. `extracted.json` and each result record include the source chunk, one-based line, full chunk SHA-256, raw-line SHA-256 and statement UTF-8 SHA-256. All advertised versions of the 17 distinct reserved source papers were fetched with non-overwriting HTTP receipts. Follow-up primary bodies and selected public Lean bodies have separate receipts under `http/`. HTTP failures (including mistaken 404 paths) are retained; none is interpreted as novelty evidence. TLS verification remained enabled. No denied route was retried, no browser was opened, and no downloaded code was executed.

Current heads observed:

- OpenAI/math: `4eaee87548250b2682affda7d05d947c05554bae`.
- Omega: `effec9e0fb54096e2f0b2b233fe0a1019df41874`.
- Lean Pool: `01db1d7049cf9668bda1e9e106875ee1278b43e6`.

`outputs/registry-screen.json` records Lean Pool projects/candidates metadata and tree screens, six GitHub repository queries, complete Omega D5/Problems trees and the complete OpenAI preprints tree. The recursive repository-root trees were truncated; the separate subtrees correct only those specified scopes. The OpenAI Lean tree remains truncated. This is a bounded path/metadata screen plus selected body reading, not a semantic audit of every public proof. Citing-work searches were web/title/reference-neighborhood searches; no comprehensive citation database clearance is claimed. The prohibited Crossref, Semantic Scholar, arXiv search API, ScienceDirect and DBLP routes were not used directly.

`outputs/history-screen.json` and `outputs/inherited-evidence.json` retain bounded history matches and inherited document hashes. `outputs/printed-examples.json` indexes source captions/examples for the sustained finite routes. No surviving witness required a complete construction-isomorphism audit. `logs/` retains full numerical outputs and resource receipts. Every search process used the lane resource wrapper: two CPU affinity, 120-second CPU, 140-second wall, sampled 6 GiB RSS guard, 12 GiB address-space limit, and `MALLOC_ARENA_MAX=2`. The RSS sampler does not guarantee transient aggregate process-tree peaks. The CPU-killed SAT receipt has return code -9 and no wall/RSS cap reason; its CPU timeout is not an UNSAT verdict.

No Lean packet is supplied because no new full-scope ordinary proof survived. There was no fake bounded or surrogate endpoint, no accepted-credit claim, no child agent, no git operation, and no background lane job remains.
