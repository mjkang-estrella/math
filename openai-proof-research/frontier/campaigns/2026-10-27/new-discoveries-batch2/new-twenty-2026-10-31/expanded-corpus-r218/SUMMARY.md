# expanded-corpus-r218

No qualifying new solution or literal Lean endpoint was obtained. Discovery credit claimed: **0**. This is a bounded research handback, not completion of the campaign's sixty-solution objective. Exactly 20 reserved ID-keyed dispositions are in results.json.

Six targets are ineligible because of identified prior resolutions:

| MathDB ID | Decisive prior evidence |
|---|---|
| 373825 | Source arXiv:2603.23434, Theorem 5 proves its Conjecture 4. |
| 373932 | Public 2026-09-07 [odd-graph refutation](https://ideosphere.ai/papers/tbsym-graphs), O4=K(7,3). |
| 374225 | Source arXiv:2604.15535, Theorem 2.2 proves its Conjecture 1.3. |
| 374385 | Current Omega repository contains FazekasAbelianSquareEqualityRefutation.lean, refuting the equality clause of the literal conjunction. |
| 374464 | [Alexandersson, arXiv:2607.18746](https://arxiv.org/abs/2607.18746), Theorem 7.2 and Corollary 7.3 prove eventual polynomiality. |
| 374885 | [Jin–Kang–Steffen, arXiv:1502.04561](https://arxiv.org/abs/1502.04561), Theorem 3.5 already includes planar graphs without triangles. |

The other fourteen are parked. In particular, 374731's v1 product conjecture is absent from the retrieved v2 text; this is recorded as a version/scope concern, not as a new refutation or a proved author retraction. The analytic/topological/famous targets 373859, 374480 and 374860 have no feasible finite route here. The factor-loopless restriction in 375053 is a real remaining distinction; printed looped examples do not settle the reserved loopless target.

Completed mathematical checks, none producing a surviving counterexample:

* **374340:** all labeled graphs on 2–6 vertices, all 1044 unlabeled order-7 atlas graphs, and 1000 seeded samples each at orders 8,9,10. Exact majority-color subset partition optimization and every edge deletion.
* **374492:** all unlabeled trees through order 17, exact maximal-matching counts and total sizes, ratio and uniqueness comparisons for eligible diameters. Order 18 stopped at CPU 120 seconds before a completed row; no coverage claim for order 18. Independent edge-subset enumeration agrees with the moment DP on all unlabeled trees through order 9.
* **375027:** all partitions of sizes 1–42 and 30000 seeded larger samples, reaching size 5476. Literal spar labeling and ordinary-partition containment.
* **374894:** connected labeled graphs through order 6; 10000 seeded graph samples at orders 8,10,12,16. Floating-point Rayleigh diagnostics only; no certified spectral upper-bound claim.
* **374103:** all 1023 nonempty triple systems on five labeled vertices, 268 eligible; 20000 seeded six-vertex samples, 6350 eligible sparseness-2 systems. Exact rational gamma computation using source Proposition 5.3.
* **374250:** direct legal-move SG computations for nonregular interior one-piece boards through total board length 22. Corrected characteristic function checked against source equation (2.1). The original games.log used a wrong residue table and is superseded by games-corrected.log; its apparent violations are not findings.
* **374386:** all complement representatives of binary words through length 20 under the literal shared-k effective-partition hypothesis; distinct square factors counted.
* **374204 / 374904:** exact small split-Hamiltonicity and matching-removability checks through the recorded graph ranges, including all order-7 atlas graphs. Mostly known small regimes; no contribution claimed.

ATTEMPTS.md explains the three strongest sustained routes, exact semantics, and missing proof lemmas. CANDIDATE.md states why none is ready for formalization. No partial checker or bounded diagnostic is offered as the reserved theorem.

Provenance and reproducibility:

* raw/ preserves all 20 exact corpus lines, including their newline. extracted.json records chunk hash, one-based line, raw-line hash, and statement hash.
* sources/ contains primary PDF text and the earlier versions for all five multi-version sources. HTTP bodies and receipt files are immutable; http-manifest.json hashes all 155 HTTP/search artifacts.
* logs/source-conjecture-index.json indexes source clauses; logs/printed-inventory.json indexes example/table/figure mentions for active routes. This is not complete visual/cited-construction clearance.
* scripts/ contains extraction, guarded no-retry HTTP retrieval, capped numerical searches, and report generation. logs/ retains full outputs and resource receipts, including failed diagnostic setup runs and the CPU-capped tree run.
* Run scripts with `PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2 python3 -I <absolute lane>/scripts/limited.py <unique log name> python3 -I <absolute lane>/scripts/<script>.py <arguments>`. Use unique log names to preserve previous logs. Search arguments: trees.py 17; partitions.py 42; words_games.py words 20; words_games.py games 22; random_graphs.py majority or spectral. No package installation is required.

Current registry heads checked: OpenAI/math 4eaee87548250b2682affda7d05d947c05554bae; Vilin97/lean-pool 01db1d7049cf9668bda1e9e106875ee1278b43e6; Omega/trureturing de81f09d1b5868b1ef5f62c9c8cab94962481c39. Root recursive OpenAI/Omega tree responses were truncated; complete relevant subtree responses followed. These are path/title screens and targeted positive-content checks, not a corpus-wide semantic absence proof.

OpenAlex returned HTTP 429 on the third source query; subsequent requests to that host were skipped and it was not retried. Denied services specified in TASK.txt were not directly queried. No TLS verification bypass, uploads, external messages, browser tabs, git operations, child agents, shared ledger changes, or Lean dependency/cache changes. Numerical runs were serial under the lane wrapper (2 CPUs, CPU 120 seconds, wall 140 seconds, sampled RSS cap approximately 6 GiB). No process remains running at handback. Lean was not run because no new full ordinary proof survived screening.
