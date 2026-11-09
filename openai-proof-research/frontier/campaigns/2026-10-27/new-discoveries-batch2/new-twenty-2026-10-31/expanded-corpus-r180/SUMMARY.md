# Expanded corpus r180

No qualifying discovery is nominated. Exactly 20 ID-keyed dispositions are in `results.json`; all have credit zero. This is a bounded investigation, not a claim that every reserved conjecture is settled or that the literature is exhausted. No Lean endpoint survived the credit screen, and no Lean packet was manufactured.

The primary-source pass exposed substantial routing defects: the layered-number record misdefines g_i; the permanent record swaps row/column language; the Cayley-sum record's conjecture was not located in its cited PDF (including explicit v1); the zero-sum record falsely treats 4-ZSPP as stronger than 3-ZSPP; and the quasi-kernel axiom needs a nonempty-arc restriction to avoid an edgeless endpoint failure. Source scope governed all attempts.

## Dispositions

| IDs | Verdict |
|---|---|
| 349419 | Published exact weighted-cycle theorem, arXiv:2205.15810 Theorem 2 |
| 356347 | Refuted in its own source, Theorem 1.9 |
| 356462 | Excluded credited circulant-nut family; also previously refuted |
| 356476 | Published Jin-Schlosser proof, arXiv:2010.01435 |
| 356748 | Explicit refutation is the classical binary Golay construction; zero credit |
| 356961 | Source main theorem proves the conjecture |
| 357072 | Source Theorem 4.8 proves forbidden-subgraph characterization |
| 357849 | Full ordinary potential argument already follows from a public arbitrary-offset lemma; zero credit |
| 381874 | Alon et al. Theorem 5 proves all fixed-k NP-completeness |
| 355385, 356173, 356349, 356718, 356922 | Parked on precise source, analytic or full-scope gaps |
| 355934, 356749, 365571, 381950, 381984, 382041 | Parked after bounded exact/heuristic searches |

## Actual numerical coverage

* Permanent: all ternary matrices at (m,n)=(2,3),(3,5), modulo independent column signs and column permutation. Respectively 20 and 6188 representatives; 18 and 5807 satisfy expansion. Also 30000 random ternary 4-by-7 matrices, 29872 eligible. No counterexample. No assertion about arbitrary real entries or larger n.
* Quasi-kernel axiom: all labelled oriented nonempty-arc graphs through n=5 (2,26,728,59048 instances), and all loopless nonempty-arc digraphs through n=4 (3,63,4095). Random fixed-outdegree digraphs: 2000 each at n=6,8,12,20,40. Second route: 40000 annealing proposals at each of n=6,8,10,12,16 to minimize the best vertex surplus. No substantive failure. Digons are permitted in the latter loopless-digraph tests.
* Zero sums: all 17 multiplicity patterns 3a+4b+5c=39 for C_2^3 x C_5, with explicit disjoint zero-sum blocks found for every pattern. This implies the finite group's 3-ZSPP by refining every part >=3 into 3,4,5. The group is already in the source's computational base-case neighbourhood; no new general theorem.
* Perfect spanning sets: all nonzero m-subsets in cyclic groups C25 (m=3,s=2: 2024), C63 (m=3,s=3: 37820), C41 (m=4,s=2: 91390). None perfect. Zero cannot be in a perfect spanning set, so this exclusion of zero loses no solutions.
* Inversion: exact BFS computes inversion number for every labelled tournament through n=6 (1,2,8,64,1024,32768 orientations). No vertex-deletion violation. This does not cover all sparse oriented graphs.
* Cycle products: permutation annealing found and independently checked a supermagic C3 square C4 labeling. One million proposals each at C3 square C5, C3 square C7, C4 square C5 reached squared weight error 2. These were heuristic non-findings, not nonexistence certificates. A second exact SAT route found a C3 square C5 labeling in 4.74 seconds. Independent integer verification checked every vertex weight equals 62 and the labels are exactly 1..30. CNF, encoding/model metadata, solver log, and direct certificate are retained; this single finite instance receives no credit.
* Golay diagnostic: 2048 distinct syndromes from all <=3-element subsets of the standard 23 syndrome columns in F_2^11. Correct but classical and uncredited.

All executable numerical processes ran sequentially under `scripts/limited.py`: affinity at most two CPUs, CPU 120 s, wall 140 s, sampled RSS cap 6 GiB, MALLOC_ARENA_MAX=2. Numerical children (including CaDiCaL) were single processes, so sampled process RSS equalled their process-group RSS. No numerical timeout occurred. The watcher is sampled rather than a cgroup hard RSS guarantee. No Lean invocation, package installation, or background job remains. A C++ source was drafted but could not be compiled because g++ is absent; all reported computations use retained isolated Python scripts.

## Prior-art and provenance limits

`raw/` preserves exact newline-terminated corpus lines. `extracted.json` and `results.json` retain the original chunk path, one-based line, chunk SHA-256, raw-line SHA-256 and statement SHA-256. `outputs/fetch-*.json` and other receipt files record actual URLs, UTC fetch times, status and downloaded-byte hashes. Primary PDFs and extracted text are in `sources/`. Downloads were treated as data; no downloaded code was executed. TLS verification stayed enabled.

Inherited ledgers and context were read and frozen, read-only, under `outputs/context-*.json`. ID/title history matches are in `history-matches.txt`; most hits are incidental numeric/hash substrings, not historical research. This is not a global historical clearance.

Live registry heads: Lean Pool `01db1d7049cf9668bda1e9e106875ee1278b43e6`, OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`, Omega `7720ddb8cb36adec857e61a906bbc4c25b2ec6c6`. All were fetched using `/commits/HEAD`. Complete scoped OpenAI preprints and Omega D5/Problems trees were fetched after detecting that root-recursive trees were truncated. Lean Pool projects.yml and all candidates/ files were fetched at its pinned SHA. Eight repository searches were spaced eight seconds apart; all returned zero hits. The exact queries and keyword hits are in `outputs/registry-screen.json`; the eight queries do not individually cover every one of the twenty targets, and no comprehensive proof-body or deleted-history screen is claimed. No novelty clearance is inferred from these bounded non-findings.

The source bodies were read to the depth stated for each ID, not all proof pages in every PDF. Citing literature, technical reports and later versions were checked selectively through the saved searches. Parked records are unresolved. The requested multi-hour depth was not achieved: this pass reports the actual bounded work and its gaps rather than claiming a completed deep investigation. The two concrete proof/refutation routes failed the credit screen before Lean investment.

`CANDIDATE.md` gives the excluded ordinary arguments and explains why no Lean packet is warranted. No shared index, ledger, historical report, dependency or other lane was edited; no git, child agents, browser tabs, author contact, uploads or external messages were used.
