# Expanded corpus r112: investigative handback

One candidate is proposed for review: **MathDB 374241** (arXiv:2604.16188, Conjecture 4.16). It now has a complete proof and a literal Lean endpoint:

> For all a ≥ 3 and b ≥ 4, R_cyc(S_a, P_b^mon) = 1 + (a−1)(b−2).

Credit is zero for all 20 IDs until independent review and root acceptance. No counts, ledgers, shared files or other lanes were changed.

## The candidate: 374241

The lower bound is the source's own Theorem 4.5 (block colouring). The upper bound is new and comes from **Theorem A**:

> If t ≥ 1, b ≥ 4 and N = (t+1)(b−2)+1, every graph on N cyclically ordered vertices in which each vertex has at most t non-neighbours contains a clockwise path on b vertices.

The proof is short:

* The forward and backward jump lengths J and K satisfy J, K ≤ t+1 and J+K ≤ t+2.
* If there is no such path, each greedy path's span is forced to equal its upper bound, so every greedy successor has maximal jump t+1.
* The orbit of u = g(0) then reaches u−1 with a maximal jump, contradicting K(u) = 1.

With t = a−2, colour-1 degree ≤ a−2 is exactly "no colour-1 S_a". SAT data confirm that the extremal minimum degree n − ⌈n/(b−2)⌉ matches Theorem A exactly for b = 4, 5, 6 and n ≤ 13.

* Full write-up: `PROOF-374241.md`.
* Lean packet: `formal/` (`CycDefs`, `CycRot`, `CycLower`, `CycUpper`, `CycMain`, `Audit`). The endpoint is `CycRamsey.cycRamsey_startStar_monPath`. All definitions, both bounds and the minimality of the cyclic Ramsey number (`IsLeast` → `sInf`) are proved.
* `formal/replay.sh` performs a fresh extracted rebuild with `-DwarningAsError=true`. All five modules build (rc 0) and `leanchecker` passes on each (rc 0). Axioms: only `propext`, `Classical.choice`, `Quot.sound`. Keyword scan: clean.
* Mathlib is the pinned prebuilt cache d13f23b7, used read-only and not rebuilt.

Open risks for reviewers:

* Literal fidelity of the Lean definitions (Sym2 colouring, `Fin` rotation, `fromRel` graphs).
* Prior art: only a bounded search for Dirac-type results on convex geometric graphs was done.
* Significance: the proof is short. The upper-bound mechanism is not in the source, which only has the ordered bound 1+(a−1)(b−1).

## Other dispositions (all zero credit)

**Excluded**

* **374618**: refuted in its own source (Remark 2.1, family W_k).
* **374246**: a one-paragraph consequence of the source's Theorem 1.3 plus the Theorem 4.1 block colouring. This is the routine-bridge pattern. Full proof in results.json; its Table 19 lists weaker lower bounds.
* **375112**: the ρ clause is kernel-checked public prior art in Omega (bodies fetched and read at HEAD e51c7d81). The q clause is open. My exhaustive screen of words up to length 28 only corroborates the ρ result.

**Beyond-range searches, no counterexample**

* **375370 (CRIM)**: every partition of size ≤ 85 solved (241,783,707 positions). There is no odd-rank P-position. The source's table goes to size 30.
* **374960 (q-zeta)**: every preorder of size ≤ 8 checked (the source went to ≤ 6). This is a modulo-2^61−1 identity check at one q and is probabilistic. Mutation tests fail as they should.
* **375467 (complete partitions)**: the checker reproduces the source's counts. Beyond the source's range, completeness holds for:
  * {2^6,4} and {2^7,4};
  * {1^8,4} and {1^10,4};
  * {1^8,5}, {1^9,5} and {1^10,5};
  * {2^6,3} and {2^7,3}.

  {2^8,3} hit the cap.
* **374243 (ordered K_a vs alternating path)**: witnesses at f−1 for five cells beyond Table 15 confirm the lower side. At n = f, CaDiCaL returned UNKNOWN after 112 s per cell.

**Parked with a documented gap**

* **374236**: two candidate proof routes were refuted by SAT:
  * the single-cut Erdős–Szekeres lemma;
  * transfer of the Theorem A jump bound, which fails because long red runs exist even at extremal n.
* **374240**: no upper-bound mechanism found.
* **374521**: a reduction to pairs of graphs with integral Laplacian matching roots is recorded; no search beyond n = 9.

**Source-backed parks**

* 373552 and 373739: analytic or numerical targets.
* 374156: Schwartz's colouring cones.
* 374228: the famous square-energy conjecture.
* 374411: affine higher Bruhat computations.
* 374698: plane-digraph normal sets.
* 374792: needs Walnut, and Java is disallowed.
* 374848: infinite tree groups.
* 375347: for m ≥ 7 it contains Stanley's open SCD-existence problem.

## Provenance and limits

* All 20 raw corpus lines are kept byte-exact in `raw/`. `extracted.json` binds the chunk path, one-based line, and the chunk, raw-line and statement SHA-256 hashes.
* All 16 source HTML bodies were fetched (HTTP 200), each with a dated receipt in `sources/`.
* Live registry heads (via /commits/HEAD):
  * OpenAI/math 4eaee87548250b2682affda7d05d947c05554bae, unchanged.
  * Omega e51c7d81cdffe6e70999db34b8a564a99074807b, newer than the root-known 9a49565d.
* Complete untruncated trees were screened (`outputs/registry-screen.json`). Bodies were read only for the Omega half-frequency, CRIM and Fibonacci hits.
* The historical searches by ID, title and source arXiv ID found only false numeric hits and sibling IDs (373550/373551 r68, 374697 r70, 374244 r110).
* No novelty clearance, complete literature audit or corpus-wide review is claimed.

## Resources and process notes

* Heavy computations ran under `scripts/limited.py`: 2 CPUs, 120 s CPU, 140 s wall, sampled RSS 6 GiB, 12 GiB address space. Each run has a log and receipt in `logs/`.
* Limitation: the sampler watches only the direct child, not grandchildren. It is not a cgroup guarantee.
* Some quick validations and exploratory SAT loops (at most 60 s per cadical call) were first run outside the wrapper. The exploratory loops were then rerun under the wrapper with full logs (`logs/mindeg-*`, `logs/cutlemma-*`, `logs/runs-*`).
* One early half-frequency run lost its buffered output when it hit the wall cap. It was rerun with flushing, and that first run gives no evidence either way.
* C code was compiled with the Lean toolchain's `leanc`; CaDiCaL is the Lean toolchain's binary. No packages were installed.
* No Java, git, child agents, browser tabs, publication or external messages were used. Two web searches and public HTTP fetches were made.
* No background process remains.
