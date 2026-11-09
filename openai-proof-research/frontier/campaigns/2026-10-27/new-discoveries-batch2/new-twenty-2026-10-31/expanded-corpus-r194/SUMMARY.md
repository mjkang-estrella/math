# expanded-corpus-r194 (Claude lane): summary

Reservation: 20 IDs (reserve8), from 323194 to 381117, in `reservation.json`. Exact raw corpus lines are in `raw/<id>.jsonl`. Chunk, line, chunk hash, raw hash and statement hash for each ID are in `extracted.json` and are repeated in `results.json`.

**Outcome: no candidate. No CANDIDATE file was written. No credit is claimed.**

Lane rules followed: I wrote only inside this lane. I ran no Lean, lake or solver binaries. Each computation was one capped `python3 -I` process per tool call, under the 2 GB / 100 s wrapper. I ran no git, started no child agents and opened no browser tabs. TLS verification stayed on, and no request was denied (no 403 or 429). The history search (`scripts/extract.py`) was limited to the prose, ledger, review and results files of `new-discoveries-batch2`. It found no prior notes on any reserved ID, apart from the root's launch note and numeric coincidences (`history-matches.txt`). The ledger shows that sibling record 375232 (same source as 375229) was excluded.

## Dispositions (20)

| ID | Outcome | Basis |
|---|---|---|
| 323194 | parked, deep | Separated-graph C*-algebra injectivity conjecture; operator-algebraic, nothing finite to check |
| 323220 | parked, no finite route | Govindarajan Conjecture 3.2 (α–β decomposition). New rows need counts of higher-dimensional partitions far beyond n = 25 |
| 323656 | known refuted | This is Solymosi's Conjecture 2.5 in arXiv:1206.2717; the MathDB title wrongly says "Elekes". Disproved by Murphy, arXiv:1709.10438, Theorem 2 |
| 323845 | parked, deep | Extremal metrics on projective bundles; the source's proof is conditional |
| 323879 | known proved | Aval–D'Adderio–Dukes–Hicks–Le Borgne, arXiv:1301.4803 (JCTA 2014), prove both symmetries |
| 323949 | known proved by source | Balková–Pelantová–Starosta, "Proof of Brlek–Reutenauer conjecture" |
| 324150 | known proved | LaClair–McCullough, arXiv:2601.15403 (J. London Math. Soc. 2026) |
| 324252 | parked after structured search | See below |
| 324673 | parked, deep | Would follow from the Uniformity Conjecture |
| 346734 | known proved | Younsi, arXiv:1209.0824 (EJC 2013); the source also proves it |
| 381117 | known refuted | Evans–Hubička–Nešetřil, arXiv:1801.01165: Hrushovski's graph has no ω-categorical extremely amenable expansion |
| 372920 | parked after exhaustive search | See below (Kohnert-adjacent family) |
| 373454 | parked, deep | Generic holonomy; differential geometry |
| 373969 | parked, deep | GMS sparse counting lemma; the source proves only H = K4 |
| 374530 | parked, deep | Gaussian minima; the source's result is conditional |
| 374917 | parked, deep | Still open in v2; infinite Ramsey problem |
| 374944 | source refuted | Riener–Shapiro v3 (2026-10-21): Conjecture 1.2 fails at (n, k) = (23, 19). MathDB copies v1 |
| 375060 | source refuted | St. Dizier, "Counterexamples to Robichaux's conjecture" (the source itself) |
| 375072 | parked, deep | Galashin Conjecture 11.18, still open in v2 (2026-10-28); a statement about the dimension of moduli spaces |
| 375229 | parked, open and famous | General matroid EF1 conjecture; sibling 375232 excluded; no tractable mechanism |

## Sustained routes

### 324252 (Deng–Tang–Zhang Conjecture 6.1: H(G) ≥ r(G) except for even paths)

- **Source and literature.** I read the whole source. It proves the conjecture for trees and unicyclic graphs, and proves H ≥ r − 31(k−1)/105 in general. Searches found no later proof or refutation. A proof would imply the Caporossi–Hansen conjecture R ≥ r and Fajtlowicz's 1988 conjecture R ≥ r − 1, which is still open. So a proof is out of reach for this pass, and the realistic win was a counterexample.
- **Exhaustive check.** All 995 connected graphs on 2 to 7 vertices (`outputs/harm/direct-n7.txt`). The minimum of H − r over non-even-paths is 0, reached only by C4 and C6. For odd n the minimum is 1/15.
- **Gadget reduction.** I reduced the path-like regime exactly. A long path with gadgets attached (end gadgets, inline gadgets, side gadgets) is a counterexample if and only if the total gadget excess is below 1/6. I checked every rooted gadget and every two-terminal gadget on up to 7 vertices. The minimum excess is 7/30, the source's pendant-near-an-end value. Gadgets with cycles have excess at least 1/3 (`outputs/harm/gadgets-n7.json`, `gadgets-cyclic-n7.json`).
- **Local search.** Simulated annealing on graphs with up to 22 vertices, 2215 restarts. The best graph found is C4, with H − r = 0.
- **Result.** No counterexample, so the conjecture is parked.

### 372920 (Hafner Conjecture 5.2: almost vexillary supports via streamlined bubbling diagrams)

- **Implementation.** I implemented Grothendieck polynomials by isobaric divided differences and checked G_2143 against the known formula. I also implemented the source's Definitions 3.1–3.4: bubbling moves, K-bubbling moves and the SBD weights.
- **Validation.** All 24 permutations in S4 and all 103 vexillary permutations in S5 have a matching A. That is what the source's theorems require, so the implementation behaves correctly.
- **Exhaustive check.** I tested every almost vexillary, non-vexillary permutation in S5 (16), S6 (179) and S7 (1765). Each one already has a matching A with at most one square per column. No state-space cap was hit.
- **S8 sample.** 171 of the 16 545 targets, hash-sampled across all lengths. All pass.
- **Result.** No counterexample, so the conjecture is parked. Outputs are in `outputs/groth/`.

## Registry screen

The Lean Pool HEAD is still 01db1d7049cf9668bda1e9e106875ee1278b43e6. Grepping its tree paths and `projects.yml` found nothing relevant. I ran 6 GitHub repository searches. The only hit is a student project on the Randić index versus radius; it has no Lean code and claims no result. Details are in `outputs/registry-screen.json`. I did not re-fetch Omega or OpenAI/math, because no candidate reached nomination.

## Files

- `results.json`: 20 entries, one per ID, with provenance, review depth, outcome, disposition, receipts and coverage.
- `outputs/fetch-receipts.json`: URL, status, SHA-256, size and UTC time for every download (all saved in `sources/`).
- `outputs/abstracts.txt`: parsed abstracts and version histories for all 20 sources.
- `scripts/`: all code (`extract.py`, `fetch.py`, `abs.py`, `textify.py`, `ghsearch.py`, `leanpool_grep.py`, `harm/*`, `groth/*`, `build_results.py`, `registry_screen.py`).
- `logs/`: extraction log, fetch log and Lean Pool grep log.
