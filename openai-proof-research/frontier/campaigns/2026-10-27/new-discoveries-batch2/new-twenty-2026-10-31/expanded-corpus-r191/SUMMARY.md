# expanded-corpus-r191 (Claude lane): summary

Reservation: 20 MathDB IDs (327019 to 350219, not contiguous), reserve8 rule. Exact literal statements, raw corpus lines and hashes (chunk, one-based line, chunk/raw/statement SHA-256) are in `extracted.json` and `raw/`. A history search of prior campaign notes by ID and title (`history-matches.txt`) found no earlier disposition of any reserved ID; the only ID hits are the launch note and a hash coincidence.

**Outcome: no candidate.** No CANDIDATE file is written. Accepted count is unchanged.

Lane restrictions were respected: no Lean, lake, leanchecker or SAT/ILP binaries; every computation ran as one `python3 -I` process under `ulimit -v 2000000; timeout 100`; nothing was written outside the lane; no child agents, browser tabs or git.

## Dispositions (detail in `results.json`)

| ID | Outcome | Basis |
|---|---|---|
| 327019 | Source-refuted | The source (Miska, arXiv:1401.1717) proves v_37(a_n) ≤ 1 for 37 ∤ n, and 37 is a Schenker prime. A lane diagnostic confirms this numerically (n ≤ 2800). |
| 327069 | Parked | Proved over RCA0 + IΣ⁰₂ in the source (Cor. 5.11). Plain RCA0 is still open (source Question 5.12). A logic problem with no Lean route. |
| 327142 | Parked | Open (known bounds 4 / 26 / 22). Needs an infinite family of groups. |
| 327206 | Parked | Analytic spectral Turán problem. |
| 327299 | Parked | Source finds S-crucial permutations at n = 17 and 21, none at 18–20 or 22. Arbitrarily-long existence needs an infinite construction. |
| 327364 | Parked | Still open for even p in source v8 (April 2026). Only odd p is proved there. Research-level. |
| 327443 | Known | Disproved by Adiprasito–Padrol (Israel J. Math. 2016), with d = 5 counterexamples. |
| 330334, 330335 | Parked | Deep classification conjectures. Both are still present in v4 (Adv. Appl. Math. 2017). |
| 330501 | Parked | Deep (annular Khovanov). |
| 330528 | Parked | Asymptotic Frankl–Rödl variant. |
| **330821** | Parked after sustained search | Open (Wang–Wu, AJC 2020). See route 1 below. |
| **330961** | Parked after bounded exhaustive tests | See route 2 below. |
| 330962 | Source-refuted | The source labels it "(false)" (C5, Figure 8). The lane solver reproduces Figure 8(a). |
| **330963** | Parked after bounded exhaustive tests | See route 2 below. |
| 331147 | Known | Solved by Hernández Martínez–Peterin (Commun. Comb. Optim. 2026). Only the abstract was read. |
| 331434 | Parked | Asymptotic chain-partition problem (Füredi family). |
| 331440 | Parked | Infinitary DC-set question. |
| 331551 | Source-refuted as printed | PSL₂(7) has no cubic GRR (source theorem). |
| 350219 | Known (claimed) | Rukavicka, arXiv:2410.12714 (2024), claims a proof of the FPZ conjecture. |

## Route 1: Bang-Jensen–Gutin–Li Conjecture 6.1 (330821)

The original 1996 paper was read (Sections 5 and 6, including the 2n − 2 sharpness example).

Status:
- Conjecture 1.3 (the reserved one) is open as of AJC 2020.
- The stronger Conjecture 1.4 was disproved by Wang–Chang–Wu (Discrete Math. 2020).
- The Bang-Jensen–Guo–Yeo 5n/2 − 4 theorem settles n ≤ 6. So a counterexample needs n ≥ 7, and at n = 7 it needs a constrained pair with degree sum exactly 13.

Search (`scripts/bjgl_sa.py`):
- Simulated annealing over strong non-Hamiltonian digraphs, using an exact subset-DP Hamiltonicity test.
- Objective: total deficit below 2n − 1 over non-adjacent dominating or dominated pairs.
- Seeds: random digraphs, and non-1-tough digraphs (deleting a cut set S leaves |S| + 1 complete components).
- Runs at n = 6, 7, 8, 9, 10 (about 7.6M, 4.8M, 1.4M and 0.33M steps at n = 7, 8, 9, 10). The best deficit was always 1, which is exactly the printed sharpness level.

Calibration:
- In "dominated only" mode, the same code finds counterexamples to the disproved Conjecture 1.4 within seconds (966 labelled examples at n = 6, 5 at n = 8).
- One of them was confirmed by an independent permutation brute-force checker (`scripts/bjgl_verify.py`).

This is heuristic, bounded evidence, not exhaustive coverage. A counterexample would have been an ideal Lean certificate, but none exists in the searched regime.

## Route 2: Cranston–Rabern fixability (330961, 330963)

The source's Definition 1 (fixability), superabundance and Section 5 algorithm were read. I implemented an independent bottom-up fixpoint solver (`scripts/fix.py`). States are quotiented by colour permutation: a state is the multiset of colour-membership vectors. Pot P = [k] is used, which is enough because fixability is monotone in P.

Validation:
- It reproduces Figure 8(a): C5 is superabundant and not fixable (closure of 23,846 canonical states).
- It reproduces Theorem 2.5: stars with superabundant lists are always fixable.
- The Lemma 2.2 counter (fixable but not superabundant) is 0 in every run.

Results:
- **Conjecture 4.1 (330961):** every tested profile inside its hypothesis is fixable. Tested: P5 (7 profiles, k = 7), P6 (5 profiles, k = 6, up to 41,280 states, game heights up to 12) and the 7-vertex spider S(2,2,2) (2 profiles, k = 6, up to 53,616 states).
- **Conjecture 4.3 (330963):** tested on the star with one edge subdivided, D = 3 (22 profile runs at k = 7 and 10) and D = 4 (3 profiles at k = 6). Every superabundant non-fixable assignment has |L(r)| = d(r), |L(s)| = d(s) and ψ_L(G) = ‖G‖ exactly. So no violation of (a), (b) or (c) occurs, and the (c) threshold is tight in the tested range.
- These are bounded findings only (pots limited to k colours).

## Registry screen

`outputs/registry-screen.json`:
- Lean Pool HEAD is 01db1d7049cf9668bda1e9e106875ee1278b43e6 (unchanged). The tree and projects.yml were grepped and gave no relevant hits.
- 8 spaced GitHub repository queries all returned 0 results, with no 403 or 429.
- Omega and OpenAI/math were not re-fetched, because no candidate reached the investment stage.

## Files

- `extracted.json`, `raw/`: literal statements and provenance.
- `results.json`: exactly 20 ID-keyed entries.
- `outputs/fetch-receipts.json`: dated URL, status and SHA-256 receipts.
- `sources/`, `sources/txt/`: downloaded primary sources.
- `scripts/`: all scripts (extract, fetch, abs, bjgl_sa, bjgl_verify, fix, schenker, build_results, registry_screen, ghsearch, leanpool_grep).
- `outputs/*.json`: full computation outputs.
- `logs/`: extraction and Lean Pool grep logs.
