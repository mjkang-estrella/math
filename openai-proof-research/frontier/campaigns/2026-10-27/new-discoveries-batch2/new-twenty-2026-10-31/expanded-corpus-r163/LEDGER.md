# Per-ID ledger, expanded-corpus-r163

Exactly 20 reserved IDs. Provenance (chunk, one-based line, chunk/raw/statement SHA-256) is in `results.json` and `extracted.json`; raw lines are in `raw/<id>.jsonl`. Registry screen: `outputs/registry-screen.json`.

| MathDB | Title | Outcome | Verdict (short) |
| --- | --- | --- | --- |
| 335383 | Dual-acyclic orientation conjecture for positive-genus triangulations | PARK_hard_structural | Existence of a dual-acyclic 3-orientation on every positive-genus triangulation; structural topological conjecture, no small finite route; parked. |
| 336139 | The permanent-non-singular $(0,k)$-matrix conjecture | PARK_hard_structural | Existence of a uniform constant k for permanent-non-singular (0,k)-matrices (weaker than the (0,2) claim); 1-2-3-type weighting conjecture; parked. |
| 336449 | Yan and Martinez–Savage's enumeration conjecture for restricted inversion sequences | EXCLUDE_source_proved | The source (Z. Lin, Restricted inversion sequences and enhanced 3-noncrossing partitions) proves the Yan / Martinez-Savage conjecture; the MathDB note itself says the paper's purpose is this enumeration. Known. |
| 336565 | The 3-design conjecture for the trace-cubic design | CANDIDATE_full_scope_proof | Ordinary proof complete for the full conjectured scope. Odd-m half is a routine Assmus-Mattson/Kasami bridge; m = 2 mod 4 is the substantive part. Credit risk: moderate-high (short elementary argument). Lean: medium-high cost, draft lean/LiuDing3Design.lean UNCOMPILED with explicit sorry obligations. |
| 336566 | The odd-dimensional weight-enumerator conjecture for the design code | EXCLUDE_routine | Follows from classical BCH/Kasami theory plus a two-line span argument: zero credit (routine/known). |
| 336741 | Wendland's five-list conjecture for facial unique-maximum coloring | PARK_hard | List FUM-colouring of all plane graphs with lists of size 5; a counterexample search needs plane-graph generation and list-assignment search beyond this lane; parked. |
| 337060 | The edge-transitive 3-circulant modular-product conjecture | PARK_verified_no_counterexample | Conjecture appears true; a proof would be a case analysis of a deep external classification (Kovacs-Li), likely judged a classical-theorem bridge and infeasible in Lean. Parked. |
| 338345 | Plex-existence conjecture for Latin squares | PARK_flagship_implies_Ryser | Conjecture 13 (k-plexes for all k in N(n) = {1..n} for odd n) contains Ryser's conjecture (k=1) and Wanless survey Conjecture 8.5; famous open; short disposition only. |
| 339233 | The join-graph characterization of local antimagic chromatic number | PARK_family_warning | Parked: any counterexample would most likely be a parameter-variant three-weight obstruction (FAMILY WARNING); no genuinely different mechanism found. Source theorems (C_m v O_n, C_2m v O_2n, M_6 v O_2n) all consistent with the conjecture. No lower-bound exhaustive search run (labelling search too large in pure python). |
| 339234 | The complete-join characterization of local antimagic chromatic number | PARK_family_warning | Parked under the family warning; no candidate. |
| 339445 | Adjacent-swap connectivity conjecture for binary tropical matrix identities | PARK_search_budget | Parked; best tractable next step: implement Minmax-based ~_2 classes (Algorithm 8) and exact 4D hull tests, search lengths 23-28. |
| 339995 | Maximal-consumer existence conjecture for partition consumption | EXCLUDE_source_bridge | Conjecture 8.12 follows in two lines from the source's own Theorem 5.4 proof: zero credit. |
| 340115 | Equivalent quasi-transversal conjecture for Latin squares | PARK_flagship_equiv_Brualdi_Stein | Equivalent (by the source) to the Brualdi-Stein near-transversal conjecture; Montgomery (2023) proved it for all large n, small/intermediate n open; flagship, short disposition. |
| 340262 | Generalized 2-colour conjecture for planar digraphs of prescribed digirth | PARK_flagship | g = 3 case is the Neumann-Lara 2-colour conjecture for planar digraphs (famous open); short disposition. |
| 340616 | The sparse simplicial-complex index conjecture | PARK_asymptotic | Existence of a constant c > 1 (exponential-deficit regime); no finite certificate; parked. |
| 340618 | Samotij–Sudakov's Kleitman analog for projective cubes in b\mathbb{Z}_{2^n}d | PARK_verified_no_counterexample | No counterexample; conjecture consistent. Parked (exhaustive n=5 needs 2^32 subsets; a branch-and-bound would be the next step). |
| 341388 | The AMRZ line-and-bridge conjecture for graphs without pendant edges | PARK_not_finitely_refutable | "except for finitely many cases" cannot be refuted by any finite example; refutation needs an infinite family; parked. |
| 349834 | Diameter formula for generalized Petersen graphs | EXCLUDE_source_withdrawn_and_boundary | Source arXiv:2102.10397 withdrawn in v2 by the authors (349435 precedent: withdrawn = retracted). The only failures are the Petersen graph and GP(7,2)/GP(7,3) at the n >= 5 boundary (371911 precedent: classical-boundary correction). Zero credit. |
| 367578 | Unique maximality conjecture for matroids avoiding dual symmetric-tensor circuits | PARK_hard_structural | Unique maximality of X-matroids on K_n (rigidity/symmetric tensor matroids); no small exact route in pure python; parked. |
| 382445 | Henning–Oellermann–Swart conjecture on the Steiner k-diameter and Steiner k-radius | EXCLUDE_known_resolution | HOS conjecture settled in the literature (holds for k=3,4 by HOS, k=5 by Reiswig, false for k>=6 by Reiswig tightness). Zero credit. |

## Coverage of finite searches

- 349834: BFS diameters for all 5 ≤ n ≤ 330 and all s; failures only at n = 5 and n = 7.
- 337060: all C_n(1,a,b), 7 ≤ n ≤ 145, every (a,b), with an exact automorphism search for arc-transitivity; 0 violations.
- 340618: exhaustive n = 3, 4 (all 2^8 and 2^16 subsets); local search n = 5, M = 17..28.
- 336565: Walsh-criterion check m = 3..14 except m = 12 (m = 4, 8 are controls); proof steps audited m = 3..10.
- 339445, 339233, 339234: no search run (see verdicts); 338345, 340115, 340262, 340616, 341388, 335383, 336139, 336741, 367578: source-backed short dispositions.
