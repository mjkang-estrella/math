# expanded-corpus-r154: summary

Lane: Claude Opus 5.5 investigator, reserve7 IDs (20), 2026-11-04. No candidate is proposed for credit. Nothing here is self-accepted; root decides.

## Outcome in one paragraph

None of the 20 reserved IDs produced a creditable endpoint.

- **Settled in the literature (6 IDs):**
  - 326366: proved by its own source.
  - 326670: refuted by its own source.
  - 327096: refuted for m ≥ 4 by Chan et al., as reported in arXiv:1507.02874.
  - 331057: refuted by the bow-tie graph (Sedlar and Škrekovski).
  - 349215: resolved by Zhang, arXiv:2503.21215 v7.
  - 358921: four of its five congruences were proved by Sellers.
- **Three sustained computational routes, all negative for counterexamples:**
  - **323488 (crossing vectors).** I proved f(2,4) = 8 exactly by an exhaustive, symmetry- and compression-reduced search. This confirms Conjecture 5 at k = 3, w = 4. It is a parameter instance, so it earns no credit.
  - **352002 (fully commutative elements of G(m,m,n)).** The conjecture appears true. The increment is k = n(n−1)·Cat(n−1) for n = 3 to 6. I also found and computationally validated a structural reduction to the affine symmetric group. A full proof would be research-scale and very expensive in Lean.
  - **382404 (8-regular K3-irregular graphs).** Heuristic search reached the authors' own plateau of 2 equal pairs, and no example was found.
- **Remaining IDs:** analytic, asymptotic, deep or flagship problems, with source-backed dispositions.

## Dispositions

| ID | Outcome | Basis |
|---|---|---|
| 323488 | Parked: finite instance verified | f(2,4) = 8 by exhaustive search (see below). No 9-element counterexample exists. |
| 324844 | Parked | Verified through n = 15 by others; m1 proved by Seymour; next cases need ≥ 17-vertex triangulations. |
| 326366 | Excluded: proved by its source | Lai, arXiv:1309.5379, proves exactly this conjecture. |
| 326670 | Excluded: refuted by its source | Zhang–Zhang, arXiv:1311.1987, disprove Ilić–Ilić Conjecture 1.3. |
| 327096 | Excluded: known refutation | Chan et al. counterexample for m ≥ 4, reported in arXiv:1507.02874 (IEEE Trans. IT 2016). |
| 331057 | Excluded: known refutation | The bow-tie graph needs 4 parts (Sedlar–Škrekovski 2021; arXiv:2207.03941 abstract). |
| 335091 | Parked: analytic | Monge–Ampère eigenvalue extremality. |
| 336555 | Parked: continuous | Lagrangian weighted complete intersection. |
| 346692 | Parked | 4 ≤ r ≤ 7 open with asymptotic intent; small-n failures would only be endpoint corrections. |
| 347383 | Parked: deep | Integrality forces d = 6, 22, 46, 78, …; at d = 46/47 both sides are open existence problems. |
| 349215 | Excluded: published resolution | Zhang, arXiv:2503.21215 v7 (2026-09-01): molecules = cells, which is equivalent to irreducibility. |
| 351416 | Parked: finite range verified | All trees with n ≤ 18: the sun / balanced double sun is the unique maximiser. Only trees are covered. |
| 352002 | Parked: strong lead | Linear growth verified, k = n(n−1)·Cat(n−1), mechanism validated; no proof. |
| 358921 | Parked | PD2(25n+5) ≡ 0 (mod 4) holds for all 25n+5 ≤ 3000; a proof needs a 5-dissection. |
| 360916 | Parked: deep | The source proves the weaker n/2 + 1 bound for large n, not the 2(n+1)/5 uniqueness statement. |
| 362724 | Parked: asymptotic | An O-bound; the source settles only a special case. |
| 368119 | Parked: deep | Large-parameter exact Ramsey number. |
| 373687 | Parked: flagship | ISK4-free graphs are 4-colourable; the best known bound is 8. |
| 376131 | Parked: deep | The source covers n = 28 and 32 ≤ n ≤ 10000; open at n = 30 and in general. |
| 382404 | Parked: search negative | MathDB inverts the definition (paraphrase defect); worked from source Conjecture 5.5; no example found. |

## Sustained routes

### 323488: f(2,4) = 8 (Felsner–Krawczyk–Micek, first open case)

**Reduction (rigorous).**
- In a k-crossing-free antichain, closing a gap in one coordinate means lowering every value above the gap by 1. This preserves the sign of every pairwise difference and never increases an absolute difference. So the family stays an antichain and stays k-crossing-free.
- By the source's Proposition 17, each coordinate takes at most k^(w−1) = 8 distinct values. (The heights in the orders <_i give an injection into {1..k}^(w−1).)
- So a 9-element family may be assumed to lie in [0, q_i − 1] in each coordinate, with R + 1 = max q_i ≤ 8 attained on coordinate 1, and coordinate 1 taking every value 0..R.

**Search coverage.**
- Exhaustive branch-and-bound max-clique over {0..4}⁴, with no forcing: the maximum is 8.
- Layered transversal search for every R = 1..7. Each such family contains a transversal (one vector per coordinate-1 value) that forms an (R+1)-clique. The search enumerates all transversals and then looks for the remaining 9 − (R+1) vectors in their common neighbourhood.
- No 9-family exists. Where an 8-family has to exist, the search finds one (sanity check).
- Logs: `outputs/323488-search-logs.txt`. Scripts: `work/323488/clique.py`, `work/323488/layered.py`.

Via the source's Proposition 4, this gives width(M(P)) ≤ 8 for every P in P(3,4), matching the conjectured (k−1)^(w−1).

This is a verification of a parameter instance only, so it earns no credit.

### 352002: fully commutative elements of G(m,m,n) with the affine generating set

**Reproduced and extended.**
- An independent BFS checker over the group, propagating Foata normal forms of commutation classes, reproduces the source's Tables 4 and 5 exactly, including the counts by length.
- Totals a_m:
  - n = 5: 346, 626, 906, 1186, 1466 (m = 2..6).
  - n = 6: 1562, 2822, 4082 (m = 2..4).
  - n = 3 checked up to m = 7; n = 4 up to m = 6.
- The increments k are 12, 60, 280, 1260 for n = 3, 4, 5, 6. These equal n(n−1)·Cat(n−1).

**Mechanism.**
- The affine symmetric group maps onto G(m,m,n), with s_0 mapping to s̃_n. The kernel is the set of translations t_{mβ} with Σβ = 0.
- So g is fully commutative iff its coset has a unique minimal-length element (computed by Shi's length formula) and that element is fully commutative, i.e. 321-avoiding.
- Counting such affine elements reproduces a_m and its length profile exactly for n = 3, 4, 5 and m = 2, 3 (`outputs/352002-affine-check.txt`). That check uses translations with |β_i| ≤ 2, which is evidence, not a proof of sufficiency.

**What a proof would need.**
- The classification of long fully commutative affine permutations (Hanusa–Jones; Biagioli–Jouhet–Nadeau).
- An exact count of the unique-minimality boundary, which in the data grows by n(n−1)·Cat(n−1) per step of m.

This is research-scale work with a very large Lean cost: affine permutations, Shi's length formula and Green's 321-avoidance theorem are not in Mathlib.

**Not verified:** whether the published Discrete Math. 346(12) version still contains Conjecture 4.5 (ScienceDirect is not accessed under the 403 policy).

### 382404: 8-regular K3-irregular graphs

- **Definition defect.** MathDB's wording, "do not all have distinct", inverts the source's definition (Definition 2.2). Read literally, the statement is trivially false (K9 is a counterexample), which is a paraphrase defect with no credit.
- **Search.** Simulated annealing over 8-regular graphs on 17 to 22 vertices, using 2-switch moves and incremental triangle counts. Three objectives:
  - the equal-pair count;
  - the same plus a near-collision penalty;
  - matching the sorted triangle degrees to a target set.
- **Coverage.** About 1.3 × 10⁸ proposed moves in total.
  - Best result: 2 equal pairs at n = 20, the same plateau as the authors' evolutionary search.
  - In every run the triangle degrees stayed within [1, 19].
- A counterexample would be a cheap, decidable Lean certificate, but none was found. A nonexistence proof would need case analysis beyond the source's Theorem 5.2, which this lane cannot do without a solver.

### Other computations

- **351416.** All free trees with n ≤ 18 (counts match OEIS A000055).
  - Randić energy computed by the Coulson integral, validated against Jacobi eigenvalues to about 10⁻⁸. An earlier Durand–Kerner root-finder had about 10⁻³ error on repeated roots and was replaced.
  - The runner-up is always the next-less-balanced double sun. The smallest margin is 0.0025, at n = 18.
- **358921.** PD2 computed exactly from the eta-quotient f4·f6²/(f1·f3·f12) up to index 3000. All five progressions hold mod 4 in that range.

## Conduct and access notes

- **Stopped grep.** An early repository-wide grep for the reserved IDs exceeded the foreground limit and was moved to the background by the harness. I stopped it immediately with TaskStop. The historical check was then redone narrowly: results.json, SUMMARY.md, ledger.json and status.json under frontier/campaigns. That found no prior lane notes for any reserved ID; the only ledger mention is this lane's own launch.
- **Process discipline.** Every other computation ran in the foreground, one process at a time, under `scripts/cap.sh` (CPU 120 s, wall 140 s, RSS watchdog).
- **Not used:** Lean, lake, leanchecker, SAT/ILP solvers, Java, pip and browser tabs.
- **Denied routes:**
  - The GWU ScholarSpace thesis record returned 403. I recorded it and did not retry.
  - ScienceDirect was not attempted.
- **Downloads.** All downloads are in `sources/`, with receipts in `outputs/http.jsonl` (URL, UTC time, status, SHA-256). PDFs were converted with pdftotext; Python always ran with `-I`. TLS verification was never disabled.
- **Provenance.** Exact raw corpus lines are in `sources/<id>.raw.jsonl`. Chunk, line, chunk SHA-256, raw-line SHA-256 and statement SHA-256 are in `results.json`.

## Lean packet

None. No genuine endpoint survived, so no Lean sources are proposed.
