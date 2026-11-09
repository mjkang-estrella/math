# expanded-corpus-r197 (Claude lane): summary

Reservation: 20 IDs (reserve8), from 345116 to 381982; see `reservation.json`.

- Exact raw corpus lines are in `raw/<id>.jsonl`.
- Chunk, one-based line, chunk hash, raw hash and statement hash for each ID are in `extracted.json` and repeated in `results.json`.
- `results.json` has exactly 20 ID-keyed entries, each with its review depth, outcome, disposition, scripts, outputs and receipts.

**Outcome: one candidate, 350973, with HIGH credit risk** (`CANDIDATE-350973.md`, UNCOMPILED Lean draft `lean/BanaianChen350973.lean`). There are 3 known resolutions, and 16 IDs are parked. **No credit is claimed.**

## Lane discipline

- I wrote only inside this lane, ran no Lean, lake or solver binaries, ran no git, started no child agents and opened no browser tabs.
- TLS verification stayed on, and no request was denied (no 403 or 429).
- I used 8 GitHub repository queries, spaced 9 s apart.
- Every computation ran as `python3 -I` under `ulimit -v 2000000; timeout 100`. One run, the n = 9 Dumont chunk, hit the timeout and was abandoned (`logs/n9-a-01-02.time`).
- **Deviation from the brief:** early on, a single tool call extracted the 8 downloaded e-print archives with a shell `for` loop of capped `untar.py` runs. That breaks the one-run-per-call rule. It was harmless (each run took under 1 s and under 15 MB), but I record it. Every later computation was one run per call.
- The history search (`scripts/extract.py`, scoped to `new-discoveries-batch2` prose and results files) found no prior notes on any reserved ID. All hits were numeric coincidences (hashes, RSS values, big integers) or the root's launch note.

## Dispositions

| ID | Outcome | Basis |
|---|---|---|
| 381851 | parked after exhaustive search | Switching checkerboards. The literal fixed-(R,C) statement is defective (vacuous case; "only if" fails at R = C = (1,1,1,1) with the source's Example 2 M), which earns zero credit. The substantive "if" direction holds for all 3×3, 4×4 and 4×5 matrices |
| 381931 | parked (deep, computational) | Antolini–Early (arXiv:2411.07293) proved n = 6, 7, 8; n = 9 needs polyhedral software |
| 381982 | parked (q-series) | CMPP odd conjecture; status from abstracts only (source level 1; KRTW 2404.03851) |
| 349920 | parked (deep) | Fargues–Scholze independence-of-ℓ |
| 350007 | parked (deep structural) | Heroic triples; infinite χ-boundedness |
| 350024 | **known** | Spiro's conjecture: proved by Wang–Zhao (2009.05973) and bijectively by the source (345225 family) |
| 350106 | parked (analytic) | Dirac Faber–Krahn |
| 350481 | **known** | Green–Liebeck Conjecture 2.3, proved by Fang–Li, arXiv:2502.10744 |
| 350580 | parked (meta) | Growable-realizations conjecture for every U |
| 350969 | parked (deep) | Dimer tree algebras; v3 (Aug 2026) is still partial |
| 350973 | **CANDIDATE, high risk** | An explicit quotient dissection with a negative frieze entry; see below |
| 351924 | parked (analytic) | Asymmetric true complexity |
| 353037 | parked (deep) | TR x–y swap; possible later resolution not verified |
| 345116 | parked | Scaffold duality; quantifies over all association schemes |
| 345190 | parked; asymptotic route recorded | McDiarmid Conjecture 3. Sketch: a single class built from Cayley 2-edge-connected pieces of super-sparse sizes. Lean-infeasible |
| 345617 | parked (analytic) | Tree factorization of Lipschitz maps |
| 345654 | parked after extended verification | Dominance verified exactly to n = 8 (source tables go to n = 7). Wilf-equivalence proved Oct 2026 by 2610.01077 and 2610.30975 |
| 345968 | parked (hard finite) | APN automorphism conjecture |
| 346025 | parked (family) | Sibling of the parked 346023 (r161) |
| 346486 | **known** | The reserved source (Lin–Ma–Zhang, 2005.06689) proves the Ma–Ma–Yeh conjecture |

## 350973 (candidate)

Banaian–Chen (arXiv:2106.06679, v1 only), Conjecture 9.5: "The only frieze patterns of Type Λ with negative entries are those which fail the realizability test. In particular, all quotient dissections yield frieze patterns with positive entries."

**Counterexample.** Take the annulus A₄,₃ with four bridging arcs, giving a triangle and three squares. Identify the two outer squares, which share v₀ and v₂ and no edge. This is exactly the move of the source's Example 5.4 (Def. 5.3).

- The quiddity cycle is (1+√2, √2, 2√2, √2), with A = ({3,4},{4},{4,4},{4}).
- It passes the Prop. 4.2 test and is skeletal. The source's own Realization Algorithm classifies it as quotient-realizable.
- It is infinite. The proof uses the Galois conjugate √2 ↦ −√2 and alternating growth of the 4-step progression sequences.
- Its entry m₀,₁₁ = 31 − 22√2 < 0, verified exactly in ℤ[√2]. The monodromy trace is 2√2 − 2, which lies in (−2, 2).

**Searches behind it.** An exhaustive float search of periodic quiddity cycles, plus an explicit quotient-dissection enumeration of 3,732 dissections. The second found 6 negative classes, the smallest being this n = 4 one. The model was validated by reproducing the source's Example 5.4.

**Why the credit risk is high:**

1. The literal first sentence is already contradicted by the source's own example (1+√2, 1, 2, 1+√2), which has a zero and a negative entry at row 5. So the literal refutation is source-internal and earns zero credit.
2. The substantive counterexample, to the quotient clause, is a small modification of the printed Example 5.4.
3. The mechanism is the generic elliptic-monodromy one.
4. The source is a 2021 REU preprint.

I also observed that the proof of the source's Theorem 5.4 fails for ({5},{5},{4,5}). That observation is not used.

**Registry screen.** Lean Pool, GitHub, Omega and OpenAI/math are all clear (`outputs/registry-screen.json`). The 2020 REU slides were not read.

## Coverage details

- **381851.** I enumerated all 1,114,624 matrices across 3×3, 4×4 and 4×5 (`outputs/checker/summary.json`).
  - Of 12,818,863 ordered dominance-comparable pairs (condition (i) is equivalent to 2D prefix-sum dominance), 112 are unreachable, and all 112 fail (ii).
  - The fixed-(R,C) "only if" failures are a formulation artifact: 223 at 4×4 and 34,022 at 4×5.
- **345654.**
  - The enumerator agrees with brute force at n = 4 and with the source tables at n = 7.
  - At n = 8, both sides have 168,503 permutations and the dominance inequalities hold. The cumulative slack is 0, 0, 35, 266, …, 12, 3, 0, 0, 0, 0 (`outputs/dumont/dominance-n8.txt`).

## Files

- `CANDIDATE-350973.md`, `lean/BanaianChen350973.lean` (UNCOMPILED)
- `results.json`, `extracted.json`, `raw/`, `history-matches.txt` (compacted per-file pattern counts)
- `outputs/registry-screen.json`, `outputs/abstracts.txt`, `outputs/fetch-receipts.json`, `outputs/github-search.json`, `outputs/checker/`, `outputs/dumont/`, `outputs/frieze/`
- `scripts/` (all computations), `sources/` (downloaded pages and TeX, each archive extracted into its own `x-*` directory), `logs/`
