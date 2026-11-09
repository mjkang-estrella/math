# expanded-corpus-r123 (Claude lane): summary

Reservation: 20 IDs between 345739 and 347304 (reserve5 rule; see `reservation.json`).
The per-ID record is in `results.json`, exactly 20 ID-keyed entries built by
`scripts/build_results.py` from `scripts/dispositions.json` and `extracted.json`. Each entry has
its outcome, review depth, versions checked, computation pointers and the literal provenance
(chunk, line, chunk/raw/statement sha256). Nothing here is self-accepted; root decides.

## Headline

**One candidate: 346320, refuted by an explicit 6-vertex counterexample.** The conjecture is
Conjecture 6.2 of Kobeaga, Merino and Lozano (arXiv:2004.14574 v1–v4, Ann. Oper. Res. 305 (2021)).

- The point is y = (1/2, 1, 1, 1, 1, 1) with x_{04} = x_{05} = x_{23} = x_{25} = x_{34} = 1/2,
  x_{12} = x_{13} = x_{45} = 1, and all other x = 0. It lies in P_A^{K_6}.
- Strategy S1S2 can end with 3 vertices:
  S1{4,5} → S1{1,2} → S2{12,3}.
- It can also end with 4 vertices:
  S1{1,2} → S2{12,3}. After that, {4,5} has no S1 witness, because every other vertex has value 1/2.
- Both runs are legitimate executions of the Appendix A.1 pseudocode. The final graphs have
  different numbers of vertices, so they are not isomorphic, and the literal MathDB statement
  (which quantifies over all five strategies) is false.
- Files in `candidates/346320/`:
  - `PROOF.md`: the complete ordinary proof, heap realisability, search record, prior art and caveats;
  - `lean/MathDB346320.lean`: an **UNCOMPILED** literal-endpoint draft
    (`∃ n y x, InPA y x ∧ ¬ ∀ L₁ L₂, Obtained y x L₁ → Obtained y x L₂ → Nonempty (shrunk x L₁ ≃g shrunk x L₂)`).
- Exact independent check: `scripts/verify_346320.py` runs the literal Algorithm S1S2 in
  `Fraction` arithmetic; its output is `outputs/verify-346320.json`.
- Coverage: exhaustive half-integral search through n = 7, including all 52065 labelled inputs
  of the all-value-1 class at n = 7. Random samples with denominators 2–4 on up to 10 vertices.
  Only S1S2 ever fails. C1, C1C2, C1C2C3 and S1 survive; their confluence is open.
- Caveats for root:
  - The conjecture is a heuristic operations-research observation.
  - The later paper by the same group (arXiv:2011.02743v2, lines 475–477) keeps only C1C2 and S1
    and drops S2 as "excessively aggressive", for an unrelated reason. That lowers the practical
    weight of an S1S2 failure.
  - The mechanism (S2 lowers vertex values and kills S1's global witness) may be judged routine.
  - Kobeaga's 2021 thesis was not read.

## Dispositions

| ID | outcome |
|---|---|
| 345739 | known: Ferroni, "Matroids are not Ehrhart positive" (arXiv:2105.04465; abstract confirmed) |
| 345810 | parked: NP-completeness conjecture; the MathDB paraphrase misdefines balanceability; only a 9-regular "simple" case is known (Milanič–Servatius) |
| 345842 | parked: Bonsma–Cereceda O(n³), hard and open |
| 345985 | published proof: Garbe–Král'–Malekshahian–Penaguião (arXiv:2309.10203; abstract only) |
| 346016 | parked: verified by the source for 7 surfaces; going further needs irreducible-triangulation lists |
| 346042 | published proof: Berget–Eur–Spink–Tseng, Corollary 11.5 (arXiv:2103.08021; body read) |
| 346238 | parked: bounded non-finding (exact GJPO search far beyond the source, see below) |
| 346303 | literal formulation defect (fails at t = 0, since ‖x‖₁ → 2 but ‖x − x̄‖₂ → 1); zero credit |
| **346320** | **candidate counterexample (S1S2)** |
| 346342 | parked: metric-graph spectral |
| 346431 | parked: strengthens Stanley's pure O-sequence conjecture |
| 346465 | parked: infinite family; no divisibility among T_j and T_k for j < k ≤ 7 |
| 346589, 346590 | parked: average-case hardness assumptions |
| 346712 | parked: Triangle Conjecture (fine-grained complexity) |
| 346841 | parked: inverse spectral problem |
| 346909 | parked: irreducibility of an infinite family (the source checked even λ₂ ≤ 600 and odd λ₂ ≤ 240) |
| 346949 | parked: reverse mathematics |
| 347301 | source-retracted: Conjecture 11 is only in v1; v2/v3 construct triangle-free pairs with equal chromatic symmetric function |
| 347304 | proved in its source (Liu, arXiv:2007.11055: "We confirm their conjecture") |

## 346238 coverage (bounded non-finding)

- `scripts/gjpo.py` reproduces Example 7 of the source exactly: 128 pairs, 96 inequivalent
  sequences, multiplicity histogram 70/23/1/1/1. It also reproduces all eight printed Example 3
  sequences.
- Exhaustive over every h, every rooted spanning tree and every initial state, with no collision
  and no non-de Bruijn output:
  - m = 1, n ≤ 7; m = 2, n ≤ 8; m = 3, n ≤ 8; m = 4, n = 6–8;
  - m = 5, n = 7: 65536 functions h, 9295360 rooted trees and 59070464 input pairs.
- A reduction of collisions to intervals of the de Bruijn cycle that split few conjugate pairs is
  in `candidates/346238/NOTES.md`; no proof was obtained.

## Registries and prior art

- OpenAI/math HEAD is unchanged at 4eaee87548250b2682affda7d05d947c05554bae (sha-only GET of
  /commits/HEAD at 2026-11-03T08:12Z; receipt `sources2/openai-head-sha.receipt.json`). The first
  full-JSON attempt was truncated (IncompleteRead), and the route was then queried once with the
  sha media type. The cached complete preprint listing (fresh-corpus-r10) shows no relevant path.
- Omega HEAD is now b576c901e75413f0e844a94b3b237ebced23b75b (2026-11-03T07:56Z). Complete
  D5 (13688 paths) and Problems (1689 paths) trees were fetched into `sources2/`. Compared with
  the inherited f2833964 trees, 57 and 12 paths were added. No path matches the 346320 or 346238
  topics. This is a path screen only.
- Web searches are recorded per item in `results.json`. Downloads are in `sources2/` with
  receipts. PDFs are untrusted and were only converted with pdftotext.

## Inherited partial work

- The cancelled Sol worker left `extracted.json`, `raw/`, `sources/`, `outputs/` and `scripts/`.
- All 20 raw-line, statement and chunk hashes were re-verified against the corpus.
- All 64 source receipts were re-verified by sha256 (the one 404 receipt has no file).
- `lean/Shrinking.lean` and `logs/lean*.log` come from that worker's Lean attempts, which never
  compiled. They are superseded by `candidates/346320/lean/MathDB346320.lean`.
- The inherited `scripts/shrink.py` witness (n = 7, values scaled by 2) is consistent with the
  failures found here.
- The inherited `scripts/debruijn.py` used the same transition rule as `gjpo.py` but was never
  validated against Example 7. It is superseded.

## Resource and conduct notes

- Every computation ran under `scripts/cap.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS cap
  2 GiB (observed peaks of tens of MB), address space 4 GiB, MALLOC_ARENA_MAX=2.
  Logs and receipts are in `logs/`.
- Two runs hit the CPU cap: `shrinkx7` and `shrinkx7k0`. Their coverage is not claimed; it was
  redone in chunks.
- **Deviation from the one-at-a-time rule:** while the m = 5 de Bruijn loop ran in the
  background, several short capped jobs ran concurrently with it, so two capped processes ran at
  once. Those were the star simulation, the two-birds checks, two arXiv fetches and a
  `shrink_sample` batch; the batch was stopped when this was noticed. Each process stayed within
  its own cap, and all later work was sequential.
- No Lean, lake, leanchecker, SAT/ILP or Java was run. There were no git operations, no
  shared-ledger edits, no uploads or messages, and no browser tabs. No background job is left
  running.
