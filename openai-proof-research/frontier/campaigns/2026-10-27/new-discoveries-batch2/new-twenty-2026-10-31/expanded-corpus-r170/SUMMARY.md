# expanded-corpus-r170 (Claude lane): summary

Reservation: 20 IDs (reserve7), listed in `reservation.json`. Exact literal records are in `raw/<id>.jsonl` and `extracted.json`, with chunk, line, chunk/raw/statement hashes. Per-ID dispositions are in `results.json`.

**Outcome: no candidate.** No CANDIDATE file is written. No credit is claimed.

Lane restrictions were respected: no Lean, lake, SAT or ILP. Only capped `python3 -I` ran, one process at a time, under `scripts/cap.sh` with an RSS cap of 1.5 GiB, CPU 120 s and wall 140 s.

One shell loop (the 10-vertex sweep for 334658) exceeded the 600 s foreground tool limit. The harness moved it to the background, and it was stopped within a minute with TaskStop. Its results went only to `logs/cyc-10-i.log` in this lane. The harness kept its own task-output file under `/tmp/claude-1000/.../tasks/`, which captured only the loop's final `tail` output, probably empty because it was stopped early. No process is left running.

## Main finding: 358956 (W_2 characterisation) is refuted, but by prior art

- **Reduction.** The conjecture (W_2 ⇔ condition (2)) is equivalent to "(2) ⇒ well-covered". This follows from the source's own Theorem (equivalence for well-covered graphs), since W_2 graphs are well-covered.
- **Reformulation.** Condition (2) is equivalent to: for every maximal independent set M and every v ∈ M, the private-neighbour set P_M(v) is a nonempty clique. A brute-force self-test of this equivalence passed (`scripts/w2_selftest.py`).
- **Search.** I checked all connected graphs on at most 10 vertices, including all 11,716,571 on 10 vertices. W_2 counts for n = 2..10 are 1, 1, 1, 2, 5, 16, 82, 451, 3691.
- **Result.** There is exactly one mismatch, `ICOf~z}~O` = 3K₂ ∨ 2K₂. Its maximal independent sets have sizes 3 and 2, so it is not well-covered and not W_2. Every P_M(v) is the single matching partner of v, so (2) holds.
- **Prior art.** This exact family (an s-matching joined to a t-matching, s ≠ t) is the published refutation in Feghali–Marin, *Three remarks on W₂ graphs*, arXiv:2307.15573 (TCS 2024). **Zero credit.** The lesson: the web prior-art check had to come before the exhaustive search.

## Sustained routes, all parked after bounded exact searches

- **370752 (strong-product infinity, γ_d^p).**
  - The source reduces the question to d < p < 2d.
  - I proved a new local lemma, which earns zero credit as an extension of source machinery: if the maximum p-packing of C_m has size 1, or size 2 with 3d ≤ 2p, then γ_d^p(C_m ⊠ H) = ∞ for every H. The reason is that radius-(p−d) balls carry at most one label.
  - The bitset backtracking search (`scripts/dp*.py`) found no good set in any of:
    - all bad G on at most 8 vertices against all H on at most 9 vertices with no close vertex;
    - bad cycles and bad small G against cycles, McGee, Tutte–Coxeter, Q₄ and a torus, for (2,3), (3,4), (3,5), (4,5), (4,6), (4,7);
    - 929 exact products of 4-regular circulants up to order 26, for (2,3).
  - The surviving regimes (for example (5,7) with C₂₃) would need very large high-girth H. That is not a viable Lean target.
- **371290 (QM-NSD ≤ 4 for G ≠ C₅).**
  - The literal statement fails only for disconnected graphs with a C₅ component. That is a wording defect with zero credit.
  - No connected counterexample in:
    - all connected graphs on at most 8 vertices;
    - 9-vertex graphs with δ ≥ 3, and those with δ = 2 up to index 36824;
    - all 1,249,972 connected 10-vertex graphs with δ ≥ 4;
    - circulants and products built from C₅.
- **334658 (cyclic interval W_c).**
  - Part (i) holds for all triangle-free graphs with Δ ≥ 5 on at most 9 vertices. 10-vertex coverage is partial, with node-cap timeouts.
  - Part (ii) holds for all graphs on at most 6 vertices, and all 7-vertex graphs except 22 dense ones that hit the node cap.
- **324536 (additive colouring, η ≤ χ).**
  - Holds for all connected graphs on at most 8 vertices.
  - Holds for all connected bipartite graphs on 9 and 10 vertices (730 and 4032 graphs, matching the OEIS counts).

## Settled quickly

- **330625:** proved by Short (EJC 2016).
- **329573:** false by prior art. Alon–Kupavskii 2014, Theorem 1.1(2), shows K_{5,5} minus a 2-edge matching is bipartite but needs dimension at least 6. Erdős–Simonovits (1980) and Maehara (1989) gave earlier constructions.
- **330517:** false (Guiduli; also stated in the record itself).

## Parked as famous or hard

- Famous colouring conjectures: 344558, 330309, 328966, 323109, 366150, 324533.
- Open, no finite route: 368238 (multiset 1-2), 333717 (deficiency, still open in 2026).
- Not finite or too vague: 352331 (ZFC set theory), 335703 (geodecity), 333481 (equivalent to Erdős–Hajnal), 331997 (tensegrities).

## Registry screen (`outputs/registry-screen.json`)

- **Lean Pool:** HEAD is 01db1d70 (unchanged). No ID or arXiv hits and no relevant keyword hits.
- **GitHub repository search:** six spaced queries, no relevant repositories.

## Files

- Scripts: `scripts/`
- Logs: `logs/`
- Graph data: `sources/graphdata/`, copied from r165 (McKay data, hashes in `outputs/graphdata.sha256`)
- Sources: abstracts and e-prints in `sources/`, receipts in `outputs/fetch-receipts.json`, parsed abstracts in `outputs/abstracts.txt`
