# expanded-corpus-r130 — SUMMARY (Claude investigator lane, 2026-11-03)

Twenty reserved IDs (reservation.json, reserve5 rule). Root decides; nothing here is self-accepted. No Lean, lake, leanchecker or SAT/ILP binary was run. Every computation was a single capped `python3 -I` process run through `scripts/limited.py` (2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB cap, MALLOC_ARENA_MAX=2), strictly one at a time. Nothing was written outside this lane.

## Inherited material (cancelled worker)

`outputs/inherited-hash-verification.json` re-hashes every inherited source against its receipt and every raw line against its corpus chunk, line number and statement hash. There are 0 mismatches. Two fetches had failed earlier (timeouts) and were not retried. Inherited logs and scripts were reused only after the audits described below (e.g. `disk.py` traversal rules; `crystal.py` cross-checked against a fresh implementation).

## Headline

**342364 (Ulas–Żmija Conjecture 6.1, colored binary partitions): CANDIDATE, complete resolution.**

* Proved: nu2(c_{2k}(4n)-c_{2k}(n)) = nu2(n)+2nu2(k)+3 for all k, n.
* Proved: nu2(c_{4k+1}(4n)-c_{4k+1}(n)) >= nu2(n)+3 and nu2(c_{4k+3}(4n)-c_{4k+3}(n)) >= nu2(n)+6 for all k, n.
* The last clause ("in each case the equality holds for infinitely many n") is **false for every k ≡ 3 (mod 4)**. For m = 4k+3 ≡ 15 (mod 16) the valuation is >= nu2(n)+7 for every n. The first case is m = 15, just beyond the authors' verified range m <= 10; for instance c_15(4)-c_15(1) = 48000 = 2^7·375.
* In all other cases the equality clause holds, with explicit infinite equality sets.

The proof is a new generating-function/Chebyshev operator argument with a bit-length 2-adic weight. Details: `outputs/342364-proof.md`; certificate `scripts/certificate_342364.py` → `logs/certificate-342364.log` (ALL_OK). Cross-checks: exact-integer agreement with the product definition, operator identities for m <= 64, a Lemma W stress test, and brute force for m <= 64 with n <= 4096 and for m = 65..128 with n <= 2048 (plus inherited n <= 150000 for m = 11..16). The data also show the sharp constant for m ≡ 3 (mod 4) to be max(6, nu2(m+1)+3); this is observed, not claimed. Lean: `lean-draft-UNCOMPILED/` holds the statement layer and plan only. It contains `sorry` placeholders and is not an endpoint. Novelty: no resolution found (OpenAlex citations, web searches, registries); see the proof file, Section 7.

## Second finding (HOLD)

**352401 (Lecouvey–Lenart–Schultze Conjecture 5.5).** There is a literal counterexample in A_3 with |α| = 5: a broken-diamond edge inside the path e_2^{k_2}(α) that defines φ_2(α). Every such violation lies on a path that later dies, and the paper's A_3 results stay true, so this may be a formulation defect. Independently, the paper's main formula (Theorem 6.6 / Corollary 6.8, conditional on its conjectures) **fails in A_4** for λ = (5,4,4,4,0), µ = (4,4,3,3,3): K = t^4+t^5+t^6+t^7 (Kostka number 4 by SSYT count) against fixed points t^4+2t^5+t^6+t^7. The full model is in Schultze's 2021 thesis, which returned 403. See `outputs/352401-crystal-note.md`.

## All dispositions (details in results.json)

| ID | Outcome |
|---|---|
| 342364 | CANDIDATE: complete resolution; literal conjecture false (sharpness clause, k ≡ 3 mod 4) |
| 352401 | HOLD: literal counterexample, formulation-dependent; source main formula fails in A_4; thesis 403 |
| 346745 | Proved by a routine bridge (source eq. (2),(4) + Gauss + tail pairing); propose exclusion |
| 343330 | Known: Chiu–Marberg, Alg. Combin. 2023, Thm 1.1 |
| 352059 | Known: Đokić–Doroslovački–Bodroža-Pantić arXiv:2212.00317, Thm 1 |
| 350614 | Known: source (parts 2, 4) + Addario-Berry–Donderwinkel Thm 19 (parts 1, 3) |
| 346651 | Known: the source itself (Araújo–Botler–Mota) confirms it |
| 341842 | Parked: m=1 pattern holds for n <= 36, all k; thresholds m-independent for m in {2,3,4,6}, k <= 16 |
| 341843 | Parked: eventual three-parameter statement; diagonal evidence only |
| 341844 | Parked: no violations for moduli 3, 5, 7 in range |
| 345966 | Parked: exhaustive equidistribution verified for n = 10, 11, 12 (72,442,465 objects per side at n = 12; source checked n <= 9) |
| 348761 | Parked: exact DP, all three symmetries hold through 30 nodes (~4.4e20 trees) |
| 345971 | Parked: the source reduces it to the open valley Delta conjecture |
| 345183 | Parked: non-holonomicity, no finite route |
| 346344 | Parked: analytic (metric-graph spectral partitions) |
| 347853 | Parked: analytic PDE |
| 348354 | Parked: needs Seymour decomposition; source proves the graphic/cographic cases |
| 352200 | Parked: famous (Landau constant / Rademacher) |
| 353017 | Parked: limit claim f(r) -> infinity; active author survey (v4, Dec 2025) |
| 355864 | Parked: asymptotic indicator ratio; conjecture added in v2; no counting formula |

## Registries and prior art

* GitHub `/commits/HEAD` receipts (inherited, hash-verified): Omega d5f7c3fd… (2026-11-03T10:55Z), which is newer than root's b576c901, and OpenAI 4eaee875… (unchanged).
* Complete Omega D5/Problems and OpenAI preprint trees were keyword-screened (`outputs/registry-screen-r130-claude.json`). There were no hits on any reserved conjecture. The Ulas-related Omega entries concern other conjectures.
* Prior campaign notes: the ID matches in `outputs/history-id-hits.txt` are numeric coincidences in data files.

## Denied or failed routes (not retried)

Semantic Scholar API 429; arXiv author pages 404; Schultze thesis PDF 403; Schultze research statement 500.

## Remaining lemmas

* 342364: an independent review of proof Sections 3–5, and a formal endpoint (PLAN.md step 3, the power-series operator identity, is the main cost).
* 352401: the thesis definitions, and root's judgement on the intended scope.
