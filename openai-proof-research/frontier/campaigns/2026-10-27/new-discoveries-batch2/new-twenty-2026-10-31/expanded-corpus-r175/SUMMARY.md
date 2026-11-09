# expanded-corpus-r175 (Claude lane): summary

**Reservation.** 20 IDs (reserve8, 362785–364884), listed in `reservation.json`.
- Exact literal records are in `raw/<id>.jsonl` and `extracted.json`, with chunk, one-based line, and chunk/raw/statement hashes.
- Per-ID dispositions are in `results.json`.
- Prior campaign notes: none for these IDs. The only `history-matches.txt` hits are numeric coincidences and the launch note.

**Lane rules respected.**
- No Lean, lake, leanchecker, SAT or ILP was run.
- Only capped `python3 -I` ran, under `scripts/cap.sh` (RSS 1.5 GiB, CPU 120 s, wall 140 s), in the foreground, one process at a time. Long sweeps were split into chunks.
- Three runs hit the cap and were killed by it; they left no residue. These were 5×6 Trail Trap, a first slow J=6 DGR attempt, and a first uncapped-budget q=7 path search.
- Nothing was written outside this lane, and no child agents, browser tabs or uploads were used.
- Literature searches were run before every exhaustive computation.

## Candidate: 362785, a full proof of the induced-path conjecture for G_{q,p}

See `CANDIDATE-362785.md` and the draft `lean/InducedPathGqp.lean` (UNCOMPILED, with explicit proof holes).

**Claim.** The source conjecture (Goedgebeur–Jooken–Okrasa–Rzążewski–Schaudt, arXiv:2404.11704v2, Conjecture `con:path`) holds: for every odd q ≥ 3 and every p ≥ 1, G_{q,p} is P_{3q−2}-free. The bound is sharp by the source's Lemma `lowerpath`. Before this, it was known only for q = 3 (Chudnovsky et al.) and q = 5 (the source's computer search). The source proves only P_{3q−1}-freeness for general q.

**Proof outline.**
1. **Linear model.** Translate so that one vertex outside the path is n − 1. Then i < j are adjacent iff j − i = 1 or j − i ≡ −1 (mod q).
2. **Ordering fact (★).** If two vertices have residues s and s + 1 and are non-adjacent, the residue-(s+1) vertex comes later.
3. **Lemma A.** No independent set meets every residue class.
4. **Lemma B.** Path edges at index distance ≥ 3 have different residue classes. This is the source's Claim `cla:one-edge`.
5. **Lemma C.** The edge classes form at most q monotone runs, each of length ≤ 3, with interior runs of odd length.
6. **Case analysis.** Counting deficits always yields an independent transversal when the path has 3q − 2 vertices, contradicting Lemma A.

**Independent checks.**
- The combinatorial step holds for all Lemma-B walks with q ≤ 11. There are 4q − 2 walks at L = 3q − 2, all of which have a transversal; none of the walks at L = 3q − 3 has one.
- An exhaustive search for q = 7 (about 64 M nodes) finds no induced P₁₉ and does find an induced P₁₈.
- The q = 3 and q = 5 maxima are reproduced.

**Credit risk: moderate to high.** The new part is about one page on top of the source's Claims `cla:one-edge` and `clm:ordering`, which fits the "new part under a page" exclusion profile. On the other side, it settles the authors' open conjecture in full scope, and the conjecture is still open in their 2026 v2.

**Lean cost.** About 1.5–3 k lines of uniform-in-q argument, with no large `decide` steps.

**Registry screen.** Clean: Lean Pool HEAD 01db1d70 (unchanged), 8 GitHub queries, Omega live HEAD d9631873 (compare capped at 300 files), OpenAI/math HEAD 4eaee875. Details are in `outputs/registry-screen.json`.

## Zero-credit resolutions found

- **364116** (Prim′–Cayley fixed-point sum): **proved, but routine.** A five-line double count (position symmetry, plus the source identity Prim′ = Cay² with block reversal), checked for n ≤ 7. A citing paper, arXiv:2507.09304, does not state it.
- **364642** (Saikia–Sarma–Sellers): the remaining 8n+4 congruence (mod 2^{2i+4}) **fails exactly at i = 1**: OPT₂(4) = 32 = 2⁵. It holds for i = 2, 3, 4 in range, and 8n+2 and 8n+6 hold too. This is a smallest-parameter endpoint failure (370483 precedent). The 8n+1, 3, 5 cases are proved in the source and 8n+7 in arXiv:2509.17705.
- **363938** (relaxed confusion number): **contradicted by its own source.** The bound is negative for n ≤ 5, and the source's Proposition gives C_r(K_{t,t}, τ_t) = t − 2 > ⌈3n/5 − 4⌉ at n = 6, 8, 10.
- **364120** (total equality for loopless matroids): **resolved in the source** (Chan–Pak Theorem `t:Yan-conj`, including a binary counterexample).
- **363373** (hypergraph bunkbed): **disproved in the source** (Hollom).

## Bounded searches, no counterexample (parked)

- **364883 / 364884** (disjoint Golomb rulers).
  - Regular DGRs exist iff I ≥ 2, 3, 4, 4 for J = 3, 4, 5, 6. For J = 7, I = 5, 6, 7 are regular and I = 4 is not.
  - Regularity is additive, so propagation (364883) holds for all I when J ≤ 6.
  - Extension (364884) holds for (J, I) = (3, 2), (3, 3), (4, 3), (4, 4), (5, 4) and (6, 4), covering 49,484 rulers in total.
- **363028** (Trail Trap grids). The solver was validated against the paper's values. 3×4, 3×6, 3×8, 4×5 and 4×7 are all P2-win; 5×6 was partial (18 opening classes, all P2-win).
- **362816** (derangement representation). The authors' Table 4 (order ≤ 7) was partly reproduced; order 8 is infeasible without numpy within the lane caps.

## Parked as structural, analytic, famous or imprecise

- **Structural:** 362880 (Kohnert finite characterization), 364351 (grid cut complexes; adjacent to 373304), 364626 (odd metamour periods).
- **Heavy machinery:** 363445 (Schubert coefficients).
- **Open, no finite route attempted:** 363809 (the Alon–Grytczuk–Michałek–Lasoń question; refuting it would need a finite backtracking proof).
- **Analytic:** 363910 (FKM), 363994 (β-isoperimetry, β ∈ [1/2, 0.50057)).
- **Asymptotic:** 364355 (matrix-set filling).
- **Famous:** 364471 (Griggs).
- **Imprecise statement:** 364559 (pattern given only by an image).

## Files
- `results.json`: 20 ID-keyed entries, with provenance, receipts, outcome, review depth, summary and computation.
- `CANDIDATE-362785.md` and `lean/InducedPathGqp.lean` (UNCOMPILED).
- `outputs/registry-screen.json`, `outputs/github-search.json`, `outputs/leanpool-keyword-hits.txt`, `outputs/leanpool-files.sha256`, `outputs/fetch-receipts.json`, `outputs/abstracts.txt`.
- `scripts/`: `extract.py`, `fetch.py`, `cap.sh`, `ghsearch.py`, `kw.py`, `untar.py`, `absinfo.py`, `results.py`, `gqp.py`, `lamq.py`, `lamq2.py`, `lamq3.py`, `walkcheck.py`, `trailtrap.py`, `trailtrap_selftest.py`, `dgr.py`, `dgrfast.py`, `dgr6.py`, `dgrreg.py`, `drn.py`, `cay364116.py`, `opt364642.py`, `opt364642b.py`.
- `logs/`: full outputs of every run.
- `sources/`: abstracts, e-prints, extracted TeX, prior-art pages and registry receipts.
