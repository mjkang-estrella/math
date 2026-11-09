# expanded-corpus-r245: summary (Claude resumption, 2026-11-05)

## Resumption inventory

The cancelled Sol run had already produced the following, which I reused unchanged and never overwrote:

- `extracted.json` and `raw/*.jsonl` (exact lines and hashes);
- `history-matches.txt`;
- arXiv abstract pages for all 18 sources;
- PDFs and texts for 1803.00540, 1803.06568 and 1805.00113;
- Lean Pool, Omega and OpenAI/math HEAD receipts;
- the Lean Pool tree, projects.yml and candidates;
- two GitHub searches;
- scripts `fetch.py` and `limited.py`.

My own files are under `claude-scripts/`, `outputs/claude-*/`, `sources/c-*` and `logs/claude-*`. New fetches went through the Sol run's `fetch.py`, which refuses to overwrite a receipt.

## Outcome: 1 candidate (high exclusion risk), 5 excluded, 14 parked

**Candidate: 339077** (Oh–Scrimshaw Conjecture A.3, three-shifted q-Motzkin Hankel determinants). Details are in `CANDIDATE.md`.

- The printed statement is garbled: it inherits f_n from A.2. Its intended clause "n ≡ 2 (mod 3) ⇒ t_n | g_n" is false at n = 5.
- Certificate: the integer 5×5 matrix [M_{i+j+3}(−1)] has determinant 2, but t_5(−1) = 0.
- Exact data through n = 30 show that the clause holds exactly for n ≡ 2 (mod 6) and fails for every n ≡ 5 (mod 6). The other clauses (sign, positivity, the n ≡ 1 formula) hold.
- I fitted a complete closed form for all three residue classes and verified it for n ≤ 27; it is **unproved**.
- Lean cost is tiny; an uncompiled plan is included.
- **Risks:**
  - Root may rule it a first-nontrivial-instance or misprint correction (precedents 371607, 373480).
  - The Discrete Math. journal version could not be checked, because ScienceDirect is denied.
  - The sibling A.2 (339076) was excluded because of Omega's earlier refutation. Omega has no A.3 file at HEAD 1a9b3302.

**Excluded (5):**

- 338655: source withdrawn ("the Conjectures are wrong").
- 338779: proved in its source.
- 338996: refuted in its source.
- 339171: proved in its source (aw(G□H,3) ≤ 4).
- 339142: resolved by Dreier–Mählmann–Siebertz, STOC 2023 (structurally nowhere dense classes ⊇ FO interpretations).

**Parked with exact computation beyond the source range (3):**

- **338739 (AMRZ):** all connected graphs with at most 9 vertices were checked (2,834,835 extensions at n = 9). There are 0 violations; the minimum slack is 2 at n = 8 and 3 at n = 9. Annealing at n = 12 found a minimum slack of 6.
- **338716 (unsplittable cyclic configurations):** an exact search reproduces the authors' Table 1 for n ≤ 30 and was extended to n = 40. The unsplittable classes are exactly the three conjectured families. I used the source's Definition 3, not MathDB's T4 paraphrase.
- **339156 (IPZ unique rectification targets):** all 288 d-complete heaps up to size 11 from star Dynkin diagrams were tested exhaustively, covering 4,565,120 skew tableaux. There were 0 violations; the minuscule control behaves correctly.

**Parked, other (11):**

- 338589: likely a routine bridge from Mühle–Nadeau–Williams Thm 1.3 plus Armstrong's multichain transfer.
- 339078: an uncredited prior lane exists. I added positivity coverage for shifts 4, 6, 8 with n ≤ 18.
- 338652, 338718, 338852, 338951, 338965: deep, with no finite certificate route.
- 338841, 338842, 339107: deep, with follow-up literature.
- 339031: famous.

## Registry and literature screens

See `outputs/registry-screen.json`. Heads checked:

- Lean Pool 01db1d70: no hits.
- Omega 1a9b3302: only the A.2 certificate is relevant.
- OpenAI/math 4eaee875: no hits.
- GitHub repository search: 5 queries in total, all returning 0.

I read source theorem or conjecture bodies for 338589, 338716, 339077/8, 339156 and the Chvátal survey. Every other disposition is abstract-level, and `results.json` says so for each ID.

## Discipline

- Every computation ran as one foreground capped `python3 -I -B` call (at most 61 s).
- No Lean, SAT/ILP, Java, pip, git or child agents.
- Nothing was written outside the lane.
- Deviation: two calls piped or redirected the single process's stdout (`| tail`, `> logs/claude-urt-stars11-0.log`). No second process ran.
- PDFs were read with a lane-local pure-Python extractor (`claude-scripts/minipdf.py`), because no PDF library is installed.
