# expanded-corpus-r223 (Claude lane): SUMMARY

- **Date:** 2026-11-05.
- **Reservation:** 20 IDs, 370758–371619 (reserve8).
- **Statements:** all 20 extracted from the r301 corpus. Exact raw lines are in raw/, and provenance (chunk, line, chunk/raw/statement sha256) is in extracted.json and results.json.
- **Prior campaign notes:** searched by ID and by arXiv ID (outputs/history-campaigns.json). No earlier disposition of any reserved ID was found; only same-source siblings appeared (r67 371571, r80 371136, r148 371492).
- **Restrictions:** no Lean, SAT or ILP was run. All computations were capped python3 -I -B runs in the foreground.
- **Rule deviation:** one tool call chained two capped runs, `starturan.py 4 3 5` and `4 4 5`. Both were small and capped and ran sequentially, never concurrently. It is recorded here for honesty.

## Outcome

**No result in this lane is ready to count.** There is one candidate, with high significance risk: **371607**, a refutation of Venturi's rank-two word conjecture (Semigroup Forum 2026). See CANDIDATE.md.

- A trivial circular counterexample exists: S_3 plus a constant letter.
- A less degenerate binary counterexample exists on 5 states: a = (0 1 2 3)(4), b = [0,2,0,4,0]. It is irreducible, has image sizes {5, 3, 1} only, and comes with an exact rational spanning certificate.
- Root should judge whether this rises above a trivial small-order failure. My own assessment is that it probably does not.

The strongest mathematical find, **371239** (the Gowers U^k uncertainty conjecture fails for k ≥ 6 via f = δ_0 − δ_1 on Z_3), was found independently here. A literature check then showed it was **already published** by Vranesko, arXiv:2609.06531 (2026-09-06). It is excluded.

## Per-ID dispositions (details in results.json)

| ID | Disposition |
|---|---|
| 370758 | Settled. K. Zhang arXiv:2610.01617 (2026) plus LQYZ Theorem 1.2 plus Wang–Zhang (the source) complete the two-case reading. The literal m ≥ 8 residue is a printed-ambiguity issue the source already flags. |
| 370775 | Deep arithmetic (Bremner); disposed. |
| 370778 | Analytic (long-range percolation critical curve); disposed. |
| 371042 | The literal MathDB parameters are exactly source v2 **Theorem 4.14** (proved). The current Conjecture 5.3 appears to follow in one paragraph from H⊗(h_11 H) plus Theorem 4.11(ii): a zero-credit bridge, recorded and not formalized. |
| 371077 | Tree unimodality is still open. The reservation note was inaccurate: log-concavity is what was refuted. Fang et al. 2026 prove it for sufficiently large forests. Famous; disposed. |
| 371098 | Deep structural (Burling control); disposed. |
| 371137 | Famous (Archdeacon 5-OCDC); disposed. |
| 371226 | Deep algebraic (surface dgas); disposed. |
| 371234, 371235 | Bollobás–Scott long cycles: asymptotic universal-constant statements, open; no finite route. |
| 371239 | **Prior art.** Same counterexample published as arXiv:2609.06531. Exact runs: Z_3, Z_5, Z_7 and Z_11 hold for k ≤ 5, with first failures at k = 6 (Z_3), 7 (Z_5) and 8 (Z_11). A floating diagnostic over Z_4, Z_6 and Z_3^2 found no failure for k ≤ 5. |
| 371321 | Three-colour asymmetric Folkman-type existence; deep. The 2026 hypergraph follow-up (Sviridenkov) does not imply it. |
| 371344 | Routine two-line proof: det = p^n, and the number of unit invariant factors equals rank(A mod p) = rank_p(B). Zero credit. |
| 371394 | Follows from Hedetniemi et al. 2025 (EIS-efficiency of the grids G_{n,3} and G_{n,4}), which the source itself cites, together with EISPN ≤ n. Zero credit. |
| 371489, 371490 | Complex dynamics (Ji); disposed. |
| 371570 | **Publicly proved:** Huang–Rao arXiv:2602.01692 (2026) confirm Frankl–Wang Conjecture 7.1 for all n ≥ 2k+1. |
| 371606 | No reducible extremal automaton for n = 3 (alphabets ≤ 3) or n = 4 (binary). Parked. |
| 371607 | **Candidate** (low-significance risk). See CANDIDATE.md. |
| 371619 | Exact hitting-set search: the conjecture holds for (r,s,n) = (4,3,4), (4,3,5), (4,4,5), (4,3,6) and (5,4,5). Larger cases timed out at 100 s. Parked. |

## Coverage records

**Gowers (371239):**
- scripts/gowers_prime.py covers all Σ ⊆ Z_p up to affine symmetry, using Tao's Chebotarev sharpness to reduce the problem.
- scripts/gowers_general.py covers |E| ≤ 4 with 1-dimensional kernels (floating, diagnostic).

**Automata (371607):**
- All binary automata with n = 4: none.
- n = 5 with a a permutation (one per cycle type) and b any map: 16 found.
- Circular binary (a = n-cycle): n = 4..7, none.

**Extremal automata (371606):** n = 3 with alphabets ≤ 3: 54 extremal, all irreducible. n = 4 binary: 48 extremal, all irreducible.

**Star-Turán (371619):** the exact cases listed above.

## Registry screen (outputs/registry-screen.json)

- **Lean Pool:** HEAD 01db1d7049cf9668bda1e9e106875ee1278b43e6 (unchanged from root's value). The full tree of 25038 paths was searched with no relevant hit. projects.yml at that sha returned 404 and was recorded.
- **Cached root Omega/OpenAI listings** (nanostar-parent-final-r1): no relevant hit.
- **GitHub search:** 3 queries, all 0 results.

## Receipts

- All HTTP receipts are in sources/*.receipt.json and sources/registry/.
- arXiv abs/html for the sources, arXiv abs for the prior-art papers, and the Springer page (which redirected to a cookie notice on the same host and returned 200 with the article HTML).
- No 403 or 429 responses were encountered and nothing was retried. The denied routes (Crossref, Semantic Scholar, arXiv API, ScienceDirect, DBLP) were not used.
