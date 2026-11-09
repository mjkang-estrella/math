# expanded-corpus-r160: summary (Claude Opus 5.5 investigator lane, 2026-11-04)

Reservation: 20 reserve7 IDs (`reservation.json`). All 20 have ID-keyed entries in `results.json`. Each entry records:
- the raw chunk and line, and the raw, chunk and statement sha256;
- the current arXiv version and journal reference;
- the review depth;
- the outcome, the computations and the remaining lemmas.

**Nothing is self-accepted; root decides.** The lane rules were followed:
- no child agents, no git, no Lean, no SAT/ILP binaries;
- python3 -I only, one capped process at a time (`scripts/cap.sh`: CPU 120 s, wall 140 s, RSS cap);
- all writes inside this lane.

## Main result: one candidate, 353800 (see `CANDIDATE-353800.md`)

**Naslund's function-field Sárközy tightness conjecture is false.** Source: arXiv:2203.01293v3, Q. J. Math. 2022, Conjecture 13. The conjecture says that for k = 2 and q odd, Theorem 1 is tight, i.e. the maximum is q^{3n/4}.

**Literal finite witness.** There is a set A ⊂ P_{5,4} of 160 polynomials with no difference equal to a square, while the conjecture caps such sets at 5³ = 125.
- A = {c0 + c1T + c2T² + c3T³ : (c0, c1, c2) ∈ X, c3 ∈ F_5}.
- X is the 20 solutions of 4c0c2 − c1² = 2, together with the 12 points t(a², 2ab, b²) for t ∈ {1, 4}.
- It was verified by two independent scripts. The full-polynomial verifier tests all b of degree ≤ 3.

**Uniform disproof (ordinary proof, §§3–4 of the dossier).** For every prime power q ≡ 1 (mod 4) and every n ≡ 0 (mod 4), there is a square-difference-free A ⊆ P_{q,n} with |A| = q^{3n/4}(1 + 1/q + 2/q²).
- Key fact: the level set {4xz − y² = nonsquare} is independent in the "square-type isotropic cone" Cayley graph, because its tangent planes are anisotropic.
- It is extended to all n by a middle-window version of Naslund's own extreme-coefficient argument (his Theorem 10).
- Machine checks of the construction: q = 5, 13, 17, 29, 37, 41, plus the complete q = 5, n = 8 instance. There were 0 violations.

**Further evidence.**
- q = 3 also fails for every n ≡ 0 (mod 4) with n ≥ 8, via a computational slice (297 > 243).
- For q ≡ 3 (mod 4) and n = 4 the bound is exactly right (Hoffman).

**Limits.**
- The improvement is a constant factor, so the exponent 3/4 is not improved.
- The k ≥ 3 cases searched did not violate the bound (k = 3: q = 4 exact, q = 7 searched; k = 4: q = 5 searched).

**Lean.** `lean/MathDB353800.lean` is **UNCOMPILED**.
- Endpoint: `¬ Conjecture`, the literal statement over all finite fields and all admissible k and n.
- Witness: q = 5, k = 2, n = 4.
- Proof path: the square b² of degree ≤ 3 forces natDegree b ≤ 1, then a coefficient comparison, then a kernel `decide` over 32·32·25 cases.
- Mathlib names were checked against the pinned cache. Expected axioms: propext, Classical.choice, Quot.sound.

**Prior-art screen.**
- Source v1–v3 checked; v3 is post-refereeing.
- Green 2017 read. He cites Link's unpublished 2008 examples of size 5^{3n/2} = N^{3/4}, which equals the bound rather than beating it.
- Li–Sauermann 2212.12754, 2609.12499, 2510.27573 and 2510.27581: none addresses the question.
- arXiv searches.
- OpenAI/math at HEAD 4eaee875 (unchanged): only an integer square-difference preprint, with no function-field content.
- Omega at **new HEAD b52262a0** (2026-11-04T12:05:53Z): complete D5 (13929) and Problems (1720) trees, untruncated, with no relevant path. This was a path screen only.
- Residual unread items: Lê–Liu (Acta Arith. 2013, not on arXiv); Link 2008; association-scheme literature on symmetric bilinear forms.

## Dispositions of all 20 IDs

| ID | Outcome | One-line reason |
|---|---|---|
| 353800 | **CANDIDATE** | Explicit 160 > 125 refutation, plus a uniform disproof for all q ≡ 1 (mod 4) and all n ≡ 0 (mod 4) (above) |
| 354578 | zero credit: source-internal | The source's own Table 1 formula for K_{p,q} gives 2 positive path eigenvalues once q > (p²+p−1)/(p−1) (e.g. K_{2,6}). Census of n ≤ 7: the minimal 2-connected counterexamples are K_{1,1,5} and FQjVo |
| 354500 | zero credit: defective | No edge of the proposed matching graph reaches a diagonal pair (τ,τ), so every Stanley equality case (e.g. the 3-antichain) violates Hall's condition. All posets n ≤ 5 tested: failures in 3/6, 86/118, 1999/2281 instances |
| 382075 | known | Zhu, arXiv:2307.08121 (Annals of Combinatorics 2024), Theorem 1.5 at k = 2. My FS computations agree (n ≤ 8 complete; 288 qualifying graphs at n = 9) |
| 353553 | source-resolved | Fang's source proves the Zeilberger–Reed conjecture (bijection) |
| 353973 | source-resolved (negative) | Bickle's source constructs maximal planar graphs with no spanning 2-tree; the MathDB "conjecture" is refuted in its own source |
| 357777 | source-resolved | Xu–Li–Zhou confirm the Shi–Shan conjecture |
| 382216 | parked, verified small | Z_q(K_{n,m} □ K_2) conjecture: an exact minimax solver confirms it for all n + m ≤ 10. Remaining: an oracle strategy for Z_1 ≥ n+m and Z_+ ≥ 2min(n,m). No later resolution (Abiad–Moghaddas 2509.03967 checked). The Lean game semantics would be heavy |
| 354435 | parked, attribution defect | The source misquotes KKP: the original conjecture is "for large enough r". No twin-free 3-uniform counterexample: exhaustive ≤ 6 vertices (all 2^20 labelled edge sets at n = 6; twin-free tested: n = 6 1,045,380, n = 5 918, n = 4 5), random n ≤ 9, and 842k random regular graphs up to 18 vertices |
| 355218 | parked | Reduces to connected G. Prior lane probe: connected n ≤ 8, no counterexample. Edge-replacement proof gives domination but not connectivity |
| 353989 | parked | Only all-same-parity, non-Hamiltonian-pair three-cycle products remain open (smallest C3□C5□C7, 105 vertices). A refutation needs a nonexistence certificate |
| 361080 | parked | The source handles k = 3 and the δ = k critical case. Open: (k+1)-critical graphs with δ ≥ k+1, k ≥ 4 |
| 353486, 354575, 354661, 355102, 357115 | parked (structural) | No finite-certificate mechanism identified; source statements read |
| 354851, 355576 | parked (asymptotic/analytic) | Polynomial-bound and commonness statements, out of reserve7 scope |
| 354875 | parked (geometric) | Strengthened thrackle conjecture |

## Coverage records (exact)

- **382216:** n,m ≥ 2 with n+m ≤ 10, all pairs, q ∈ {0,1} (q = 2 for n+m ≤ 9). Logs: `outputs/qzf-run1..4.log`. Solver validated against the source's K_{n,m} and book-graph values.
- **382075:** every connected bipartite Y without a non-trivial cut edge, Y ≠ C_n:
  - n = 5–7: 40 graphs;
  - n = 8: 120 graphs;
  - n = 9: graph9c lines 0–12339, 288 graphs.
  - All give exactly 2 components. Logs: `outputs/fs-*.log`.
- **354578:** all connected graphs n = 3–7 (McKay lists copied from lane r88, hashes in `sources/graphdata/*.receipt.json`). Exact integer characteristic polynomial (Berkowitz) plus Descartes' rule. Log: `outputs/pathmatrix-n3-7.log`.
- **354500:** all naturally labelled posets n = 3, 4, 5 (7, 40, 357).
- **354435:** see the table row. Logs: `outputs/hyper12-*.log`.
- **353800:** see the dossier §8.

## Receipts

`outputs/fetch-receipts.json` holds every HTTP fetch: URL, status, sha256, bytes and UTC. All fetches were arXiv abs, e-print and search pages, the GitHub API, or raw.githubusercontent. There was one 404 from a wrong OpenAI path, which was then fetched correctly.

Downloaded archives were unpacked with `tarfile` `filter='data'` into fresh directories under `sources/eprint/`.
