# expanded-corpus-r227 (Claude lane): summary

**Outcome: no candidate. 0 new solutions; campaign count unchanged.** All 20 reserved records have
dispositions in `results.json`, with exact corpus provenance: chunk path, one-based line, chunk, raw-line and
statement hashes, and raw lines kept byte-exact in `raw/`.

## Dispositions

| ID | Short title | Outcome |
|---|---|---|
| 364179 | Spouse-loving Oberwolfach OP⁺(4m;m) | Excluded: published follow-up constructs all odd m ≥ 5 |
| 364256 | Biased (m,1) edge-colouring game | Parked: needs a uniform witness family for every non-exceptional pair; Lean cost of game proofs very high |
| 364405 | Induced cycles, CD(0,∞) triangle-free | Parked: ill-posed ("several graphs" left unspecified) |
| 364454 | Invariant graph, expanding Thurston maps | Parked: deep dynamics |
| 364481 | pre₂ injectivity | Excluded: already proved (Li, arXiv:2508.00971). This lane found an independent short proof first |
| 364512 | Lasso functoriality | Parked: categorical, no finite route |
| 364624 | Frankl, one pendant vertex | Excluded: the source proves it equivalent to union-closed (v1 Prop. 3.16); removed in v6; family of r216 |
| 364715 | k-general d-position NP-completeness | Excluded: routine bridge (k = 3 is Klavžar–Rall–Yero; NP membership by a geodesic DP) |
| 364748 | NIEP boundary extremality | Parked: deep geometric |
| 364839 | Castelnuovo triplets (Hibi et al.) | Parked after a validated exact random search; Lean cost (volume) high |
| 364872 | Isolation game 3/7 | Parked: same conjecture as 369233 (r222); not repeated |
| 364900 | Skew Loebl–Komlós–Sós | Parked: deep extremal |
| 364925 | Matching divisors (Langlands) | Parked: deep |
| 365072 | Su–Liu Ramsey-full equivalence | Excluded: refuted in its own source |
| 365080 | CFKS hypergraph surplus | Parked: asymptotic |
| 365097 | Additive complexity is regular | Parked: contains the open abelian-complexity conjecture |
| 365116 | LHS module support | Parked: superseded by v4's complete 230-group computation |
| 365134 | Non-conflicting flows, Hamiltonian path | Parked after sustained structured search (below) |
| 365197 | Linear small eigenvalues | Excluded: proved in source v2, Theorem 1.3 |
| 365505 | Finitary matroid hindrance | Parked: deep, infinite structures |

## Sustained route 1: 365134 (Mkrtchyan, Conjecture 8)

Exact reformulation:

- A non-conflicting flow with respect to F is a labelling of the F-edges by a, b, g = a+b.
- On each F̄-cycle, #a + #g and #b + #g are both even.
- No F̄-edge joins an a-label to a b-label.

3-edge-colourable graphs are trivial, so only snarks matter.

Checker validation:

- P10 has no flow.
- The source's Theorem 5 graph (34 vertices, all 96 perfect matchings) has no flow.
- Witnesses for five named snarks pass an independent Z₂×Z₂ verifier.

**Coverage.**

- **All Hamiltonian-path cubic multigraphs on n ≤ 14** (labelled completions: 2,205, 29,295 and 446,985). The only failures are the two labelled Petersen copies at n = 10. For simple graphs on n = 16, only 1/32 of the space was run (81,722 completions).

  This range adds nothing beyond the source: a probe shows every bridgeless Hamiltonian-path cubic multigraph with n ≤ 12, and every simple one with n = 14, has a 2-factor with ≤ 2 cycles. The source's Theorem 4 already covers such graphs.
- **Beyond Theorem 4.** A P10−e block with both cut edges in F always conflicts. Otherwise it acts as a "twisted" F̄-edge that forbids equal non-g end labels. P10−e and P10−v blocks cannot be traversed by a Hamiltonian path, so at most two can occur.

  Tested: every bridgeless Hamiltonian-path base multigraph on m ≤ 10 vertices with its two ends replaced by Petersen blocks:
  - e–e: 8,008 graphs;
  - v–v: 2,300 graphs;
  - v–e: 4,204 graphs.

  Every 2-factor of these graphs has ≥ 3 cycles, and every graph admits a flow.
- **Petersen-derived snarks:** 308 triangle/digon expansions, Blanuša-type dot products, 2-sums, J5 and J7 all admit flows.

**Remaining gap:** a proof for graphs whose 2-factors all have ≥ 3 cycles, or a forcing mechanism that uses at most two rigid blocks.

## Route 2: 364481

The lane derived a complete short proof via the doubling identity φ(2t) difference = (φ(t) difference)(φ(t) sum) and a growth argument. A literature search before any Lean investment then found that Li (arXiv:2508.00971) had already proved it. Excluded.

## Route 3: 364839

- The h*-form of the conjecture: h ≤ (c+1)(d+1) for c ≥ 2.
- Prism analysis shows the printed Q(c) is the only prism of that kind attaining the bound.
- About 214,000 random lattice 3-polytopes, with the checker validated on every printed example. For c = 1, b reaches 34. For c ≥ 2, b ≤ 11. No violation.

## Prior art and registry screen

- Lean Pool HEAD `01db1d70…` (unchanged; full tree of 25,038 paths screened).
- OpenAI/math HEAD `4eaee875…` (unchanged; cached preprint listing screened).
- Omega HEAD is now `e4f8da06…` (tree listing truncated; partial path screen only).
- 4 GitHub repository searches returned 0 hits.

Results are in `outputs/registry-path-screen.json` and `sources/gh-search-*.json`. A scoped history screen of 69,000 campaign files found no prior disposition of any reserved ID (`outputs/history-screen.json`); sibling records from the same papers were handled consistently by r59, r89, r159 and r176. No 403/429 or challenge was encountered. House of Graphs serves only a JavaScript shell, so the snark catalogue was unavailable.

## Process deviations

These are recorded candidly in `logs/environment-notes.txt`:

- one Bash call chained two wrapped runs;
- several inline helper one-liners ran without the ulimit wrapper;
- two n = 16 runs timed out, and one partial log was overwritten.

No Lean, SAT, child agents, git, or writes outside this lane.
