# expanded-corpus-r139: summary (Claude lane, 2026-11-03)

There are 20 reserved MathDB IDs (reserve7). `results.json` has exactly 20 ID-keyed entries, each with exact provenance: chunk, one-based line, chunk, raw and statement sha256, and arXiv abstract receipts.

This lane ran no Lean, SAT/ILP or compiled helpers. Every computation was a single `python3 -I` process under `scripts/limited.py` (2 CPUs, 120 s CPU, 140 s wall, 1.5 GiB sampled RSS, 4 GiB address space, MALLOC_ARENA_MAX=2). Receipts are in `logs/*.receipt.json`. No background jobs remain. Nothing was written outside this lane. Nothing is self-accepted.

## Candidate (needs root review and Lean compilation)

**355217: strict middle-graph increase conjecture (Kazemnejad, Pahlavsay, Palezzato, Torielli, arXiv:2206.15439 v1, Conjecture 7.1) is FALSE.**

- **Witness.** G8 is connected, with 8 vertices and 11 edges: 01 06 16 23 27 37 46 47 56 57 67. That is, two triangles {0,1,6} and {2,3,7}, the hub edge 67, and twins 4 and 5 joined to both hubs. For it, γ̃c(G8) = 4 = γ̃c(M(G8)).
- **Certificates.**
  - S = {0,2,4,5} is an outer-connected dominating set of G8; a four-case argument shows no 3-set works.
  - D = {m01, m23, m46, m57} (a perfect matching) is an outer-connected dominating set of M(G8).
  - Vertex-node counting gives ≥ 4 (the source's Theorem 4.1).
- **Structure.** For even n, γ̃c(M(G)) = n/2 if and only if G has a perfect matching F with G − F connected. This gives an infinite equality family G_{a,b}, with a, b ≥ 1 and n = 2a + 2b + 4, proved by hand and checked for a, b ≤ 3.
- **Search.** All connected graphs of order ≤ 8 were checked. There is none for n ≤ 7, and G8 is the unique case at n = 8.
- **Domain.** The literal statement also fails for the 2-vertex edgeless graph. That is a domain defect and is not claimed; G8 is connected.
- **Source and prior-art checks.**
  - The source's own families all satisfy the strict inequality, so there is no source-internal conflict.
  - Only v1 exists, and the 2023 follow-up does not discuss the conjecture.
  - Web searches found no refutation.
  - The live Omega HEAD e73ca9e3 has moved since root's 86172888. Its full recursive D5, Problems and Reg trees were screened with no match. OpenAI/math HEAD 4eaee875 is unchanged.
  - Root should still run Scholar, MathSciNet or zbMATH citation searches.
- **Significance.** The conjecture is human-posed but niche. The certificate is very small and has literal definitions, which matches the root's Lean-cost priority.
- **Deliverables.**
  - `work355217/PROOF.md`: ordinary proof, Lemma, family, credit checks and statement correspondence.
  - `work355217/lean/MiddleOCD.lean`: an **UNCOMPILED** draft. It gives the literal definitions under both connectivity conventions and the endpoints `conjecture71_false`, `conjecture71'_false` and `conjecture71Connected_false`. The generic lemmas cover parent-map connectivity, closed-set disconnection, vertex-node counting and matching domination. Steps marked PERF use kernel `decide` and have hand-argument fallbacks.
- **Related ID.** MathDB 355218 (the same source's Conjecture 7.6, γ̃c(L(G)) ≤ γ̃c(M(G))) is outside this reservation and was not examined. Flag it for root.

## Settled or known (zero credit)

- **357110:** disproved in the literature by Hu, Lou and Huang, arXiv:2307.15605 (2023). The literal statement also fails at n = 7, where P7 has γ = 3 = ⌊7/2⌋. My exhaustive tree search (odd n ≤ 15) independently finds smaller-ρ trees for every odd n ≥ 7; at n = 9 the spider T(1,2,5) has ρ = 2 < ρ(H') ≈ 2.112.
- **367811:** the source itself (Norin–Steiner) disproves the Guo–Kang–Zwaneveld conjecture.
- **368875:** the source proves the Botler–Naia conjecture.
- **326684:** the source's Remark 1.3 shows failure for n = 2–4 and validity at n = 5, and its Theorem 1.2 covers n ≥ 6.
- **373604:** proved by Keusch (JCTB 2024).
- **336640:** proved by Ferber–Krivelevich (Adv. Math. 2022).
- **358688:** proved by H. Lee, arXiv:2306.06627 (digraph form, stronger).
- **325257:** printed part (a) (j ≤ 2^k) contradicts the source's own Table 4 at n = 6, j = 4 (⟨z¹⟩P₆ = 0 but ⟨z¹⟩P₁₀ = −1). This is a zero-credit correction. The extended verification below found no independent failure.

## Parked, with exact coverage

- **325257 tatami.** Exact P_n validated against every datum in the source. Coverage for n = 2…285 (the authors stopped at n < 200):
  - Parts (b), (c), (e) and (f) all hold. Real-root counts were decided exactly by Descartes' rule for n ≥ 20, using the fact that P_n > 0 on (0, ∞).
  - Monotonicity of α_n was certified by exact rational separators.
  - Corrected (a) (j < 2^k) holds over the caps listed in `results.json`.
  - Irreducibility (d) was not checked.
- **324534 Skowronek-Kaziów.** Weights {1,2} by products are the same as {0,1} total weights by sums. This is a special case of the Wong–Zhu (2,2) conjecture. It holds for all 288266 graphs with n ≤ 9.
- **369136 Beaudou.** It holds for all connected graphs with n ≤ 8. It is already known for mp ≤ 4, so any counterexample needs γ_b ≥ 11.
- **Open structural or famous items, with source-backed dispositions:**
  - 351642 Bárány–Larman
  - 327276 Moshkovitz–Shapira (K_{2,3} and s = t−1 known; asymptotic in n)
  - 323205 (d = 6, 7 done by the source; d = 8 needs 110-vertex searches beyond the lane limits)
  - 331992
  - 337246
  - 340252 (an "exists c" statement)
  - 347086
  - 353843
  - 359723 (Clow–Stacho is linear only when t ≥ log₂ χ₂)

## Reusable tooling (lane-local)

- `scripts/graphgen.py` and `scripts/graphgen_chunk.py`: pure-Python canonical augmentation. `graphs/g1..g9.txt` hold all graphs up to 9 vertices, with counts matching OEIS.
- `scripts/extract.py`: provenance and history patterns. It uses grep because `rg` is not on the host.
- `scripts/fetch_abs.py` and `scripts/report.py`.
- Source receipts: `sources/pdf-receipts.txt`, `sources/abs-receipts.json`, `sources/head-*.json` and `sources/omega-*-e73ca9e3.json`.
- `history-matches.txt` is large because title patterns matched common words. Every ID hit was checked and found to be an incidental digit match inside hashes or numbers. No prior review of any reserved ID was found.
