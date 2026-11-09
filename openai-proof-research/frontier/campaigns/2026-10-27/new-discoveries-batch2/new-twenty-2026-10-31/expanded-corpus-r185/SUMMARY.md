# expanded-corpus-r185 (Claude lane): summary

Reservation: 20 MathDB IDs between 342653 and 344926, listed in reservation.json under the reserve8 selection. Exact raw corpus lines are in raw/ and their hashes in extracted.json and results.json; the prior-campaign grep is in history-matches.txt (numeric false positives only, so no old exclusions). All twenty sources were fetched from arXiv (abstract pages showing every version, plus current e-prints for the 14 sources worked on beyond the abstract). Receipts are in outputs/fetch-receipts.json. Computations followed the Claude-lane rules: python3 -I only, one capped run per call, peak RSS under 1.8 GB, no Lean, no SAT/ILP. No child agents were used, nothing was written outside this lane, and no git operations were run.

**Outcome: no strong candidate, so there is no CANDIDATE file.** One item is resolved in full by a short bridge from published work. Two items are resolved in the literature. The finitely checkable items received structured searches beyond the authors' published ranges, and none produced a counterexample.

## Dispositions

| ID | Outcome | Basis |
|---|---|---|
| 343238 Abebe generalized Brouwer | **TRUE: resolved by a routine bridge (zero credit)** | k = 2 is Brouwer's conjecture, proved by Kothari–Tudose (arXiv:2606.12197). For k ≥ 3, Lew's Theorem 1.3 (arXiv:2508.04209) gives s_t ≤ (sum of the (r+1)t largest ridge degrees) ≤ r·f_r + #(facets with boundary inside the chosen ridges). Lovász–Kruskal–Katona together with C(t+r, r) ≥ (r+1)t then gives the bound C(t+r, r+1), which is exactly Abebe's inequality. Lew does not draw this conclusion. See outputs/343238-bridge-proof.md. |
| 343505 Medvedoff–Morrison shuffle groups | Resolved (published) | Xia–Zhang–Zhang–Zhu, Forum Math. Sigma 12 (2024) e104 (arXiv:2304.01037): the full Shuffle Group Conjecture, plus the parity remark fixing Alt versus Sym. |
| 344346 sign of odd-part index difference | Resolved (published) | Equivalent (Seo–Yee Theorem 1) to non-negativity of 1/(q,−q³;q⁴)∞, proved by Craig (arXiv:2112.09269). |
| 344347 generalisation to O^d | Parked (analytic) | Positivity of 1/(q,−q^{4d−1};q^{4d})∞ for every d. Only d = 1 is known. It needs circle-method analysis for each d and is a pair variant of 344346. |
| 342653 homogeneous block counts | Parked, with bounded verification | At most two blocks follows from the source (length and exponent sum are invariant). The paraphrase is ambiguous when an index is absent from a word, a wording defect. Exhaustive search over e-homogeneous words with the faithful Artin action on F_n found no conflicting block counts: ++−+ to length 12 (543,100 braids), +−−+ to 12, ++−++ to 11. The braid counts equal the Saito growth series of the conjectured Artin–Tits monoid, so the source's stronger HBGR conjecture holds up to those lengths. A Burau-minor invariant route was tested and refuted (the word σ₂σ₃⁻¹σ₄¹⁰σ₃⁻¹σ₂σ₁ gives degree 11 against c₀ = 3). |
| 343468 Postnikov 2-adic | Parked | Exact check for n ≤ 3500 is consistent, with α ≡ 9047 mod 2¹⁴ and records 343, 855, 9047 as in Postnikov. Postnikov himself verified n ≤ 100,000. No proof route. |
| 344494 Cameron–Mol weaker mean-subtree conjecture | Parked after structured search | Still open per Cambie–Jooken–Wagner v2 (Sept 2026; checked n ≤ 10; barbell graphs with only one increasing edge class). Exact disjoint-pair formula. Every tested graph has an increasing non-edge: K_{a,b} (a ≤ 14, b ≤ 30, closed form), complete multipartite graphs and barbells (n ≤ 12). In clique-dominated graphs a clique-adjacent P3 always increases μ. |
| 344926 Pasotti–Pellegrini near 1-factors | Parked after extended search | Authors verified v ≤ 23. Exact solver with verified realisations on all boundary lists: v = 25 (slack 2, 9,240 lists), v = 27 (slack 1, 24,957), v = 33 (slack 0, 54,264), v = 35 (slack 0, 24,480). All realisable. A refutation would be a costly nonexistence certificate. Near the parked 329760 family. |
| 344776 Brown–Erey | Parked; source-fidelity note | MathDB writes (x)_k where the source has (x−1)_{k−1}, which makes the equality clause literally false (a paraphrase defect, zero credit). Source status: proved at x = k (EEFH), for ω = k or α = 2 (Yang 2023), and for very large x. Cores with long ears reduce to Knox–Mohar's general-x Tomescu bound. No finite route. |
| 342833 Negut positivity | Parked (deep) | Open. The BHMPS convex-curve conjecture (arXiv:2102.07931) would imply it; only lines are proved. |
| 343087 p-group tiles spectral | Parked (deep) | Flagship Fuglede-type statement. |
| 343127 PCSP hardness | Parked (deep) | Brakensiek–Guruswami conjecture. |
| 343222 planar cover degeneracy | Parked (deep) | A minimal counterexample needs min degree ≥ 5, a cover and an f-assignment; infeasible without SAT. |
| 343390 / 343391 undecidability | Parked (deep) | Logic statements and a pair from one source. The Omega card on Young-lattice diagonals is unrelated. |
| 343851 / 343852 infinite Kőnig | Parked (deep) | Infinite hypergraphs; a pair from one source. |
| 344370 free elevation rank | Parked (deep) | Known for d ≤ 3; free elevations cannot be computed in this lane. |
| 344509 Tesler Ehrhart positivity | Parked (deep) | Lee–Liu prove the 3rd and 4th coefficients; dimension about n²/2. |
| 344759 smiling ("bold") bouquet | Parked (deep) | Still a conjecture in v3 (renamed "bold"); infinite geometric. |

## Registry screens (outputs/registry-screen.json)

* Lean Pool HEAD is 01db1d7049cf9668bda1e9e106875ee1278b43e6, unchanged, with a complete 25,038-entry tree and projects.yml. No relevant hits.
* GitHub: 6 spaced repository searches, no denials. Only data repositories turned up (Jooken's mean-subtree code; a math-market BHR statement for the sibling Buratti–Horak–Rosa conjecture). No prior Lean proofs or refutations.
* Omega: live HEAD 1d46a625e4e90388fb62b944367e1bc5fc51257a; the path screen used r182's cached D5 and Library trees at 63ebfbfb. OpenAI/math HEAD is 4eaee875, unchanged; the preprint listing was grepped. No relevant hits.

## Honest credit assessment

* 343238 is a genuine full-scope resolution of the MathDB item, but it is a roughly ten-line combination of Lew's 2025 theorem, a classical theorem (Lovász–Kruskal–Katona) and the 2026 Kothari–Tudose theorem. This is the zero-credit bridge profile, and no credit is claimed. The root may want to record 343238 as "resolved by literature".
* The remaining searches are bounded non-findings. They are recorded precisely so that later lanes need not repeat them.
* No Lean was run (lane restriction). No Lean packet is warranted.

## Files

results.json (20 ID-keyed entries) · extracted.json · raw/*.jsonl · outputs/343238-bridge-proof.md · outputs/registry-screen.json · outputs/github-search.json · outputs/fetch-receipts.json · outputs/abstracts.txt · scripts/ · logs/ · sources/ (downloaded material, untrusted, fresh directories).
