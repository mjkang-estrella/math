# expanded-corpus-r78: summary (Claude Opus 5.5 investigator, 2026-11-01)

Campaign count unchanged: 11/20 beyond 39 prior. No credit is claimed. Root acceptance is needed for anything below.

## Headline candidate: MathDB 334207, proved with a full literal Lean endpoint (pending review)

**Ding–Zhang–Ge Conjecture 2** (arXiv:1609.09236; Finite Fields Appl. 49 (2018)): for every prime power q, every b ≥ 2 and every n ≥ 2b, there is a linear MDS (n, 2b)_q b-symbol code. This is the exact MathDB statement.

The proof is new as far as the bounded search below could tell, and short.

1. For a linear [n, n−b] code, d_b ≥ 2b holds iff every b cyclically consecutive columns of a parity-check matrix are linearly independent. If wt_b(c) < 2b, then a zero window exists and the support fits in a window of length b.
2. Over every field, for every b ≥ 1 and n ≥ b, there is a cyclic sequence of n vectors in F^b in which every b consecutive vectors form a basis. The proof is a strong induction on b with a bridge lemma, which reduces (b, n) to (n mod b, b + n mod b), Euclid-style. The construction is a 0/1 matrix whose window determinants are all ±1.
3. Then |ker H| = q^{n−b}, and δ_0 − δ_b is a codeword of b-weight exactly 2b. So C = ker H is MDS with d_b = 2b.

The source proved only the cases q ≥ b − 1 (b ≥ 3), (q, b) = (2, 4), b = 5 with q ≥ 3, and b | n. It explicitly asked for "a neat and brief proof". The new content is chiefly small fields and arbitrary lengths, for example q = 2, b = 5 with 5 ∤ n.

* Ordinary proof: `BSYMBOL-ORDINARY-PROOF.md`.
* Lean: `formal/BSymbol.lean`. Endpoints are `BSym334207.dzg_conjecture2` (prime power q; every field of order q, plus existence of one) and `BSym334207.dzg_conjecture2_field` (every finite field). The source definitions of wt_b, D_b, minimum b-distance and MDS are encoded literally; the mapping table is in `LEAN-PACKET-334207.md`.
* Verification:
  * strict `-j1 -DwarningAsError=true` build;
  * fresh extracted replay (`fresh-replay/`);
  * `leanchecker -v BSymbol` passes;
  * full audit of all 157 local declarations: none unsafe, no local axioms, transitive axioms ⊆ {propext, Classical.choice, Quot.sound};
  * forbidden-token scan clean.

  `leanchecker --fresh` (replaying all of the imported Mathlib) exceeded the 120 s CPU cap and is not claimed. Details are in `verification.json`.
* Diagnostics: 4,106 windows have determinant ±1 over ℤ, and 68 codes over F_2, F_3, F_5 were fully enumerated, all with d_b = 2b.
* Prior art (bounded):
  * The published version's outline still lists Conjecture 2.
  * Liu–Pan (arXiv:2103.16299) gives an MDS characterisation but no all-length construction.
  * Five other citing papers checked by full-text grep make no claim on Conjecture 2.
  * Web searches (standard and extended) found no resolution.
  * Registries: OpenAI/math HEAD 4eaee87548250b2682affda7d05d947c05554bae is unchanged. Omega HEAD was e307ede5 at 21:50 UTC and 6e37b782cf6cfe60366783f4272ac2ab8645a3e6 at the 23:16 UTC recheck. Full D5/Problems trees were re-fetched at both times; no b-symbol, MDS or symbol-pair path exists (path screen only).
  * Not searched: MathSciNet/zbMATH/Scholar citation indexes, Chinese-language literature.
* Open review questions for root:
  * **significance**: an 8-year-old published coding-theory conjecture, now proved with an elementary argument;
  * **independent prior discovery**: the construction is simple, so this cannot be fully excluded without citation-index access;
  * **statement fidelity**: review the definitions in `LEAN-PACKET-334207.md`.

## Sustained routes, parked with recorded coverage (details in `SEARCH-COVERAGE.md`)

* **329078 (chord-diagram genus ranges, Conjecture 3.2).**
  * Reformulated as the genus range of the cubic backbone+chord graph.
  * The implementation is validated against the paper's tables.
  * Exhaustive search over all chord diagrams with ≤ 12 chords found no counterexample.
  * n = 13 was cut by the CPU cap.
  * No proof, and Lean would need a topological-surface bridge.
* **341374 (χ''(L(K_n)) = 2n − 3).**
  * Type 1 verified for 2 ≤ n ≤ 13 by SAT plus a Z_n-equivariant ansatz.
  * Reformulated as a partition of all P₃'s of K_n into P₃-decompositions of K_n minus matchings, the matchings partitioning E(K_n).
  * No uniform cyclic construction exists (n = 6, 7 fail), so a general proof needs a design-theoretic construction.
  * The conjecture still appears open (only conformability was proved, in 2023).
* **322842 (k-coloured kernels in l-quasi-transitive digraphs).**
  * The literal statement is false at l = 1 by the source's own Theorem 5. That is an endpoint defect, not credit.
  * For l ≥ 2 I reduced the problem via Duchet's theorem to "far pairs". My candidate Lemma A turned out false in general (backward tournaments), so that route is closed.
  * No counterexample in circulant or random searches; the positive control passed.
* **324248 (flashcard bound ≤ 2n).** Exact simulation to t = 10^8: the bound holds, with equality often attained. No proof mechanism.

## Known or resolved (excluded)

| ID | Resolution |
|---|---|
| 316194 | Refuted by Huang–Sudakov |
| 320032 | Fails via Santos' counterexample to Hirsch plus the Klee–Walkup equivalence |
| 323763 | Settled per its own source |
| 329526 | Proved by BHMPW 2020 |
| 332847 | Follows from Hopkins (tCDE ⇒ mCDE) |
| 333295 | Settled by Salez (covers CD(0, ∞)) |
| 339281 | Refuted by its own source |
| 342205 | Refuted by Defant–Elvey Price–Guttmann (μ₃ ≥ 9.4854) |
| 343064 | Settled by Lau 2024, Thm 1.3, and the current version of the source, Thm 3.14 |
| 345108 | Proved by Han, arXiv:2607.08279 (Jul 2026), Lemma 26.2. I computed i, j ≤ 40 before finding this. |

## Parked without a tractable full-scope mechanism (25 IDs; reasons in `results.json`)

316834, 319591, 320953, 322106, 322353, 322409 (finite check s ≤ 200 recorded), 325402, 326089, 328421, 330337, 334241, 334656 (unread lead: Bara 2020), 335127, 336155, 337337, 338400, 340097, 341386, 341906, 342130, 342771, 343453, 343946, 345633, 345748.

## Deliverables

* `results.json`: exactly 40 ID-keyed entries. Each has the literal statement, raw-line provenance (chunk, 1-based line, chunk/raw/statement SHA-256), review depth, outcome and evidence paths.
* `extracted.json`, `raw/` (exact raw lines), `history-matches.txt` (campaign grep: only the reservation itself plus noise).
* `sources/` (dated fetch receipts with SHA-256), `scripts/`, `logs/`, `SEARCH-COVERAGE.md`.
* `BSYMBOL-ORDINARY-PROOF.md`, `LEAN-PACKET-334207.md`, `formal/`, `fresh-replay/`, `334207-proof-source.zip`, `verification.json`, `SHA256SUMS.json`.

## Process notes

* No git operations, shared-ledger edits, child agents, browser tabs, uploads or external messages.
* Temporary CNF scratch files were briefly written to `/tmp/r78t`, outside the lane, and then deleted. The scripts now write to `outputs/cnf/`.
* No background jobs are left running.
