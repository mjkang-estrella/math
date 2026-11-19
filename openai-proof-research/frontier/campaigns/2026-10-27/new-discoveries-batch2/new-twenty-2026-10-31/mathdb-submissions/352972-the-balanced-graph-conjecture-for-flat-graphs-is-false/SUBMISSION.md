# MathDB 352972: The balanced-graph conjecture for flat graphs is false

- Problem: https://mathdb.com/p/352972
- Source: MathDB 352972 literal universal conjecture; Hossein Teimoori Faal, On Clique Roots of Flat Graphs, arXiv2112.09721v1, Definition2.2/equation14/Conjecture2
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `FlatBalance.not_flat_balanced_conjecture and FlatBalance.not_flat_balanced_conjecture_via_bridges`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `flat-balance-corrected.pdf`, `flat-balance-corrected.tr`
- Lean source: `flat-balance-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded primary-body, current-registry and subsumption investigation; not worldwide-priority certification. remaining_literature_limits: No exhaustive worldwide novelty or complete citing-body review; Live MathDB comment/solution state not cleared; Current repository roots are not complete semantic proof-body audits; Changed TauCeti/LeanPool comparison bodies unavailable; bounded indexed search is incomplete; Unindexed or inaccessible specialist prior results remain possible trust_limits: Pinned prebuilt upstream trusted; no full upstream source rebuild or external attestation; leanchecker uses the same pinned Lean installation; RSS sampled, not a universal cgroup peak guarantee; Strict whole-process procedural compliance not claimed not_claimed: Minimality or smallest counterexample; Refutation of source Conjecture1; Publication or journal peer review; Worldwide priority; New credit for convention correction or a helper
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the balanced-graph conjecture for flat graphs, under both counting conventions. The complete bipartite graph K_(3,3) is flat, every edge lying in at most two triangles, yet its clique counts give an odd-side total of 6 against even-side totals of 10, or 9 when the empty clique is excluded, discrepancies of 4 and 3; no planarity or isolated-edge restriction is imposed. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

An actual finite simple undirected K3,3 is flat (every edge lies in at most two triangles), but its actual unordered clique counts are c0=1,c1=6,c2=9 and all higher zero. Odd total 6, inclusive even total 10, positive even total 9; discrepancies 4 and 3 refute both conventions. No planarity/no-isolated-edge restriction inserted.

## Body (paste into the MathDB body field)

Use the written proof in this folder: flat-balance-corrected.pdf. The complete Lean source is in flat-balance-source-only.zip.
