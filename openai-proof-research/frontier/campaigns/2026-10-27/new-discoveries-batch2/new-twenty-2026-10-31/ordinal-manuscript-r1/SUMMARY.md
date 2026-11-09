# SUMMARY: ordinal-manuscript-r1 (MathDB 366371) — DRAFT

**Status.** DRAFT manuscript and reproducible Lean dossier. **Zero accepted credit**; the campaign root alone accepts. Campaign count unchanged at **7/20 beyond 39**. MathDB 366834 (root HOLD) is neither presented nor bundled. Written by Claude Opus 5.5 without child agents, git, network access, browser or edits outside this lane.

## Result

A six-point ordinal space whose identity enumeration has the Keller–Petrov majorization property (Definition 7.1; all chain lengths k, repeats, permutations) but which does not embed in ℝ¹. This refutes Conjecture 7.4 of K. Keller and E. Petrov, *Ordinal spaces*, Acta Math. Hungar. 160 (2020) 119–152 (arXiv:2412.17391v1), in the range n > 4 left open by Theorem 7.5.

- Witness: pairs of {0,…,5} ranked 23 < 34 < 12 < 24 < 01 < 13 < 14 < 45 < 35 < 02 < 25 < 03 < 04 < 15 < 05.
- Majorization for every k: threshold-count reduction (Lemmas 4.1–4.2) to a 63 × 63 × 15 finite check (Lemma 4.3, kernel `decide +kernel`).
- Non-embeddability: forced order 0 < 1 < … < 5, then five comparisons summing to 0 < 0 (gap coefficients 1,2,2,2,1 on both sides).
- Lean endpoints: `OrdinalSpaces366371.not_majorizationConjecture : ¬ MajorizationConjecture` and `OrdinalSpaces366371.witness`.

## Deliverables

| File | Content |
|---|---|
| `paper.pdf` (6 pages, sha256 84238f8c…) | DRAFT manuscript; source `write_paper.py`; build record `paper-build.json` |
| `qa/page-1..6.png`, `qa/receipt.json` | every page rendered at 100 dpi and inspected; fixes recorded |
| `PROOF.md` | ordinary proof, Lean correspondence, certified vs diagnostic, limitations |
| `proof/OrdinalLine.lean` | literal module, byte-identical to `expanded-corpus-r61/formal/OrdinalLine.lean` (da892a4d…cec7703f) |
| `proof/ReviewAudit.lean`, `proof/ReviewSanity.lean` | labelled reviewer supplements |
| `replay.py`, `safe_extract.py`, `diagnostic.py`, `pins.json`, `REPRODUCE.md` | portable replay (LEAN_BIN, LEAN_PACKAGES) |
| `sources/` | exact MathDB raw line (sha256 585e249c…), arXiv HTML/abs/text with receipts, `RECEIPTS.json` |
| `source-only-proof.zip` (sha256 f1c7311e…), `source-manifest.json` | 17 members |
| `full-dossier.zip`, `dossier-manifest.json`, `archive-hashes.json`, `full-dossier-verification.json` | full dossier, verified by fresh safe extraction |
| `fresh-extraction/replay-receipts/` | receipts of the fresh replay (result.json: PASS) |
| `frozen-before.json`, `frozen-after.json`, `receipts/frozen-comparison.json`, `frozen-final-check.json` | frozen-input bindings (identical) |
| `evidence/` | verbatim 366371-only author and review evidence; labelled 366371-only extracts of the joint review and root adjudication |
| `results.json` | machine-readable summary |

## Verification (fresh extraction of the source-only ZIP)

- Strict build `lean -j1 -DwarningAsError=true`: exit 0, empty log, 4.0 s; olean sha256 cddbfa4e… (byte-identical to the author lane and the independent review).
- `leanchecker OrdinalLine`: exit 0.
- Full declaration audit: all 95 module constants (23 def, 69 theorem, 1 inductive, 1 ctor, 1 recursor), cross-checked against an environment origin scan; full types printed; every def/theorem has a body (`value? true`); none unsafe/partial/implemented_by/extern/axiom/opaque; no `sorry`; transitive axioms ⊆ {propext, Classical.choice, Quot.sound}.
- Sanity supplement: endpoint types, non-vacuity (Prec with a transposition, Sim with repeats, EmbeddableInLine on two points), `#print axioms` of both endpoints.
- Negative controls: 5 rejected as intended (dropped fifth comparison → `linarith failed`; perturbed table → kernel finite check `is false` at the exact line; wrong endpoint; `sorry`; added axiom) plus malformed olean; 2 positive twins pass.
- Diagnostic (stdlib): axioms over 6⁶; literal Definition 7.1 for k ≤ 4 under both readings (441/3136/15876/63504 chain pairs, 0 violations; counts match the independent review); reduced finite check; threshold = sorted dominance; certificate; perturbed table fails.
- Caps per call: ≤ 2 CPUs, CPU 120 s, wall 140 s, AS 64 GiB, MALLOC_ARENA_MAX=2, sampled private RSS guard 6 GiB (max observed 724 MB private; total VmRSS reported, max 2.46 GB), systemd user scope MemoryMax=6G active. No job left running.

## Limits (also in the paper)

- Published 2020 journal text not read; arXiv v1 (Dec 2024) postdates it; identity of Conjecture 7.4 assumed.
- Bounded prior-art search (author lane: 1 web + 1 arXiv author search; review: 5 web searches); classical scaling literature not searched body by body. **No priority claim.**
- n = 5 and n = 6 scans are diagnostics only; **no minimality claim**.
- Significance modest and expected in spirit (cf. Kraft–Pratt–Seidenberg 1959); not implied by bounded-order cancellation results (majorization: unbounded order, restricted shape).
- Trusted base: Lean kernel/compiler, prebuilt Mathlib oleans (no upstream rebuild), leanchecker from the same installation.
