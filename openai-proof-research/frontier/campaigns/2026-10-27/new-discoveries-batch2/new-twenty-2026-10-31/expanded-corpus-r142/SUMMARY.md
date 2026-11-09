# expanded-corpus-r142: summary (Claude lane, reserve7, 20 IDs)

Date: 2026-11-04 (UTC). Lane-local work only. No Lean, lake, leanchecker, SAT or ILP solver, or compiled helper was run. All computations used capped `python3 -I` through `scripts/run-capped.sh`, one process at a time. The largest peak RSS sampled was about 30 MB. No background job is left running. No credit is claimed, and nothing is self-accepted.

## Headline: one candidate, MathDB 354228 (full ordinary proof, no Lean)

Bača, Semaničová-Feňovčíková, Lai and Wang (FI 185(2), 2022; arXiv:2204.04479v2) conjecture the following (their Conjecture 6, even case):

> For every even t ≥ 2, the complete full t-ary tree satisfies χ_la(T) = l + 1.

The source proves the odd case and the bound ≤ l + 2 for even t.

**Result.** I give a complete ordinary proof that χ_la(T(t, n)) = t^n + 1 for every even t ≥ 2 and every depth n ≥ 1 (`outputs/antimagic/proof.md`).

- **Lower bound.** This is the standard leaf argument, included in the proof.
- **Upper bound for n ≥ 3.** The construction is new and explicit:
  - leaf edges get the top label block;
  - the internal labels form nested shells {Z ± d} around Z = (N − t)/2 + 1, so every row from 1 to n − 2 is coloured tZ + (its own label set); these sets are disjoint and lie inside the leaf-label range, which makes the colouring automatically proper;
  - the permutation σ(a) = 2a, σ(k + j) = 2j − 1 has displacements exactly ±1, …, ±k, so the leaf t-tuples have sums Γ ± d and every parent of leaves gets the single new colour c = Γ + Z;
  - t = 2 needs one swap.
- **Upper bound for n = 2, t ≥ 4.** A separate explicit family built from the source's Lemma 2.13; n = 2, t = 2 and n = 1 are handled explicitly.
- **Evidence.** Generator `scripts/antimagic/construct.py`. The independent checker `scripts/antimagic/check.py` verifies tree shape, bijectivity, properness and the colour count. It passed all 84 cases (t up to 60, up to 32 766 edges; `outputs/antimagic/check-r2.jsonl`).
- **Prior art (bounded search).** No resolution of the even case was found on the web. The citing preprint arXiv:2610.22783 (Oct 2026) disproves the general tree leaf conjecture but does not touch even full trees. The Omega registry at HEAD 3bb89bf7 (live HEAD, advanced past root's 86172888; complete Problems listing of 1709 files and the D5/S3/Combinatorics subtree) has no antimagic or full-tree item. OpenAI/math HEAD 4eaee875 is unchanged.
- **Lean.** Not built. There is an UNCOMPILED draft with a literal endpoint statement and `sorry` obligations (`formal-draft/LocalAntimagicEvenTree.lean`) and a correspondence plan (`formal-draft/STATEMENT-CORRESPONDENCE.md`). Lean cost is HIGH: this is a general-n construction, estimated at several thousand lines. That is a real negative under the root's Lean-cost priority.
- **Risks for root.**
  1. Significance: this is a modest labeling conjecture from Fundamenta Informaticae.
  2. Family: graph labeling is adjacent to the credited 381805 (SEMT strength), but it is a different invariant.
  3. The n = 2 case uses the source's Lemma 2.13 (the n ≥ 3 case does not).
  4. Independent review is still needed.

## The other 19 IDs

| ID | Outcome | Reason |
|---|---|---|
| 353608 | EXCLUDE | Shi–Shan conjecture proved (Xu–Li–Zhou, arXiv:2303.09741; Ota–Sanka; strengthened by Liu, arXiv:2503.12860). |
| 354274 | EXCLUDE | Covered for all ℓ: Chudnovsky–Seymour (ℓ = 2), Wu–Xu–Xu (ℓ = 3), Wang–Wu (arXiv:2307.01460, ℓ = 4; body unread), Chen (arXiv:2301.00112, ℓ ≥ 5). |
| 354848 | EXCLUDE | The source v2 itself reports that Scott–Seymour proved Conjecture 5.2. |
| 355123 | EXCLUDE | Neither arXiv version has a conjecture; the record paraphrases the source's proved Lemma 3.8 as a "for every f" claim. |
| 358203 | EXCLUDE | The literal t ≥ 2 form is refuted by the source's own family Q. Exact check at t = 2, p = 3/5, n = 80: μ(Q) = 0.3431 > 0.33696 (`outputs/tomon/q-t2.json`). The genuine t ≥ 4 conjecture is hard. |
| 358962 | EXCLUDE | The endpoint misprint is genuine at n = 9: neither symmetric partition of 9 has a full tensor square, by exact computation (`outputs/kron/n9.json`). This is the known Pak–Panova–Vallejo exception {2, 4, 9}. n = 10 to 12 hold. |
| 360433 | PARK after computation | Ruckle (proven for n ≤ 7). Integer-weight and 2–4-level block strategies for n = 8 to 14 found no violation (`outputs/ruckle/*`). This does not exhaust all LP vertices. |
| 354609 | PARK | Buratti–Horak–Rosa; the source already verifies n ≤ 37. |
| 354065, 359798, 360250 | PARK | Famous open problems: Matching–Jack non-negativity, Frankl's union-closed conjecture, BIG⇒BIG (equivalent to Erdős–El-Zahar). |
| 354567, 359239, 360099, 360217, 360508, 360682, 360817, 367148 | PARK | Probabilistic, model-theoretic, convex-geometric, extremal-matroid, asymptotic, classification-level, geometric-group-theory and structural problems respectively. None has a tractable finite certificate. The 360217 check of rank-6 direct sums found no counterexample; 367148 at \|X\| = 8 was not attempted. |

## Files

- `results.json`: exactly 20 ID-keyed entries, each with literal statement, provenance (chunk, line, chunk/raw/statement SHA-256), review depth, outcome, attempts, coverage and gaps.
- `outputs/extracted.json`, `sources/<id>.raw.jsonl`: literal corpus lines.
- `sources/*.abs.html`, `*.html.html`, `*.body.txt`: arXiv receipts (abstract pages with version histories), fetched 2026-11-04. Fetch logs are in `outputs/fetch-*.json`.
- Registry receipts: `outputs/registry-heads.json`, `omega-compare.json` (445 commits since 86172888; file list truncated at 300), `omega-tree-screen.json`, `omega-problems-screen.json`, `omega-d5-comb-screen.json`, `omega-labeling-files.json`.
- Scripts: `scripts/` (`extract.py`, `fetchabs.py`, `html2txt.py`, `run-capped.sh`, `antimagic/*`, `ruckle/*`, `kron/kron.py`, `tomon/q.py`, `finalize.py`).

## Coverage notes

- The first Ruckle sanity runs (n ≤ 7) and the earliest exploratory annealing were printed to the console only. The saved logs are reruns.
- The Plan-A local search is superseded by the explicit construction.
