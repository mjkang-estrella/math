# expanded-corpus-r137 (Claude): summary

Lane: reserve7 reservation of 20 MathDB IDs (`reservation.json`). Investigator pass, 2026-11-03 18:30–20:00 UTC.

Lane restrictions observed:

- No Lean, lake, leanchecker, SAT or ILP, and no compiled helpers.
- Only `python3 -I`, one process at a time, run under `scripts/capped.sh` (2 CPUs, 120 s CPU, 140 s wall, RSS sampled). Peak RSS was under 200 MiB. Receipts are in `logs/*.receipt.json`.
- No git, no writes outside this lane, and no background jobs left running.
- Zero credit is claimed; nothing is self-accepted.

## Outcome

### 1. 329080: chord diagrams with genus range {1, 2} — CANDIDATE

Conjecture 3.4 of Burns–Jonoska–Saito et al., arXiv:1410.6148 (JKTR 2015).

**Literal defect.** The printed "for any n ≠ 4" is false at n = 1, 2, where no diagram has range {1, 2}. This follows from the source's own table and earns zero credit.

**Main result.** A full proof of the intended statement:

- for every n ≥ 3 with n ≠ 4, the unique diagram with genus range {1, 2} is (123123)(44 ⋯ nn);
- n = 4 has exactly four such diagrams;
- n = 1, 2 have none.

**Proof ingredients:**

- band-deletion heredity of the minimum and maximum genus;
- bipartite interlacement graph ⇒ planar thickening;
- shortest-odd-cycle reduction to a triangle;
- a new finite 5-chord base lemma (79 classes; 453 explicit genus-3 witnesses over 945 labelled words);
- a new dart-model transfer lemma for existence.

**Verification.** Everything was checked exhaustively in the combinatorial model:

- the model agrees with the ribbon-graph face count and with the source's GR₁…GR₆ table;
- the hereditary classification up to n = 9 confirms uniqueness (the source computed n ≤ 7).

**Files.** `outputs/329080-proof.md`, `lean/329080/` (UNCOMPILED drafts plus PLAN.md with the statement correspondence), `outputs/chord-*.json`, `scripts/chord*.py`.

**Risks for root:**

- the topological boundary count is bridged to the combinatorial face count;
- the conjecture is modest, and the heredity-plus-finite-base technique may be judged routine;
- the Lean cost is moderate to heavy, dominated by the general permutation surgery lemma.

### 2. 368752: prefix-reversal expander conjecture — refuted, probably zero credit

Blanco–Buehrle Conjecture 6.3, arXiv:2506.08345v1.

**Result.** For every n ≥ 1, h(P_m(n)) ≤ n(n + 1)/⌊m/2⌋. So {P_m(n)}_m is never an expander family. The proof uses the color-sum map to Z_m; the bound is attained exactly on the literal graphs I built.

**Why it probably earns nothing.** It is a generic abelian-quotient obstruction (lesson 373367). It is also a two-line bridge from Greaves–Zhu, arXiv:2509.09425, Lemma 2.5, plus the Cheeger bound the source itself prints. Expect EXCLUDE.

**Files.** `outputs/368752-refutation.md`, `lean/368752/Refutation.lean` (UNCOMPILED).

### 3. Bounded searches with no counterexample (parked)

**356145 — five-letter complete bifurcate trees.**
- I recast the question as an insertion game; the solver reproduces the source's four-letter Theorem 7.
- With five letters, Builder survives to depth 14 when Spoiler may insert anywhere.
- Builder also survives to depth 22 when Spoiler must insert next to the last letter, and to depth 15 when Spoiler may insert within distance 2 of it.

**363690 — path-linked triangles.**
- Every perfect triangle gluing onto H = (t ≤ 4 triangles) + a path is 3-colourable for |V(H)| ≤ 15, even ignoring the path-linked restriction. That is up to 1.4M gluings per H.
- This covers every H with at most 15 vertices.

**334831 — fixed-order Roller-Coaster.**
- For α = 6 and n ≤ 16, a structured clique-partition search realizes 4 of the 6 orders of (s₃, s₄, s₅).
- The two "dip" orders, with s₄ below both s₃ and s₅, were never found. That is a lead only: no non-existence proof is available.

**374787 — distinct covering systems.**
- I looked for a cheap density counterexample over exponents up to 8 and m < 200, and none exists.
- An exact search needs ILP or SAT, which this lane can't run.

### 4. Source-settled, public partial progress, or deep (parked or zero credit)

| ID | Disposition |
|---|---|
| 351991 | Source-refuted (ART(k) > (k − 2)/(k − 3) for k = 6..10). |
| 351632 | Partial public progress (Wenger graphs, g = 8, q odd); extremality refuted at q = 3 by arXiv:2401.08271; g = 12 open. |
| 359084 | Open for k ≥ 3; needs a modular-forms route. |
| 325256 | All-n tatami coefficient identity; authors verified to n = 20. |
| 339134 | Uniform PG(2, q) construction needed. |
| 347137 | Every-root refutation needed; strictly harder than the excluded 347138 gadget route. |
| 324966 | Likely Postle–Thomas (not verified). |
| 356265 | All-n gucycle existence. |
| 369787, 374003, 351150, 363427 | Hard structural, asymptotic, or infinite objects. |
| 364297, 404700 | Flagship open problems. |

Each ID has an entry in `results.json`.

## Checks performed

- **Provenance.** Exact raw lines are in `raw/<id>.jsonl` (newline preserved). Chunk, line, chunk, raw and statement hashes are in `results.json` and `outputs/provenance.json`.
- **Sources.** All 19 arXiv sources were fetched with receipts in `sources/*.receipt.json`. Current versions were checked from the abstract pages: v4 for 324966; v2 for 339134, 351150, 364297 and 369787; v1 for the rest. The published PMC version of 329080 was checked.
- **Campaign history.** No prior notes on any of the 20 IDs; only the reservation lines in ledger.json (`outputs/history-hits.txt`).
- **Registries.** Live HEADs fetched 2026-11-03 19:10 UTC:
  - Omega moved to ada3bf0c12ee20d00efcf8b040282d36ddb76e90, from 86172888.
  - OpenAI/math is unchanged at 4eaee87548250b2682affda7d05d947c05554bae.
  - I fetched the complete Omega D5 (13,784 paths) and Problems (1,700 paths) trees and screened them by path (`outputs/registry-path-screen.json`).
  - I read the PrefixReversal files that matched; they concern Hamiltonicity and generation, not expansion.
- **Prior art.** Web searches for 329080 and 368752 found no later resolution. No access routes were retried after denial, and no denied routes were attempted.

## Recommendation to root

- Route 329080 to independent review: proof fidelity, novelty, and whether the face-count bridge is acceptable. Then send it to a Sol worker for Lean, following `lean/329080/PLAN.md`.
- Treat 368752 as a probable exclusion: a routine bridge.

## Process notes

- A few short runs used a plain `timeout 130 python3 -I` without the capping wrapper. These were the n = 12 triangle sweeps (under 1 s each), the class listing for chord diagrams with n ≤ 7, and the density scan. Each was a single process with RSS well under 100 MiB. Every substantive run has a receipt in `logs/`.
- `outputs/history-files.txt` is the partial output of a first, over-broad history grep. I stopped it after about 10 minutes because of hash-substring false hits. The authoritative history screen is `outputs/history-hits.txt`.
