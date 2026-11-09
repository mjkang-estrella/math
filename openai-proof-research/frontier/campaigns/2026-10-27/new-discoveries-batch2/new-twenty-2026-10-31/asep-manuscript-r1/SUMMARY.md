# MathDB 368807 manuscript dossier: DRAFT, zero accepted credit

This lane covers Conjecture 1 of Vercesi, Barta, Gambardella, Gualandi and Mastrolilli (arXiv:2506.10671v1, p. 14): "For each x vertex, N(x) contains at least one tour". The campaign count stays at 15/20 beyond 39, and root alone accepts.

## The result

x* = X/4 is a fractional vertex of P^8_ASEP that is adjacent to no tour, so Conjecture 1 is false.

- x* has 19 support arcs and exactly 8 tight cuts, which form 4 complementary pairs.
- Its tight-system rank is 56 = m.
- For each of the 5040 tours, an integer perturbation certificate (slack 1/8, scale 1/512) shows that [x*, T] is not even an extreme subset.
- Whether n = 6 and n = 7 also fail is open.

## The paper

The paper is `asep-368807-draft.pdf`: 7 pages, AI-assisted, DRAFT status, no human authors, no priority claim. Its source is `dossier/paper/manuscript.md`, built by `dossier/paper/build_paper.py`.

It covers:
- the exact source definitions (2)–(4) and (6), Definition 3 and Conjecture 1 with quantifiers;
- why ordinary adjacency is the intended reading, and why the pivot and orbit readings do not rescue the conjecture;
- x* in full, with the vertex lemma;
- the perturbation lemma and the certificate format;
- the rank histogram, labelled as a diagnostic;
- the n = 4 control;
- the Table 2 observation, stated candidly: printed |N| = 20 and 28 against computed 11 and 20, with the tour–fractional double count 3000 = 3000;
- n = 6 and n = 7 as open;
- the formal correspondence table, with all six endpoints and the ASEPDefs and ASEPArcs definitions;
- the axioms and trust limits;
- related work, with Deza–Indik (arXiv:math/0512493) cited as a metric-polytope precedent, not a subsumer.

The bibliography contains only bodies that were read. The Laurent–Poljak conjecture is cited as stated by Deza–Indik.

**PDF checks.** All 7 pages were rendered at 110 dpi (`qa/page-1..7.png`) and inspected visually; the receipt is `receipts/pdf-qa.json`. Three issues found during inspection were fixed:
- an orphaned heading;
- an over-justified reference;
- an unembedded default font.

All fonts are embedded. The PDF built from the extracted source ZIP is byte-identical to the lane build.

## Fresh replay of the source ZIP: PASS

`asep-368807-source.zip` (sha256 `6e0046d0…67bb`, 44 members) was safely extracted and replayed with `tools/replay.py` using `LEAN_BIN` and `LEAN_PACKAGES`.

- **Pins.** Lean 4.34.1 at commit 5045d005…, with lean and leanchecker SHA-256 pinned. mathlib is d13f23b7…; both the manifest and the checkout HEAD file match.
- **Builds.** The replay refuses existing oleans. There were 23 strict `-j1 -DwarningAsError=true` builds in dependency order: the 21 proof modules, the PermOrder helper and AuditLib. leanchecker passed on all 22 frozen modules.
- **Forbidden constructs.** The scan of the proof modules is clean.
- **In-module axiom checks.** The `#print axioms` lines report only standard axioms.
- **Full declaration audit.** It covers 300 local constants: 187 theorems, 110 defs and 1 structure with its constructor and recursor. For each it records the module, full type, `value? (allowOpaque := true)`, the unsafe and partial flags, implemented_by and extern attributes, and collectAxioms.
  - An uncached body walk recomputes all six endpoint closures.
  - Two compiler `_unsafe_rec` helpers (digs and triples, partial safety) are flagged, and no endpoint closure reaches them.
  - All six endpoints use only propext, Classical.choice and Quot.sound: `ASEP.arc_counterexample`, `arc_neighborhood_tour_conjecture_false`, `counterexample`, `neighborhood_tour_conjecture_false`, `segment_not_face` and `segment_not_exposed`.
- **Controls.** The positive control succeeds. All six negative controls fail for the intended reason: a certificate digit mutation, a tour swap, a dropped tight cut, a false no-tight-cut claim, a sorry, and a new axiom caught by the audit.
- **Caps.** There were 54 Lean calls, run one at a time, each with 2 CPUs, CPU ≤ 120 s, wall ≤ 140 s, sampled RSS ≤ 6 GiB, MALLOC_ARENA_MAX=2 and a systemd MemoryMax=6G scope. The maximum CPU time was 21.0 s and the peak sampled RSS was 5.16 GB (ASEPCover).

Receipts are in `fresh-replay/receipts/`. Before a final cosmetic fix to the PDF builder, an identical replay of the earlier ZIP also passed; it is recorded in `receipts/superseded-replay.json`.

## Other checks

- The Lean modules are byte-identical across `expanded-corpus-r96/lean`, the dossier and the extracted copy (22 files; `receipts/lean-identity.json`).
- The raw MathDB line hash is c215c90f…1067 (`receipts/mathdb-binding.json`).
- An exact stdlib cross-check, run on the extracted copy, passes (`receipts/check-arith.json`):
  - feasibility over all 238 cuts;
  - the 8 tight cuts;
  - rank 56;
  - all 5040 certificates re-decoded with the tight cuts recomputed, maximum Σ|v| = 34;
  - the n = 4 control, with 5 of 6 tours adjacent.
- All 1012 frozen input files are unchanged before and after the work (`receipts/frozen-bindings.json`).

## Deliverables

- `asep-368807-draft.pdf`, and the paper source in `dossier/paper/`.
- `dossier/PROOF.md` and `dossier/REPRODUCE.md`.
- `results.json`.
- `asep-368807-source.zip`.
- `asep-368807-full-dossier.zip` (sha256 `23063a4e…78bc`, 268 members). It adds hash-identical copies of the sources and receipts, the review and adjudication, the history, the fresh-replay receipts, the QA images and the receipts. It was verified by a fresh safe extraction against its manifest (`full-dossier-verification.json`). `results.json` and `SUMMARY.md` describe the ZIPs and are not inside them.
- `source-manifest.json`, `full-dossier-manifest.json` and `ARCHIVES-SHA256.json`.
- `receipts/` and `qa/`.

## Limits

- The literature check is bounded and is not a novelty clearance. The Laurent–Poljak originals, the journal version of Deza–Indik, Elliott-Magwood's thesis and the 2024 Optimization Online file (HTTP 404) were not read.
- The rank histogram was not recomputed here.
- The prebuilt mathlib oleans are trusted. leanchecker was not run with `--fresh` and shares the Lean installation. RSS is sampled.
- reportlab 5.1.0 was copied hash-identically from the xor-magic lane into `tmp/pdfdeps` (`receipts/pdfdeps-copy.sha256`); there was no network install.
- Significance is modest: the conjecture is a remark drawn from preliminary tests.

## Conduct

- No child agents, git, publication, uploads, browser use, accounts, external messages or ledger edits.
- No network access by this lane.
- No writes outside this lane.
- No jobs are running (`receipts/no-running-jobs.json`).
