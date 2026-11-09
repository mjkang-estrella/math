# expanded-corpus-r135: summary (Claude Opus 5.5 investigator lane)

Date: 2026-11-03. 20 reserved IDs from reservation.json (reserve6). I wrote only in this lane directory. No child agents, no git, no Lean, no solver binaries, no compiled helpers. All computations were single capped `python3 -I` processes (`scripts/limited.py`: 2 CPUs, CPU 120 s, wall 140 s, RSS sampled under 6 GiB). Two runs reached the CPU cap and are recorded as such. No background job is left running.

## Headline: one candidate

**347138, Bang-Jensen–Bessy–Yeo Conjecture 35: REFUTED (candidate).** The ordinary proof is complete; the Lean draft is UNCOMPILED.

- **Family.** For every m ≥ 3, take D_m on m + 4 vertices:
  - the complete digraph on A = {a_1, ..., a_m};
  - the source's own semicomplete digraph W1 on B = {p1, p2, p3, p4} (4-cycle, chord p1p3, 2-cycle p2↔p4);
  - entries a_1p1 and a_2p3, and exits p3a_1 and p3a_m.
- **Properties.** λ(D_m) = 2 and α(D_m) = 2.
- **Failure.** No vertex of A is the root of a non-separating out-branching. A two-arc cut forces the branching to use exactly one entry, and crossing arguments then reduce everything to two 2-line W1 cases.
- **Files.**
  - Proof: `candidates/347138/PROOF.md`.
  - Correspondence plan: `candidates/347138/statement-correspondence.md`.
  - Draft Lean: `candidates/347138/lean/NonSepBranching.lean`. It is UNCOMPILED and contains explicitly tagged `sorry` obligations: λ ≥ 2 for general m, an α = 2 pigeonhole tail, and the finite W1 bridge into kernel `decide`.
- **Verification (diagnostic Python).**
  - Brute force on D_m for m = 2..7: the failing roots are exactly A.
  - An independent finite certificate (C1 to C4) and a monotone subset form over all 128 subsets T ⊆ W1.
  - The prescribed good pairs (B_s^+, B_t^-) all EXIST in D_m, so this is not the known good-pair obstruction W of arXiv:2003.02107.
- **Prior art.**
  - The published version (Graphs Combin. 38 (2022) 187) keeps Conjecture 35 verbatim.
  - No refutation was found online.
  - The cited paper has only a single α = 2 example (W) plus families with α = 3 and α ≤ 7.
  - Path screens of the registries are clean: OpenAI HEAD 4eaee875 unchanged; Omega HEAD a41b3dc7, whose 19 changed files since 86172888 are all irrelevant.
- **Honest risks for root.**
  1. The gadget is the source's W1, and case e = p1 is exactly the source's Theorem 19(b). The new content is the co-bipartite gluing that makes arbitrarily large α = 2 counterexamples, together with the crossing argument. This is a plausible "routine bridge" objection.
  2. Only the rooted version is refuted. Conjecture 34 (some root) survives, because D_m has good roots in B.
  3. In the two-block design, W1 is the unique gadget for b ≤ 5. Exhaustive checks: 24 labelings at b = 4, none at b = 5 (55,404 digraphs and 6,060,075 attachments).
- **Lean cost.** Moderate. The finite parts go by `decide`; the general-m parts are the crossing lemmas (drafted) and 2-arc-strong connectivity (outlined).

## Other 19 IDs

| ID | Disposition |
|---|---|
| 347274 Mondrian | PARKED after investigation. The only-if direction is the source's own Lemma 2.1 and Propositions 2.1 and 2.2. Proper partitions are open for k ≥ 9 (the source has only k = 7, 8). The published DM 2021 version keeps the conjecture; no later resolution was found. Remaining lemma: a uniform proper layout with provable non-congruence for all k. Lean cost is high (analytic, all k). |
| 329890 Harvey–Wood 2-regular minors | PARKED. All-odd case and asymptotics known (Csóka–Lo–Norin–Wu–Yepremyan; arXiv:1903.03908). Split and blow-up lower-bound analysis gives no violation outside the excluded cases. |
| 341359 Dross–Havet | EXCLUDED, known: Benford–Montgomery, arXiv:2103.06229 (JCTB 2022). |
| 343364 avoidable induced paths | EXCLUDED, known: Bonamy–Defrain–Hatzel–Thiebaut, EJC 2020. |
| 343498 planar equitable vertex arboricity | EXCLUDED, known: Esperet–Lemoine–Maffray 2015 (the record says so). |
| 348099 subgraph entropy | EXCLUDED, known: Aougab–Clay–Hamed, arXiv:2506.18838 (exact Conjecture 1.6). |
| 354329 high-girth Steiner systems | EXCLUDED, known: Kwan–Sah–Sawhney–Simkin. |
| 340023 fractional EH, girth | PARKED. Only the odd-girth analogue is proved (arXiv:2608.02522). |
| 340024 Mohar–Wu weakening | PARKED (deep). |
| 338234 Kanté–Kwon | PARKED (deep). |
| 341385 Chen–Chvátal | PARKED (famous). |
| 342566, 346147 Kelly | PARKED (famous; these two are essentially duplicates). |
| 344219 list linear Hadwiger | PARKED (famous). |
| 344401 majority colouring | PARKED (contains the majority 3-colouring conjecture). |
| 346570 many flows (orders 6, 7) | PARKED (asymptotic; open). |
| 355847 pseudocircle triangles | PARKED (n = 8 enumeration not feasible under the caps). |
| 381276 contact-number stability | PARKED (analytic). |
| 382235 Hamiltonicity complexity | PARKED (algorithmic). |

## Files

- `extracted.json` and `raw/*.jsonl`: exact literal lines, with chunk, line, chunk/raw/statement hashes.
- `results.json`: 20 ID-keyed entries with provenance and source receipts.
- `sources/`: PDFs and texts; abstract receipts; the published Springer HTML; the cited paper arXiv:2003.02107; the Mondrian published PDF; Omega compare; registry HEAD JSON.
- `scripts/`: extract, context, fetch and limited (copied from r134; grep replaces rg); spiral; branching; gadget*; goodpair_check; assemble_results.
- `logs/`: full outputs and resource receipts for every numerical run.

Zero credit unless root accepts; I do not self-accept.
