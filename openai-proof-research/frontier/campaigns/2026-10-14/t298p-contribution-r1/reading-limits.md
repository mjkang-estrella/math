# Reading limits — T298P contribution review r1

Not read: any proof-gate output. No `t298p-proof*` path was opened, and `t298p-parent/proof-r1-brief.txt` was not opened. Only my own brief, `t298p-parent/contribution-r1-brief.txt`, was read, together with the parent's `intake.json`, `dispatch-r1.json` and `reading-and-interface-intake.json`. These are dispatch and intake records written before any review, and they contain no verdict.

## Author packet (fresh-structural-discovery-r104; all hash-authenticated by the author verifier)

**Read in full:**

- candidate.md
- scope-freeze.md
- scope-status.json
- comparison.md
- reading-limits.json
- stress-checks.md
- finite-entropy-chart.md
- normal-slice-construction.md
- matched-volume-attempt.md (A–G)
- unconditional-score-construction.md (1–5)
- encoding-attempt.md (1–5)
- MANIFEST.json
- primary-receipts.json
- source-receipts.json
- progress.json
- reproduction.md
- verify.py (read before execution)

**Not read or executed by me:** coarse-diagnostics.py and .json, volume-normalization-diagnostics.py and .json. They are hash-authenticated only. The parent reports reproducing them, and my C1–C5 are independent.

## Pinned sources (private copies, verified against git blobs by the author verifier)

**Source298, read in full:**

- README.md
- paper.tex
- sections 01-introduction, 02-conventions, 03-fisher, 04-signal, 05-flow, 06-blocks
- references.tex

**Companion287:**

- Read in full: README.md, sections/entropy-dimensions.tex, sections/amplification.tex.
- Read via grep: main.tex theorem statements (thm:rank-step, thm:main).
- Not read: cocycle.tex, flow.tex, generation.tex, preliminaries.tex, references.bib, figures.

**Relative generation and the generator problem for finite factors (Sept 23 2026):**

- Fetched at the pinned commit from raw.githubusercontent.com into scratch /var/tmp/t298p-c1-gen-src. Git blobs were matched against preprints-tree.json.
- Read in full: README.md, build/sections/introduction.tex, build/sections/consequences.tex.
- Not read: generation.tex, independence.tex, perturbation.tex, main.tex, preamble.tex, references.bib, paper.pdf.

**Pinned catalogue:** preprints-tree.json directory names were screened by keyword (749 preprints). sources/CONTENTS.md was grepped for entropy, Fisher, von Neumann and generator entries. No other pinned free-entropy preprint was found.

## External primary bodies (private, receipt-matched)

- **Shlyakhtenko math/9812079v1 (shlyakhtenko-relative.txt):** all 763 lines read. This covers Definitions 2.1–2.3 and 2.10, Remarks 2.4 and 2.11, Propositions 2.5–2.18, Theorems 2.15, 2.17 and 2.19, Corollary 2.20, §3, §4 (Theorem 4.1, whose proof is omitted in the source, Proposition 4.2, Theorems 4.3–4.6) and §5 (Theorem 5.1 with its proof).
- **Nica–Shlyakhtenko–Speicher math/9809081v1 (nica-shlyakhtenko-speicher.txt):** all 644 lines read. This covers §2, Lemmas 2.6–2.10 and Theorem 2.1 with proofs, Proposition 2.11, and Theorem 3.1 with its proof.
- **Nica–Shlyakhtenko–Speicher math/9809080v1 (nica-fisher.txt):**
  - Read: lines 1–60 (abstract and introduction start) and 1180–1380 (Proposition 4.1 with its proof, (4.4)–(4.5), and the start of the proof of Theorem 1.3).
  - Not read: lines 61–1179 and 1381–1769, including Remark 2.6. Remark 2.6 is relied on only as quoted at lines ~1225–1229: Φ*({A,A*} : M_d) ≥ Φ*(A,A*).

## Literature screen (bounded; snippets and abstracts are not theorem evidence)

**WebSearch queries:**

1. two-variable χ/χ* counterexample (extended)
2. M_k(M) amplification relative to matrix units
3. "finite-entropy separation" 2026 (extended)
4. orbital free entropy with matrix units
5. 2026 two self-adjoint χ < χ* (extended)
6. inner derivations and unconditional Fisher information in M_k(A)
7. reduction to two generators and the unification problem
8. Shlyakhtenko M_k compression and the Schreier formula

**WebFetch, abstract pages only:**

- Dykema funct-an/9605005 (not relevant)
- Ueda 1610.04118
- Jung math/0410594 (Lemma 3.1 seen only via search snippet)

**Snippets only:** 2201.09503, math/0702745, 1210.6421, 2305.02574 (Jekel–Pi), 2510.07558.

No two-variable finite gap and no unconditional finite-part matrix-amplification formula for χ or χ* was found. Absence is not clearance.

## Campaign history

**Scope:**

- NEW-TEN-2026-10-14.md: lines 1–200 and 1700–1832 read, plus every grep hit for 298, T298P, r104 and free-entropy terms (lines 803 and 1168 context). Lines 201–1699 were not read except through grep.
- frontier/RESULTS.md: does not exist.
- frontier/iterations and campaigns/2026-10-14: grepped for free-entropy, microstates, χ*, Fisher, Shlyakhtenko, R-diagonal and Voiculescu terms, and for family298/source298/T298P, matrix units, two generators, normal slice and gauge orbit. Excluded: private, inputs, frozen, r104 and t298p-* directories.

**Results:**

- Every hit was inspected in context.
- The only substantive prior family-298 record is fresh-analytic-discovery-r20, entropy-obstruction.md and checkpoint.md, read in full. It concerns noise persistence and maximal terminal microstates and contains no variable reduction.
- The remaining hits are catalogue listings or unrelated uses of "near-diagonal", "chi chi*" or "scores".
- frontier/sources/* catalogue copies were not opened.
