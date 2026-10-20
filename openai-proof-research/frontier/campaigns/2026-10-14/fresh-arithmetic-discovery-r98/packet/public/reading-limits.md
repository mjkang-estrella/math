# Reading limits, arithmetic r98

## Read in full

- `AGENTS.md`; the r98 brief and the common research brief (both copied to `private/history`).
- r97 `REPORT.md`, public `report.md`, `screens.md`, `reading-limits.md` and `discovery-arithmetic-r97-parent/intake.json` (copied). The r97 `FINAL.json`, `integrity-results.json`, `verify.py` and `controls.py` were inspected as templates and are not copied.
- Pinned family 009 mod-$p$ source: `main.tex`, `sections/01-introduction.tex`, `sections/02-symbols.tex`, `sections/05-fields.tex` (retained under `private/upstream`, blob-checked).
- Primary: Carter–Vogt, PNAS 77(7):3756–3757 (1980), both pages from scanned page images, all four columns transcribed in author notes.
- Primary: Machala, Čas. pěst. mat. 100 (1975) 142–154, read through a text extraction of the DML-CZ PDF. Formulas were checked against the theorem and definitions; OCR noise in symbols was resolved by context.
- Survey: Havlicek, arXiv:1210.2053v1, read through a text extraction.

## Read in part

- Pinned Bogomolov–Pop `build/local-theory.tex`: lines 1–180 only (ℓ-adic setting; not used).
- Pinned Lech `build/main.tex` and `build/sections/charp.tex`: read during family screening. The exact line extent was not re-verified after a context summary. Not used by any derivation; local copies removed.
- `sources/upstream.json`, the catalogue and project history: navigation only.

## Fetched but not read

The remaining 14 fetched pinned files (other Lech sections, mod-$p$ `03-intersection.tex`, `04-lines.tex`, `references.bib`, mod-ℓ `main.tex`, `01-introduction.tex`, `02-local.tex`, Bogomolov–Pop `introduction.tex`) were not read this round and are recorded as removed in `source-register.json`. In particular the mod-ℓ companion was not read in r98. r97 read the mod-$p$ sections 03 and 04.

## Not obtained

- Carter–Vogt, Mem. Amer. Math. Soc. 27 No. 235 (1980): the proofs of the PNAS announcement, including the reduced-lineation classification.
- Radó, Math. Z. 110 (1969) and the 1970 paper cited by Carter–Vogt.
- Brezuleanu–Rădulescu, J. Geom. 23 (1984).
- Klingenberg, Skornyakov, Garner and Schilling are known only as citations.

So the Carter–Vogt plane classification is used only as an announced statement and never as a proved input. Theorem D uses Machala's theorem, whose proof was read. Machala's Satz 1–2 are cited by him to Radó; Theorem D uses them only in the commutative case, where they are standard valuation facts.

## Provenance gaps

- The exact retrieval URLs for the PNAS page images, the Machala PDF and the Havlicek PDF were not retained. Identifiers (DOI, PMC id, DML-CZ persistent URL, arXiv id) and SHA256 values are in `primary-register.json`.
- A scratch file `/tmp/r98fam.txt` (catalogue titles only) was created outside the root early in the round and immediately deleted. The tool harness also auto-saved one long text-extraction listing under `/tmp/droid-terminal-*`; this was harness behaviour, not an author write.

## Pre-seal changes

`public/report.md` was written once before sealing. Author notes and scratch (page crops, text extractions, register builder) stay outside the packet under `work/` and are not sealed.
