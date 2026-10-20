# Reading limits, arithmetic r100

This round ran in two session segments separated by a context compaction. Segment 1 did the brief/history reading, the family screening reads, and the first source fetches; its durable record is `notes/session-log.md` (unsealed, outside the packet). Segment 2 (current) re-read every load-bearing text and did the direction-A/B analysis. Extents below distinguish the two honestly.

## Read in full (segment 2; load-bearing)

- Pinned 024 source: `statements.tex`, `companion.tex` (both re-read line-complete this segment; `introduction.tex` read in full in segment 1).
- Pinned prime-arguments paper (family 182 companion): `introduction.tex`, `local.tex`, `descent.tex` (line-complete).
- Pinned integer intersective paper (family 182): `introduction.tex` (line-complete; re-read this segment).
- Ford, *The distribution of totients* (arXiv:1104.3264 lineage): the Section 7.3 passage on common divisibility of preimages (the sentence on \(k=6\) and on Carmichael's conjecture) and the Theorem 8 vicinity, re-read this segment from r2's retained text extraction (`private/history/ford-totients-r2-text-extraction.txt`, unchanged copy; retrieval record `ford-totients-r2-retrieval.json` from r2). No other part of Ford's text was read this round; the rest of r3's Ford usage is cited as r3 history only.
- Project history, segment 2: `t024w-proof-r1/report.md` (full); `totient-recovery-r3/checkpoint.md`, `scope.md`, `totient-recovery-parent/disposition.json` (full); i99 scout §1–§3 and §6–§7 (its AP/IP/PP/SF/OI screens and conclusion; the middle technical sections A1–A5/B1–B4 were read selectively around the screened targets).
- r78's `research.md` §2 (family 206 screen) at the start of segment 2.

## Read in full (segment 1; not re-verified line-by-line after compaction)

- `AGENTS.md`; the common brief and the r100 role brief; r99 parent `disposition.md` + `contribution-r1-adoption/adoption.json`; r99 author `scope-freeze.md`, `screens.md`, `reading-limits.md`, `report.md`; `t164f99-contribution-r1` `review.md` + `reading-limits.md`; NEW-TEN head; r93/r95/r98 parent assessments; r95 family-history counts (stale; navigation only); r85's family-142 screen and r96's 028/013/207/001 screens.
- Pinned family-008 manuscript: `README.md`, `build/paper.tex`, `build/references.tex`, `build/sections/01-introduction.tex` through `08-induction.tex` (screening reads; the grt-freeness conclusion is recorded in the session log).
- Pinned introductions/top-level files for screening: families 029 companion (simprim), 021, 012, 022, 025, 023, 030, 026, 020, 153, 160, and the 024 introduction named above.

## Read in part

- Pinned prime-arguments `tuples.tex`: lines 1–64 (slot/cycle/dimension definitions) and 495–511 (`eq:prime-thresholds`, `eq:small-prime-modulus`), plus targeted searches for the parameter occurrences. The reflection-positivity proofs in between were not read.
- `sources/CONTENTS.md`: the entries for families 001, 002, 004, 005, 006, 007, 008, 009, 010, 011, 012, 013, 014, 027, 159 (abstracts; navigation/screening).
- i99 scout: see above.

## Fetched but not read (removed before sealing)

- Pinned prime-arguments paper: `kernel.tex`, `lifts.tex`, `primes.tex` (fetched in segment 2 for the feasibility audit; superseded by the parameter-chain analysis; not read; removed).
- Pinned integer intersective paper: `tuples.tex`, `kernel.tex`, `lifts.tex`, `transfer.tex`, `induction.tex` (same disposition).
- A byte-duplicate of the integer paper's `introduction.tex` was fetched twice (two local names); one copy retained, one deleted. Recorded here since the fetch log is per upstream path.

Each removal is recorded with blob, size, SHA256 and reason in `source-register.json`; no removed file has a local copy.

## Not obtained

- Ford's paper as a rendered PDF (r2's text extraction was used; r2/r3 verified the PDF's SHA256, recorded in their receipts).
- Pollack–Pomerance–Treviño [PPT2013] (cited by the pinned companion's `lem:fiber-propagation` paragraph; not acquired).
- Lucier 2006, Rice 2013, Rice 2019, Arala 2024, Adajar et al. 2026, Green–Sawhney 2025, Bloom–Maynard 2022, Pintz–Steiger–Szemerédi 1988, Green 2024, Thorner–Zaman 2024, Li–Pan 2009, Erdős 1958, Maier–Pomerance 1988, and the QRH/zero-free companion (family 003) cited by the prime-arguments paper: citations only, never acquired (see `external-navigation.json`).

## Provenance notes

- All pinned source bodies were fetched from `raw.githubusercontent.com/openai/math` at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; every fetched file's git blob SHA-1 was verified against `sources/preprints-tree.json` (13223 entries, `truncated: false`) at fetch time, and every retained body was re-verified in segment 2 during packet reorganization.
- The tool harness auto-saved terminal output under `/tmp/droid-terminal-*` during segment 2 (harness behaviour, not an author write). No author scratch was written outside the round root.
- Author scratch, the reorganization/manifest builder scripts and the session log stay outside the packet under `work/` and `notes/` and are not sealed.

## Pre-seal changes

All public documents were written once before sealing. `packet/MANIFEST.json`, root `FINAL.json` and root `REPORT.md` were generated last, in that order; `integrity-results.json` was regenerated by the controls run after sealing and sits outside the packet.
