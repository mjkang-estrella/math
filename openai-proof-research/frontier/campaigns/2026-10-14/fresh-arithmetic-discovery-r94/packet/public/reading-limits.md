# Reading limits, provenance and timing

## Runner record

The first runner was GPT-6 Astra. It was stopped by the user during prefreeze screening. This resumption is Factory Droid (Opus 5.5, high) and records that provider and model wherever the provider is recorded. I treated the prior runner's acquisitions as inputs, re-checked their bytes, and re-derived their conclusions rather than trusting them.

## Canonical sources

There are 45 canonical non-PDF blobs. All are checked against the complete `sources/preprints-tree.json` (13,223 entries, not truncated, SHA256 `eeecc1da…09b`), with pinned raw URLs, Git blob IDs and SHA256 hashes (see source-register.json).

- 36 were acquired by the prior runner: source249 (8), 250 (10), 063 (8) and 164 (10).
- 9 were acquired by this runner: source321.
- All 45 are retained.

## Reading depth by source

- **249.** Introduction, `sec:degree` (complete), `sec:transport` (complete), `geometry.tex` lines 1–160 (seed, residual finiteness, start of the cubical cover), `presentation.tex` lines 1–60 (theorem statement and outline), and `conclusion.tex`. The proofs of `lem:aligned-presentation`, the quadratic estimate, finite-quotient solvability, compactness and `prop:model` were not reread. They are stipulated and are not used by my limitations except through the stated theorems.
- **321.** Introduction, the plus construction and `04-construction`, as displayed. Output truncation hid about 235 lines in total: 47 of the introduction, 38 of the plus section and 150 of the construction (the presentation and the boundary-matrix calculation). Also read: the `thm:tower` and `cor:torsion` statements and the final proof of `thm:main`. The tower proof body and `lem:cyclic-cover` proof were not read in full.
- **250.** Envelope introduction only.
- **063.** Introduction only.
- **164.** Bodies not semantically reread by this runner.

## Primary sources

There are three successful primary pairs. Fujita v2 and v3 returned 404 (recorded).

- **Leary–Petrosyan, arXiv:2605.07853v1.** Abstract, introduction, Corollary 1.4, §5.4–§5.6 (Corollaries 5.14, 5.15 and 5.21) and references were read. The prior runner's page-20 render was viewed. §§2–4 were not read.
- **Leary, Math. Ann. 2018.** Opening, Theorems 3.1–3.4 and the surrounding paragraph were read.
- **Fujita, 1206.2475v1.** Introduction through Corollary 1.9 and the notation section were read. Sections 3 and 4 were not read, and the base paper [Fjt12] was not acquired.

The Fujita renders made by the prior runner were not viewed by this runner.

Classical facts used without primary acquisition:

- Neumann's finite normal generation of kernels between finitely presented groups;
- residual torsion-free nilpotence of right-angled Artin groups (Duchamp–Krob);
- Malcev's theorem;
- Davis complex structure (Davis 2008), cited from memory with the standard statements. Treat these as the reviewer-checkable classical inputs of Proposition L1 and §4 of eg-route.md.

## History

Eight history copies and three context copies are kept privately (context-register.json). They were read at these extents:

- **i07 Candidate B:** complete section.
- **structural r90 screen321:** complete.
- **arithmetic r35 scope250p:** first 1,500 bytes.
- **T250P contribution review:** first 2,500 bytes (verdict section).
- **structural r35 mixed164:** first 2,000 bytes.
- **arithmetic r1 candidate:** first 2,500 bytes.
- **R034 finding:** search-hit lines only.
- **arithmetic r18 reading.md:** search-hit lines only.

The required latest archives named in the brief (r89–r93 bodies) were not reread in this resumption. This runner relied on the brief's own summaries of those archives. None of their mechanisms (source195, 058, 247, 202, 064, 209, 200, 193) was touched.

## Search

The prior runner's hit lists are kept in `private/search/` (`initial`, `volume`, `coxeter`, `hindman`). Its search strings were not recorded, so these are navigation only.

This runner's final alias search was `rg -c -i --hidden --no-ignore` over the whole project with no size cutoff. It excluded `.git`, `.venv`, `.lake` and `node_modules` dependencies and this round's own directory. Patterns: Leary, Petrosyan, Davis complex, right-angled Coxeter, Gerstenhaber, Rothaus, log Fano, log generalized Mukai, height kernel, Bestvina–Brady, Eilenberg–Ganea, Whitehead asphericity/conjecture, D(2). It returned exit 0 with no errors and 1,242 matching files; counts are in `final-alias-counts.txt`.

Operative hits followed:

- i07 Candidate B;
- structural r90 / source321 (this is how source321 entered the round);
- the arithmetic r48 exclusion line;
- the R034 and r18 Mukai lines.

The remaining hits are catalogue copies, primary texts and inventories. Hits are not semantic reads and do not clear priority.

## Changes to the prior runner's files

Within the owned directory, this runner did the following:

- moved the prior runner's four hit files into `packet/private/search/`, with bytes unchanged;
- added registers and notes;
- deleted only its own temporary `work/` scratch, whose acquisition data is preserved in source-register.json.

An empty `controls/` directory created by the prior runner is left at the round root. `packet/public/canonical.json`, `context.json` and `primary.json` are the prior runner's original records and are left byte-unchanged.

## No priority claim

Proposition L1 and Criterion C are this runner's derivations. No worldwide novelty search was made, and they are not nominated.
