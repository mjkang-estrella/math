# Reading and search limits (contribution review r1)

Acquisition is not reading. Line numbers refer to the files named, as numbered by the file-read tool. Third-party PDF texts are `pdftotext -layout` output (poppler 26.01.0). Each such text reproduces byte-identically from its retained PDF; hashes are in `retrieval-receipts.json`.

## Author packet (fresh-structural-discovery-r61, immutable)

Read in full: candidate.md, original-scope.txt, tensor-mechanism.md, checkpoint.md, report.md, primary-comparison.md, reading-limits.md, formal-scope.md, provenance.md, verification.md, screen236.md, LICENSES.md, .gitignore, history-and-input-references.json, primary-receipts.json, checks/extraction-replays.json, checks/integrity-controls.json, verify.py, checks/integrity_controls.py, checks/finite_diagnostics.py. Not run: seal.py (never run on a frozen packet). Intake (`t247g-intake/`) and parent (`t247g-parent/`) briefs and adoption files were read; intake `verify-intake.py` passed with anchor 63f2d578….

## Pinned source (fd4aeeb2…, retained author copies, identities rematched against preprints-tree.json)

Principal `An-infinite-finitely-presented-periodic-group-September-23-2026/build/`:
- `sections/cancellation.tex`: read in full, lines 1–609 (tool count 610 including the final line). Lines 370–449 and 1–15 (`ca:D`) were reread for this report.
- `sections/finite-rules.tex`: read lines 1–160 and 615–914 (800–844 reread). NOT read by this reviewer: 161–614 and 915–1048. The classification uses only the parameter interface at 63–83, 146–157, 655–670 and 804–830. The internal correctness of the unread compiler sections is a proof-gate matter, stipulated for the source and assumed for Lemma 1.
- `paper.tex`: lines 60–312.
- A term grep over all family-247 TeX files (tensor, absorb, GK/Gelfand, growth, coefficient) found no absorption corollary. This is a lexical check, not a semantic reading of every file.

Companion `An-infinite-finitely-presented-residually-finite-2-group-October-5-2026/build/sections/`: `ring-phases.tex` read in full (1–231) and `introduction.tex` read in full (1–155). Other companion sections were covered by the grep only.

Upstream catalogue: `sources/CONTENTS.md` family-247 entry (and family 201 for comparison). The pinned `lean/docs/247.md` (blob 48b7524f) and both family READMEs (blobs 757a9e1c, 46de52c6) were read in full. The two READMEs match `preprints-tree.json`. `lean/docs/247.md` is outside the preprints tree and is authenticated only by the commit-pinned raw URL.

## Primary bodies

| Body | Read ranges | Not read |
|---|---|---|
| DRS2012 JCSS 78 (author-retained; text reproduces) | text 349–445 (§2.3), 652–831 (§5 incl. Theorems 5–7) | all else |
| Smoktunowicz arXiv 1403.2557v1 (fresh download byte-identical to author PDF, SHA256 e457258f…) | text 1–190, 410–909 (§§5–8, start of §9), 1975–2080 (end, references) | 191–409 (most of §4), 910–1974 (most of §§9–12) |
| Smoktunowicz 2008 BLMS 40, Edinburgh Pure version of record with cover sheet | text 1–165 (§1, Theorems 1.1–1.2), 455–739 (§§6–8, references) | 166–454 (§§2–5) |
| arXiv 2609.07996v1 (Adamczewski–Böhmler–Marczinzik) | text 1–260 (§1, §2 incl. Theorem 1.1, Lemma 2.3, Proposition 2.4, start of §3), 1040–1109 (contribution statement, references); single grep-hit lines 155, 388, 562–564, 706 | 261–1039 (§§3–6 detailed proof) |
| arXiv 2609.15080v1 (Greenfeld–King–Vendramin) | text 1–110 (§§1–3 start, Theorem 1.1, Lemma 3.1 statement); reference list lines 287–301 | 111–286 (proofs, Proposition 6.1) |

The arXiv abstract pages of 2609.07996 and 2609.15080 were also read. Krempa 1972 and 1979, Schützenberger 1961, Lawrence 1991, Bergman 1989, Puczyłowski 1988/1993, Chebotar–Ke–Lee–Puczyłowski 2013, Ferrero–Puczyłowski, Lenagan–Smoktunowicz(–Young) and math/0505141 were NOT read. They are known only from citations or search-result snippets, and no result is drawn from them.

Failed retrieval: one earlier attempt for Smoktunowicz 2008 through a different endpoint returned a 5927-byte Cloudflare "Just a moment" HTML page (SHA256 6c398d14…). It is not retained and was not used.

## Web search (bounded)

Several web searches were run before a context compaction. The exact query strings were not preserved. The topics were: tensor products of nil algebras and radicals; nil algebras over polynomial-growth or finite-GK coefficient algebras; finitely presented nil algebras and tensor products; Köthe conjecture 2026; Bergman/Puczyłowski/Krempa tensor-radical results; Smoktunowicz 2008 retrieval. The leads found are listed in review.md §10. A bounded search cannot establish new-to-literature priority.

## Project history

Read passages: `frontier/iterations/i07-structures.md` Candidate C; `proposals/algebra_geometry.md` around line 129; `fresh-structural-discovery-r15/screening.md` item 3 and r15 reading records; `frontier/scouts/discrete.md` §6; r32/r39 history-index family-247 entries; `screen236.md`.

Focused search, re-run for this report (from the repo root):

    rg -n -o -P '(?i)k(ö|o|oe)the|krempa|\bnil\b[^\n]{0,80}(⊗|\\otimes|tensor)|(⊗|\\otimes|tensor)[^\n]{0,80}\bnil\b|finitely presented nil' \
      -g '*.md' -g '*.tex' -g '*.txt' -g '*.json' \
      --glob '!**/private/**' --glob '!**/inputs/**' --glob '!**/primary/**' --glob '!**/pinned/**' \
      --glob '!**/upstream/**' --glob '!**/literature/**' --glob '!**/snapshots/**' \
      --glob '!**/*preprints-tree.json' --glob '!**/CONTENTS.md' \
      --glob '!frontier/campaigns/2026-10-14/t247g-*/**' \
      --glob '!frontier/campaigns/2026-10-14/fresh-structural-discovery-r61/**' --glob '!sources/**' .

The hits were only catalogue-title lines (i07 catalogue-selected, i37 catalogue-audit, i07 broad-screen-headings, r31/r39/r64 title lists), a source-paper text copy under i79 `outside/`, and NEW-TEN line 1452 (the T247G entry). A broader pattern that included "tensor product", "absorb" and "GK" matched 3151 files dominated by unrelated uses. It was not read file by file.

Disclosure: an earlier anchor-string grep over `t247g-*` matched lines in `t247g-proof-r1/author-replay.json` (anchor strings only). No other content of that parallel review was read or used.
