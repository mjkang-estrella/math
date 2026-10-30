# T117Q manuscript closure review, round 3

Role: independent manuscript closure gate, round 3 (Factory Opus 5.5), as a fresh delegated
review. It is not a continuation of the round-2 backing thread. This directory is the only
location written. Source theorems at OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
remain stipulated.

No acceptance, count, ledger, staging, commit, author-packet edit, upload or publication
action was taken. No nested agent was used. The author repair receipt and the parent v3
preflight were read as context. Neither substitutes for this gate.

## Verdict

**PASS_FULL_MANUSCRIPT_T117Q**

- **R1 is closed.** v3 applies the first fix that round 2 allowed: `-{}-` inside `\texttt`.
  All four options print and extract as ASCII `--`. The printed PDF command, run exactly as
  printed on a fresh /var/tmp copy, builds the packet PDF byte for byte.
- **No other change.** I checked that the only source change is four 2-byte `{}` insertions.
  No other byte of main.tex differs from v2.
- **No regression.**
  - The build is clean and has 16 pages.
  - The rendered pages other than p.14 are pixel-identical to v2 at 80 and 150 dpi.
  - The text layer differs from v2 only in the Reproduction paragraph.
  - The changed page was inspected visually.
- **Mathematics and other obligations.** I did not re-derive the mathematics. Every
  mathematical, attribution, scope and formal-coverage sentence is byte-identical to the v2
  text that round 2 audited in full. For that text I rely explicitly on round 2's full-scope
  audit, as the brief permits:
  - the full frozen Theorem 1.1;
  - proof E1–E8, contribution RQ1–RQ4 and editorial E1–E5;
  - R2-A–D, with the M1 classical attribution;
  - the new-in-v2 GMN Question 3 sentence;
  - §9 formal coverage.
- **Remaining items.** Round 2 stated that no other required item remains once R1 is repaired
  with no other change. No genuine new defect was found. There are no required repairs.

This is a manuscript-gate verdict only. It is not an acceptance or count judgement.

## Inputs authenticated (identity only)

All 21 anchors given in the brief were recomputed as SHA256 and match. This covers the v3,
v2 and v1 manuscripts, the round-1 and round-2 review manifests, and the prior gates:
r59 MANIFEST, candidate and original-scope; proof-r1; contribution-r1 and r2; the
parent-literature manifest and response; formal-v1; and formal-review-r1. Exact values are in
evidence.json under `external_anchors_verified`, together with 20 further context files.

| File | SHA256 |
|---|---|
| v3 manifest.json | 46a52140…f865 |
| v3 main.tex | d42ec3ad…83f1 |
| v3 main.pdf | 80b522c8…3c49a (16 pages) |
| round-2 MANIFEST.json | 005d7a52…18ae |
| v2 manifest.json / main.tex / main.pdf | 7da5998a…d518 / 9ed9f7dd…7c13 / adcc1c36…2fa8 |

Read-only verifier replays (scripts read first):

- **v3 verify.py.** It accepts the external anchor (exit 0) and rejects an all-zero anchor
  (exit 1, "external anchor mismatch").
- **Earlier packets.** v2 and v1 verify.py accept their anchors. These packets are untouched.
- **Round 2.** Its verify_review.py accepts its package against anchor 005d7a52… with `--repo`,
  which rechecks all of its recorded external inputs.
- **Copied round-2 report.** `inputs/t117q-manuscript-review-r2/` in v3 is byte-identical to
  the round-2 directory (`diff -r`).
- **v2-history.** All 14 files in `v2-history/` are byte-identical to the corresponding v2
  packet files. `v1-history/` and all pre-existing `inputs/` are identical to v2.
- **Scripts.** build.py, verify.py, integrity_controls.py and LICENSES.md are byte-identical
  to v2.
- **Author controls.** I read integrity_controls.py, then ran it on a fresh /var/tmp copy.
  Of 15 cases, only `positive` was accepted, and each rejection gave its expected reason. The
  output equals the packet receipt except for the receipt's added `preliminary_manifest_anchor`
  field.

The v2→v3 packet inventory difference, computed from the two manifests, is exactly:

- **Changed:** main.tex, main.pdf, README.md, reading-limits.md, packaging-provenance.json and
  the regenerated validation/ files.
- **Added:** inputs/t117q-manuscript-review-r2/ (7 files), v2-history/ (14 files),
  validation/v2-to-v3.patch, validation/v2-to-v3-text.patch and private/v3-page14.png.
- **Moved:** validation/v1-to-v2.patch, now under v2-history/.

No other packet file changed. Checksums are identity evidence only, not mathematics.

## Exact source change

I computed this independently from the frozen v2 and v3 files.

- **Line diff.** `diff` shows only lines 945, 949 and 950 (1068 lines in both versions).
- **Byte operations.** The byte-level edit operations are exactly four insertions of `{}`, at
  v2 offsets 44372, 44602, 44621 and 44641. There are no deletions or replacements, and the
  file grows from 51644 to 51652 bytes.
- **Reconstruction.** Replacing each of the four unique strings `build.py --output`,
  `\texttt{--output}`, `\texttt{--lean}` and `\texttt{--cache}` in v2 with its `-{}-` form
  reproduces v3 exactly (SHA256 d42ec3ad…). The author's validation/v2-to-v3.patch shows the
  same three lines.
- **Remaining `--` sequences.** The 20 remaining `--` sequences in v3 are intended en dashes
  in ranges, author pairs and page ranges (lines 106, 143, 714, 719, 723, 731, 738, 744, 794,
  903, 923, 1027, 1031, 1035, 1041 and 1056). None is inside `\texttt`, `\path` or a command.
- **Encoding.** Neither version contains non-ASCII bytes.

The four changed lines are inside the non-mathematical Reproduction paragraph (§9). They
change no claim. The sentence structure, option names and paths are unchanged.

## R1 closure checks

1. **Text layer.** I extracted the v3 packet PDF, p.14, with both `pdftotext -layout` and
   `-raw`.
   - The command line reads `python3 -B build.py --output /var/tmp/NEW-PDF-BUILD` in pure
     ASCII.
   - The formal sentence reads `--output, --lean and --cache`.
   - The Reproduction paragraph contains no U+2013, U+2014 or U+2212. Its only non-ASCII
     character is the U+FB01 "fi" ligature in "specifies", which is also present in v2.
   - Over the whole document, the text diff against v2 is confined to text lines 779 and
     782–784. Those lines differ only in the four dash pairs and in the leading layout spaces
     on lines 782 and 784.
2. **Literal execution.**
   - The author's earlier output directory /var/tmp/NEW-PDF-BUILD already exists, and build.py
     refuses an existing directory.
   - I therefore ran the command string extracted from the PDF exactly as printed. It ran
     inside a private user and mount namespace in which /var/tmp was bind-mapped to an empty
     scratch directory holding a fresh packet copy.
   - It exited 0. Its receipt records source d42ec3ad… and PDF 80b522c8…, byte-identical to
     the packet main.pdf.
   - The author's /var/tmp/NEW-PDF-BUILD was not touched.
3. **Second fresh build.** The documented build with a fresh output path, on another fresh
   copy, also gives PDF 80b522c8…, a clean main.log, and text identical to the packet's
   validation/main.txt and to the literal-command build.
4. **Negative control (R1 reproduced on v2).** The v2 p.14 command extracted from the frozen
   v2 PDF is non-ASCII (`–output`). Run literally the same way on a v2 copy, it exits 2 with
   "the following arguments are required: --output" and writes nothing. This confirms that
   the fix, not the test setup, is what makes the command work.
5. **Formal options.** The printed formal tokens are {`--output`, `--lean`, `--cache`}. They
   equal the argparse declarations of t117q-formal-v1/rebuild.py (SHA256 e767e8fd…, lines
   26–28). `rebuild.py --help` on a /var/tmp copy of the script lists exactly these options.
   No Lean rebuild was run, because none is needed for this check.

## No-regression checks

- **Build.**
  - Tectonic 0.17.0 (binary SHA256 a98aa59a…, matching the receipt), SOURCE_DATE_EPOCH
    1792281600, exit 0.
  - main.log has no warning, overfull/underfull box or undefined reference. The only line
    matching "warning" is the infwarerr package description.
  - There is no `??` in the text.
  - pdfinfo reports 16 letter pages.
  - pdffonts lists 24 fonts, all embedded and subset. The font set and ToUnicode flags are
    identical to v2's.
- **Page identity.** I rendered all 16 pages of v2 and v3 at 80 dpi and at 150 dpi and
  compared the pixels.
  - Pages 1–13 and 15–16 have no differing pixel at either resolution.
  - p.14 differs only within the Reproduction paragraph: bbox (77,465)–(576,531) at 80 dpi,
    (145,872)–(1081,996) at 150 dpi, and (193,1163)–(1441,1328) at 200 dpi.
- **Visual inspection.**
  - I viewed v3 p.14 in full at 150 dpi, and the changed region side by side with v2 at
    200 dpi.
  - The command and all three formal options show two hyphens. There is no clipping, overlap
    or reflow beyond the paragraph, and the line breaks are unchanged.
  - "--cache" at the start of a line sits about 2.5 pt into the left margin. This is
    microtype character protrusion of a leading hyphen, which the v2 en dash also had to a
    lesser degree. It is intended margin kerning, not an overfull box (the log has none), and
    it is not a defect.
- **Unchanged pages.** Pages other than p.14 were not visually re-inspected. They are
  pixel-identical to the v2 pages that round 2 viewed one by one.

## Reliance on round 2 for unchanged text

Every article byte outside the four `{}` insertions is identical to v2 main.tex 9ed9f7dd….
Round 2 audited that text in full, re-derived the standalone proof of the full frozen
statement, checked the M1 attribution and GMN Question 3 against the GMN primary, checked the
JLW/MN √d/64 deduction, and confirmed every prior required objection. It found no gap. I read
that complete report and its reading limits, and I rely on it for these items. I did not
repeat that derivation or any primary reading in this round.

The preserved obligations are:

- **Full target.** Genuine finite negative-type metrics with n_j → ∞; every complex Hilbert
  space H, including infinite-dimensional and nonseparable ones; every 1-Lipschitz
  F: V_j → S₁(H); and ordered uniform first-pair averages with constant c^{-1} and exponent
  9/2. There is no weighted, pseudometric, rank or bi-Lipschitz substitute.
- **Proof items.** Proof E1–E8, contribution RQ1–RQ4, editorial E1–E5 and R2-A–D.
- **Attribution.** M1, the classical Bourgain 1987 / Tomczak-Jaegermann 1974 attribution
  through GMN §1.3, with the unread originals disclosed.
- **Formal coverage.** The §9 coverage limits.
- **Literature priority.** The bounded new-to-project wording, with no claim of literature
  priority.

All of these remain exactly as round 2 found them. The repair cannot have affected them,
because no byte of their text changed.

## Required repairs

None.

## Optional editorial (carried, not required)

Round-2 optional items O3–O7 remain optional and unimplemented, as the brief allows:

- **O3.** Published bibliography versions of NPS, CEE and GMN.
- **O4.** R2 optional E1 and E3.
- **O5.** The ceiling notation for Bourgain's grid side.
- **O6.** Harmonizing "sharp metric-cotype grid bound" on line 100 and Appendix line 1008.
- **O7.** A more explicit Question 3 corollary.

No new optional item is raised.

## Observations (not repair items)

- **Unrecorded v3 builds.** The repair receipt's claim of a second byte-identical author
  build is stated, not recorded. The `build-history/` files are pre-v3 iterations, unchanged
  from v2. I reproduced two fresh builds independently, so nothing rests on the author's claim.
- **Output path.** The printed command uses `/var/tmp/NEW-PDF-BUILD`, while the v3 README
  uses another fresh path plus `--tectonic`. The manuscript sentence already says "with a
  fresh output directory and an explicit Tectonic option if needed", and round 2 accepted it
  apart from the dashes. This is unchanged and not a defect.

## Limits

See reading-limits.md. Hash, build, text-extraction and render checks are identity and
typesetting evidence only. They are not mathematical evidence and were not used as such.

## Package

Members:

- review.md;
- reading-limits.md;
- evidence.json;
- verify_review.py;
- review_controls.py;
- controls-result.json, generated on /var/tmp copies of the pre-final seal. It holds 27
  cases: 18 identity, 3 external-input and 6 closure cases. Each closure rejection exercises
  one closure check (reverted source, extra source change, en-dash PDF, renamed formal option
  and closure anchor);
- MANIFEST.json, which seals the others.

Verify identity with
`python3 -B verify_review.py verify <dir> --anchor <SHA256 of MANIFEST.json>`, taking the
anchor from outside the package. Add `--repo <openai-proof-research root>` to recheck all 41
external inputs listed in evidence.json.

`python3 -B verify_review.py closure <dir> --anchor <…> --repo <root>` also re-runs the R1
closure checks read-only. It checks the four-insertion reconstruction from v2, the ASCII
options in the p.14 text of the v3 PDF (using pdftotext to stdout), and the option names
against build.py and rebuild.py. Closure anchors are checked last.

The final seal adds only controls-result.json to the pre-final base. Final positive and
wrong-anchor checks are reported outside the package.
