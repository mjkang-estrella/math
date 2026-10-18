# Reading limits: T117Q manuscript closure review, round 3

## Read completely

- **Rules and brief.** AGENTS.md, VALIDATION.md, t117q-parent/manuscript-review-r3-brief.txt
  and t117q-parent/manuscript-v3-preflight.json.
- **Round 2.** t117q-manuscript-review-r2/review.md and reading-limits.md, read in full.
  Its verify_review.py was read before it was run.
- **Frozen v3 packet t117q-manuscript-v3/.** The following were read:
  - README.md and reading-limits.md;
  - packaging-provenance.json and external-read-inputs.json;
  - validation/repair-receipt.json and validation/v2-to-v3.patch;
  - validation/v2-to-v3-text.patch, validation/visual-qa.json and
    validation/build-receipt.json;
  - build.py, verify.py and integrity_controls.py, read before running.
- **Exact source diff.** The complete v2→v3 main.tex difference was computed independently
  at line and byte level.
- **Changed page.** v3 PDF p.14 was viewed in full at 150 dpi, and its changed region side by
  side with v2 at 200 dpi.

## Read in part

- **Formal packet.** t117q-formal-v1/rebuild.py, lines 1–45 only (header and argparse). No
  Lean rebuild was run.
- **v3 main.tex.** Only the Reproduction paragraph (lines 942–953), the preamble (package
  list) and every line containing `--` were read directly. All other lines were established
  as byte-identical to v2 by byte-level comparison and were not re-read in this round.

## Explicit reliance, not re-derivation

The mathematical, scope, attribution, primary-interface and formal-coverage content of the
manuscript is byte-identical to v2 main.tex 9ed9f7dd…. For it, this review relies on the
complete round-2 audit (manifest 005d7a52…), disclosed here as reliance:

- the full standalone proof re-derivation;
- the M1 GMN §1.3 check and the GMN Question 3 check;
- the JLW/MN √d/64 deduction;
- the prior-objection table;
- the formal-coverage match.

In this round I did not re-read the full theorem or proof, and I did not read any primary
text (GMN, JLW, MN, CEE, LWW, KNT, NY, NPS or EGM) or pinned source body. I did not read the
Bourgain or Tomczak-Jaegermann originals; round 2 did not read them either, and the
manuscript discloses this. No literature or novelty search was performed.

Pages other than p.14 were not visually re-inspected. They are pixel-identical to the v2
pages, at 80 and 150 dpi, that round 2 viewed one by one.

## Replays (identity and typesetting only)

- v3 verify.py with the external anchor (exit 0) and with an all-zero anchor (exit 1). v2 and
  v1 verify.py with their anchors (exit 0). Round-2 verify_review.py with its anchor and
  `--repo` (exit 0).
- The author integrity_controls.py on a fresh /var/tmp copy: 15 cases, each with the expected
  reason.
- A fresh build with build.py on a /var/tmp copy, using a fresh output path.
- The printed command, extracted from the PDF text, run exactly as printed on another fresh
  copy. It ran inside `unshare -rm`, with /var/tmp bind-mapped to an empty scratch directory,
  because the author's /var/tmp/NEW-PDF-BUILD already exists. Both builds are byte-identical
  to the packet PDF.
- Negative control: the v2 printed (en-dash) command run the same way on a v2 copy failed
  with argparse exit 2.
- `rebuild.py --help` on a /var/tmp copy of the script.
- pdftotext (layout and raw), pdfinfo and pdffonts. Renders of all 16 v2 and v3 pages at
  80 dpi and 150 dpi were compared pixel by pixel with PIL.

Cached Tectonic dependencies are trusted. The build is not hermetic. None of these replays
is mathematical evidence.

## Scratch

/var/tmp/t117q-msrev-r3/ holds the packet copies, builds, namespace roots, text extractions,
renders and zooms, and the author-control output. /var/tmp/t117q-msrev-r3-controls/ holds
the review-control copies. Neither is a package member. No frozen packet was used as
scratch.
