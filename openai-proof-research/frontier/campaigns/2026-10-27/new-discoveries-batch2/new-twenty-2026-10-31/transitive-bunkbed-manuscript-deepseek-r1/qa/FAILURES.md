# Failures and true exits

This file records the failed commands and the layout iterations, with their true exits, as required by TASK.txt. All receipts and outputs remain in the lane.

## Command failures

1. `groff -Tps -ms qa/glyphtest.roff` (label `glyphtest_build`):
   - groff exit **4**.
   - stderr: `troff: fatal error: cannot open macro file named in '-m' command-line argument 's': No such file or directory`.
   - Cause: the `-ms` macro package is not installed in this environment. The pipeline continued: `ps2pdf` exit 0 on the empty PostScript, and `pdftotext` returned only a formfeed.
   - Fix: use plain `groff -Tps` with the page-setup requests taken from `inputs/format-example.roff`; no macro package is used. The final build uses this route.

2. `\[u2115]` for the double-struck natural-number symbol (label `glyphtest_build3`):
   - groff exit 0, but warning `special character 'u2115' not defined`; the glyph rendered blank.
   - Fix: do not reproduce the glyph. The paper describes the audit's natural-number notation in words instead. No blank or box glyph remains in the final PDF.

## Layout iterations (not command failures)

All of these rebuilt with groff exit 0 and ps2pdf exit 0; the issue was pagination.

1. `build_pdf_2` / `build_pdf_3`: page 4 was overfull by one body line, so the footer was pushed to y = 769.9 pt instead of the normal 760.5 pt. Fix: force a page break before Section 5 and tighten spacing.
2. `build_pdf_4`: 6 pages; page 5 footer at y = 765.5 pt and page 6 contained only the last reference. Fix: reduce heading and reference spacing.
3. `build_pdf_5`: 6 pages; page 5 footer at y = 769.7 pt and page 6 had 10 words. Fix: further spacing reductions.
4. `build_pdf_6`: 5 pages, but page 5 footer at y = 766.9 pt. Fix: reduce reference spacing.
5. `build_pdf_7` and the final rebuild: 5 pages; every footer at y = 760.51 pt; maximum word xMax = 558.01 pt against the 558 pt right text edge; no word beyond 558.6 pt.

## Final build exits

- `groff -Tps source/bunkbed-transitive-tournaments.roff`: exit 0, stderr empty.
- `ps2pdf qa/tmp/doc.ps output/pdf/bunkbed-transitive-tournaments.pdf`: exit 0, stderr empty.
- `pdftoppm -r 150 -png ... qa/page`: exit 0.
- `pdftotext -layout ... qa/tmp/doc.txt`: exit 0.

The final PDF is `output/pdf/bunkbed-transitive-tournaments.pdf`, 5 pages. The rendered pages are `qa/page-1.png` through `qa/page-5.png`.
