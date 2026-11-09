# W020 annihilator review: provenance and read scope

The exact user task is `original-brief.txt`. `input-manifest.json` freezes its
SHA-256 and the bytes, sizes, line counts, original paths, and SHA-256 hashes of
every local load-bearing input. All substantive conclusions address those frozen
bytes. The task was performed only within `/home/mj-kang/Documents/Dev/math/factoring-research`.
The only authored output paths are `research/findings/W020-annihilator-review.md`
and this evidence directory. The read of STATE was contextual; its parent agenda
was not resumed and it was not edited.

## Local material read

- `AGENTS.md`, all 26 lines.
- `RESEARCH_TEAM.md`, all 75 lines.
- `RESEARCH_LOOP.md`, all 77 lines.
- `README.md`, all 73 lines.
- `docs/SPECIFICATION.md`, all 136 lines.
- `research/findings/W020-annihilator-amortization.md`, all 125 lines.
- `research/findings/W019-torsion-cancellation-review.md`, all 274 lines. Its
  accepted cancellation/odd-part interface and previous missing-amortization
  observation are inputs, not re-audited theorems. Its certificate was not read
  or executed.
- `research/findings/W018-powered-base-review.md`, all 165 lines, with the long
  initial tool output's truncated middle supplemented by explicit chunk reads.
  Only the exact bounded-order search and deterministic matching interface are
  imported. Its unit sampling, factor extraction probability, and progression
  application are not treated as class-group results. No certificate was run.
- `research/STATE.md`, frozen in full, but read only lines 1–105 and 1070–1172.
  The opening covers task context; the ending covers general validation status.
  Unread middle content is not an authority for this report. The explicit new
  brief and parent construction take precedence over the older STATE summary.

File discovery searched names within the project and checked for instruction
files at `research/AGENTS.md` and `research/findings/AGENTS.md` (neither existed).
No other findings, solver, Lean, task-file, or registry content was inspected.
Names of source files in W018/W019 evidence were listed to locate primary-source
copies. Only the W019 Schoof PDF/text bytes were copied; this is not a new read
or run of the W019 experimental evidence.

## Primary literature actually used

All retained source bytes and derived text/page images are hashed in
`primary-sources/manifest.json` and the delivery inventory. Page numbers are
explicit below; a full retained PDF does **not** imply it was read in full.

1. René Schoof, *Quadratic fields and factorization* (1982).
   URL: <https://www.mat.uniroma2.it/~schoof/mcpaper.pdf>.
   `schoof-quadratic-fields.pdf` and its OCR text were copied byte-for-byte from
   `research/findings/W019-torsion-cancellation-review-evidence/sources/` before
   reading the relevant passages. The source URL was also opened with web tools.
   Substantive reading: text lines 530–735 (printed pp.246–250, with the last
   passage ending mid-discussion) and 1735–1815 (printed pp.270–272, beginning
   with the end of the preceding proof). Used portions: §3's interval search,
   order recovery, powering/dividing later intervals, and the stated cost;
   Algorithm 6.4's search loop and cost. No new audit of genus theory,
   cancellation, or analytic tail proofs. A web screenshot request for PDF
   page 14 returned a reference, not an image inspected by the reviewer; do not
   count it as visual reading. The source opening exposed some introductory
   text incidentally; it is not load-bearing.

2. Andrew V. Sutherland, *Order Computations in Generic Groups* (2007 thesis).
   URL: <https://math.mit.edu/~drew/sutherland-phd.pdf>.
   Downloaded to `sutherland-phd.pdf`; `pdftotext -layout` created the retained
   text. Substantive reading: lines 565–606 (printed pp.19–20, black-box
   definition); lines 5850–5933 (pp.129–131, algorithm and divisibility lemma,
   including some surrounding probability discussion not imported); lines
   6000–6205 (pp.132–136, order-complexity discussion, Proposition 8.5,
   Algorithm 8.2, Proposition 8.7, Theorem 8.9 and limits); lines 7650–7805
   (pp.171–175, incidental prior experimental context and §11.4 comparison).
   Only the named exponent algorithms, associated bound, and encoding
   definition support the review. Historical performance numbers and the
   thesis's survey of other methods are not current performance authorities.
   PDF/printed p.134 was rendered and inspected as `sutherland-page-134.png`.

3. Kiran S. Kedlaya and Andrew V. Sutherland, *Computing L-series of
   hyperelliptic curves* (2008).
   URL: <https://math.mit.edu/~drew/ComputingLSeriesOfHyperellipticCurves.pdf>.
   Downloaded to `kedlaya-sutherland-lseries.pdf`; `pdftotext -layout` created
   the retained text. Substantive reading: text lines 245–312, §4.2, on PDF
   pages 6–7 (file page count 14). Both pages were rendered and inspected as
   `kedlaya-sutherland-page-06.png` and `kedlaya-sutherland-page-07.png`.
   The images include adjacent tables and the start of §4.3; those do not
   support a performance claim here. The printed `|G|=E` following the
   unique-multiple condition was visually confirmed, then treated with the
   explicit mathematical qualification in the report. No broad audit of this
   paper's probability, Jacobian, factoring-cost, or analytic claims was made.
   The 2008 date/authorship was cross-checked against the primary arXiv record
   <https://arxiv.org/abs/0801.2778> as returned in the date search.

Line ranges refer to the retained `.txt` files, including form-feed page
separators. Exploratory `rg` keyword results are locators rather than complete
reads; broad search output was truncated, and the relevant ranges were then
read directly as listed above. The primary PDF files, rather than OCR alone,
are retained to permit independent checking.

## Bounded literature search

Queries, in order (one bounded search pass with targeted follow-ups):

- `Schoof 1982 quadratic fields factorization algorithm class groups 6.3 exponent`
- `Sutherland computing group orders exponent interval algorithm baby step giant step exponent accumulation`
- `"group exponent" "interval" "Sutherland" baby giant`
- `"exponent" "interval" "class number" "baby" group order`
- `"order" "interval" "least common multiple" "baby" group algorithm`
- `Kedlaya Sutherland "Computing L-series" 2008 2007`

The first complete result object is retained in `web-search-initial.json`.
Later query hit lists are not all serialized locally; the exact queries and the
primary sources actually followed are listed here. Secondary hits, including
Wikipedia, commercial mirrors, forums, and bibliographic aggregators, were not
used as mathematical evidence. Cremona–Sutherland and other related primary
papers appeared as search snippets but were not followed or relied upon. This
scope does not establish absence of the exact W020 formulation elsewhere.

## Verification and experiment boundary

No certificate was preregistered or executed. All finite examples in the report
were derived symbolically by hand. No search, sweep, random sampling, performance
measurement, historical certificate execution, or case tuning was performed.
The only executable work was file inventory, copying/hashing, source retrieval,
PDF-to-text/image rendering, report/evidence writing, and structural/integrity
checks. These are not experimental outcomes or asymptotic evidence.

`verification.json` records hashes and live-input drift at handoff. If a local
input changed concurrently, its final snapshot and textual diff are preserved
under `handoff-drift/`; the original remains frozen. `delivery-manifest.json`
and `delivery.sha256` anchor all final payloads without self-reference. No
unrelated workspace files were modified by this review.
