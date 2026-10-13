# I201 reading and failure log

2026-10-12. Completed, unsealed. **No substantial nomination.**

## Scope and actual reading

Read `AGENTS.md`, `sources/upstream.json` and the controlling I201 brief in full. The original I198 brief, report, analytic record and parent response were supplied in the task. In-place follow-up reading was confined to the relevant I198 cylinder passages, its literature note, and the family-100 source files. No recursive authentication or audit of the I198 package was performed. Hashes identify whole containing files even where only a stated passage was used.

Read all four individual section files retained for *Finite cylinder approximation* (introduction, linear-coverings, finite-approximation, comparison) and its bibliography. Read all three companion introductions in full, with the radial introduction reread separately after a combined output ended early. Read the newly retrieved `radial-freezing.tex` and `angular-cubic-buffer.tex` files in full, including their proofs. Accepted all corpus theorems/lower operations at the pin without checking their upstream truth.

Read the complete publisher PDF of Kolountzakis 1998 (11 pages), Grepstad–Kolountzakis 2025 v1 (13 pages), Grepstad–Kolountzakis–Spyridakis 2025 v1 (13 pages), and Bezdek–Litvak 2009 v1 (14 pages). The latter's lattice-point material was read to complete the source, not developed as another research family. Only §3 and slicing are used here. The full-read copies and exact source URLs are recorded in the authentication file. No computation from any of these papers was rerun.

## Retrieval and display failures

* An initial broad `rg --files` returned unrelated historical copies. They were not treated as new evidence or authenticated recursively.
* A whole-catalogue display was much too large and truncated. The family-100 entry was then read with a targeted range; no full-catalogue reading is claimed.
* Initially guessed `sections/01-introduction.tex`-style paths did not exist. The actual retained paths are `build/sections/introduction.tex`, etc.; these were read successfully.
* Two exploratory line ranges in the tree manifest landed outside the desired paths. They were not used. A targeted `jq` path selection located only the four authorized covering companions.
* Some combined tool output was truncated. The radial introduction, the current common-domain paper, the complete extended-square paper, and Bezdek–Litvak were subsequently read in bounded page/range chunks. Reading claims refer to those completed displays.
* `https://eigen-space.org/ps/notch.pdf` downloaded successfully but its local extracted text had broken font encoding. Its SHA-256 was `e40885e2069cad18ad2b70d86666804b33f073deac6782be21125bcc730f2779`. The publisher PDF extracted correctly and was fully read. The unusable author copy was removed from this task's source directory; its text is not evidence.
* The Han–Wang author PDF at `https://www.math.hkust.edu.hk/~yangwang/Reprints/wh.pdf` returned HTTP 403. Its institutional metadata/abstract was inspected. No full-read copy or proof claim is recorded. The newer full-read 2025 papers give the relevant precise endpoint theorems.
* Broad web searches also returned unrelated elliptic-curve/ruled-surface papers and a mirror of the accepted corpus. Those were excluded rather than pursued. Verreault's survey was metadata/context only.

## Mathematical routes and failed claims

1. **Convex rotational envelopes.** Fully derived the square/hexagonal hull costs. They attain the endpoint density bound at three resonances and have finite C¹ realizations. For small elliptic strength their linear excess is too expensive for an automatic quadratic improvement. No global optimality is asserted.
2. **Extended squares.** The negative-product branch of Kolountzakis's explicit lattice identity gives a square plus a rectangle at one height. Keeping both extremal rectangles gives `1+2L²(det A)_+`, with exact finite retention and arbitrary compact labels. This is a useful correction but a technical combination of a known tiling and an accepted transfer argument.
3. **Common endpoint fundamental domains.** The 2025 bounded-polytopal theorem removes the endpoint-existence difficulty. A symbolic cut-and-translate example proves that a common endpoint tile can fail at a strictly denser intermediate lattice. It does not prove that every choice fails; indeed a successful choice exists at the example's resonance.
4. **Convex-body consequence.** The rotational disk sweep is nonconvex and its convex hull is a larger cylinder. Passing a cover to that hull is invalid. The perturbative determinant penalty was calculated, but no new field with verified overlap and a better coefficient was obtained. Stability of an existing strict counterexample is not nominated.
5. **Boundary/count checks.** The affine almost-everywhere tiling was upgraded using closed local finiteness. In the nonlinear construction the actual target is covered before selecting the finite collar. The collar is uniform in height. In the convex-cell construction the fine mesh is chosen larger than the Taylor remainder and smaller than the coarse mesh. An internal overly small bound on the extended tile radius was corrected to `K=2(1+LM)` before completion; the area formula never used that smaller value.

## Overlap and final review

A bounded text search of direct iteration reports found I198's cylinder diagnostic and unrelated Kolountzakis/harmonic-analysis or elliptic-PDE mentions; those unrelated families were not reopened. Search snippets from the shared index were incidental, not an index audit or edit. The final primary-literature check repeated the exact elliptic covering, extended-square, common-domain and cylinder-bound queries. No missing keyword was used as evidence of priority.

Reviewed the final arguments symbolically: sign/transposition in the extended-square formula, rectangle nesting and multiplicities, matrix inverse and spectral margin, finite collar, positive-area boundary handling, determinant perturbation constant, polygon area formulas at all piecewise endpoints, similarity conditioning, intermediate-lattice inverse and cut-and-translate exclusion. No numerical scans, experiments, tests, research programs or proof automation were used. Metadata scripts only created the input hash ledger.

Only the four requested research records, literature note, and full-read source copies inside the authorized I201 directory were written. No child agents were created. No I199/I200 live files, ancestors, shared indexes, I31, staging, commits, publication, snapshots, seals or old replay were touched. Both independent acceptance gates remain with the parent, and neither is claimed satisfied.
