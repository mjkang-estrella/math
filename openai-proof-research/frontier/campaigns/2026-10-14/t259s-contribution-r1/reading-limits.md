# Reading, search and verification limits (T259S contribution review r1)

Reviewer-owned original prose, CC BY 4.0. Retrieval is not reading. Pinned source theorems at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. No upstream audit was performed.

## Project rules and brief
* Read in full: `AGENTS.md` and `sources/upstream.json`.
* `frontier/NEW-TEN-2026-10-14.md`: lines 1–50 (acceptance criteria) and every line matching 259/T259/quotient/spectral, including the T259S development entry near the end.

## Frozen author packet (fresh-arithmetic-discovery-r30)
* Read in full: `candidate-259.md`, `scope-259.md`, `source-and-credit.md`, `reading-limits.md`, `formal-interfaces.md`, `verify.py`, `controls.py` and `diagnostics.py`.
* `reproduce.md`: the first 40 lines only.
* Not read: `checkpoint.md`, `screen262-checkpoint.md`, `finite-bubble-obstruction.md`, `history-query.txt`, `provenance/*`, the receipt JSON bodies (used only by the verifier), and the family262 material, which is not a T259S premise.

## Pinned source259 (copies authenticated against the canonical tree by Git blob SHA1)
* Read in full: `README.md`, `INPUTS.md`, `build/introduction.tex`, `build/group-actions.tex` and `build/conclusion.tex`.
* `build/compression.tex`: lines 272–296 only (Corollary `compression:cost-one` and its proof).
* Not read: `deployment.tex`, `finite-models.tex`, `planar.tex`, `rank-surgery.tex`, `surgery-figure.tex`, `paper.tex`, `references.bib`, the rest of `compression.tex`, and the PDF (not retrieved). The lower-bound proof is stipulated.

## Primary comparators (author-retained private copies, read locally; no new retrieval)
* Gaboriau 2000, extracted text lines 2380–2514: Proposition VI.21 with its complete proof, Corollary VI.22, Proposition VI.23 with proof, Criteria VI.24, Lemma VI.25 and VI.26(a). I did not view the rendered page images or read Lemma V.3.
* Abért–Weiss arXiv:1103.1063v2, extracted text:
  * abstract (lines 360–420), stating Theorem 1/Corollary 2 and the f×I result;
  * lines 1090–1210 (the strong-ergodicity definition and Theorem 3);
  * lines 1460–1670 (Theorem 4 and the Glasner–Weiss deduction).
  * I did not read the Theorem 1 proof, §3 or §4.
* Hutchcroft–Pete arXiv:1810.11015v2, extracted text lines 7600–7760: the closing remarks, including the Losert–Rindler/Schmidt Bernoulli spectral gap and Abért–Weiss Theorem 4. No other part was read.
* Not read (named as possible comparators in review §5, item 4): Kechris, *Global Aspects* Chapter 10; Tucker-Drob arXiv:1211.6395; Kerr–Pichot; Glasner–Weiss; Khezeli arXiv:2509.08325v4; Bevilacqua–Bowen arXiv:2510.05459v1; Slutsky arXiv:2607.20273v1; Kesten 1959; Losert–Rindler; Schmidt. Fell absorption, Kesten/Hulanicki and the torsion theorem for amalgams are used as standard facts and are not re-proved here.

## Project history
* Read in full: `fresh-parent-discovery-r2/screen.md`; `t259s-parent/author-side-interface-check.md`; `t259s-parent/author-assistance-provenance.json`; and the first 40 lines of `t259s-parent/contribution-review-r1-dispatch.json` (task metadata only).
* `frontier/iterations/i82-measured-group-operator-discovery.md`: lines 1–40 and §8 (lines 247–270) in full.
* `frontier/TEN-FINDINGS.md`: lines 1160–1170.
* `fresh-analytic-discovery-r34/initial-history-screen.json`: the family "259" hit list and the matching hit texts.
* `fresh-structural-discovery-r47/mechanism-check.md`: first 120 lines. This is family248 and is unrelated, apart from a generic two-generator cost bound.
* Searches (ripgrep):
  * the whole project tree, for fixed price, `A-group-without-fixed-price`, strongly ergodic/strong ergodicity, orbit-equivalence cost and graphing, in md/txt/json files;
  * `frontier/*.md`, reviews, iterations and scouts, for family259/source259/fixed-price/ergodic cost/cost interpolation/Y_M;
  * reviews and ledgers, for I82/C82.
  * Index and catalogue hits were treated as pointers only.
* Not read: the T259S proof-review brief or dispatch, `contribution-review-r1-brief.txt` (the brief text was supplied directly), any parallel review packet, and the other iteration files flagged by the r34 hit list. Those hits were word-level matches unrelated to family259 in their hit lines; their full bodies were not read.

## Verification limits
* The verifier run, the copied controls, the source mutations and my independent blob comparison establish file identities only. They prove no mathematics.
* `routine-lift-check.py` checks finite free-group words and index bookkeeping only.
* The reviewer deductions in review.md §2.1–§2.2 are prose arguments from the stated sources and classical facts. They have not been independently reviewed.
* No literature priority or exhaustive search is claimed.
