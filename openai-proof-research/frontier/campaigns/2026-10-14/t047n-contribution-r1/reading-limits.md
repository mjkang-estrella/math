# Actual reading, search and proof limits (T047N contribution r1)

Opening a file or hashing it is not semantic reading. Line ranges refer to the files as they existed at review time.

## 1. Rules and campaign
- `AGENTS.md` and `sources/upstream.json`: read in full.
- `frontier/NEW-TEN-2026-10-14.md`: lines 1–40 (acceptance rules), 160–189 and 785–1032 (the exclusions section through the T008M tail), plus targeted grep hits for 047/F004/cancellation/Ghosh/exclusion. The whole ledger was NOT reread.
- `findings/F004-cyclic-affine-actions.md`: read in full.
- `t047n-parent/reading-and-status.json`: read in full.
- NOT read: `t047n-parent/proof-review-r1-brief.txt`, `contribution-review-r1-brief.txt` (its content arrived as my task brief), `author-identity-check.json`, `parent-diagnostic-replay.json`. `t047n-proof-r1/` was never opened or listed.
- Campaign-history search: `rg` over `frontier/` for family 047, source 047, cancellation and Derksen, excluding the proof packet and the author packet. Hits other than F004 were catalogue copies (`CONTENTS.md`), unrelated primary texts, and `fresh-structural-discovery-r39/history-index.json`. None of these was opened. No campaign screen of 047 thickness variation was located.

## 2. Frozen author packet (fresh-arithmetic-discovery-r29)
- Read in full: `candidate-047.md`, `scope-047.md`, `source-and-credit.md`, `reading-limits.md`, `manifest.json`, `verify.py`, `controls.py`, `diagnostic.py`.
- Hash- or byte-compared only, not read: `checkpoint.md`, `formal-interfaces.md`, `verification.md`, every `*-receipts.json`, `source-family-inventory.json`, `controls-result.json`, `diagnostic-result.json`.
- `t047n-author-primary-clarification-r1/clarification.md`: read in full.

## 3. Source047 bodies (private, authenticated; truth stipulated)
- `01-introduction.tex`: approximately lines 1–200, including the theorem, the cylinder/residual-coordinate paragraph, the obstruction outline and the ring table.
- `03-degeneration.tex`: lines 1–120 (valuation, filtration, graded injection) and approximately 240–360 (smoothness, KZ remark, `lem:induced-lnd`, `prop:positive-invariant`).
- `04-bundle.tex`: statements of `prop:principalization` (around line 51), `prop:linearization` (around line 211), and `prop:homogeneous-lift` with its full proof (lines 337–420).
- `05-reduction.tex`: lines 1 through the Case 2 order equation (`red:pieces`, `lem:lnd-order`, `prop:extracted-lnd` Cases 1 and 2).
- `06-rigidity.tex`: only the final contradiction passage (around lines 280–330).
- `references.tex`: lines 45–75.
- NOT read: `02-construction.tex`, `07-affine-fibrations.tex`, the rest of 04/05/06 (including the main rigidity proof, which is stipulated), and `main`/`preamble`. Source PDF not retrieved.
- Family049 companions: bytes authenticated only. No body read.

## 4. Primary bodies (private copies retained by the author; not staged)
- Ghosh–Gupta arXiv:2206.15210v5 (`ghosh-gupta.txt`): lines 1–140 (abstract, introduction), 225–305 (Lemma 2.2, filtrations, Thm 2.3, Lemma 2.9, Props 2.10–2.12) and 1130–1340 (Thm 4.1 with full proof, Thm 4.2 with proof, Thm 4.3, Cor 4.4). The rest was not read, including the §3 admissible-filtration Lemma 3.2 proof and Prop 3.4. The PDF and page image were not inspected; the text extraction was trusted.
- Ghosh–Pal arXiv:2404.13803v1 (`ghosh-pal.txt`): lines 1–45 and 200–345 (Lemma 3.1, Thm 3.2 with full proof, Remark 3.3, the statement of Prop 3.4). The rest was not read; the PDF was not inspected.
- Blanc–van Santen: NOT read. It is relevant only to the abandoned pre-freeze idea.
- Cited classical results (Kaliman–Zaidenberg, Kaliman–Makar-Limanov, Dutta–Lahiri, El Kahoui–Ouali, Freudenburg localization principles): used from standard knowledge and the source's own deployment. No primary bodies were read.

## 5. Additional bounded prior-art search (web)
- Two WebSearch queries (Gupta–Sen double Danielewski; Danielewski-type thickness families).
- Fetched arXiv abstract pages only: 1908.03403 (Gupta–Sen, J. Algebra 533 (2019)) and 2002.12838 (Dubouloz). One search snippet records Danielewski's family xⁿz=y(y−1).
- Snippet-only, unread: arXiv 2607.13593 (Gaifullin–Petrov) and 2501.09613.
- No exhaustive search or worldwide novelty or duplicate certification. No local content was uploaded; only search queries were sent.

## 6. Proof limits
- Correctness of T047N was ASSUMED for classification.
- I re-derived only the following, as classification evidence, not as a proof review: the n-bookkeeping in candidate §4 (pieces, j=nq+1, the order values), the extended-Rees staircase degree pieces, the exactness of the clarification model, the GG/GP omitted-power observation, and an m=1 repair sketch.
- The m>1 repair, the rigidity proof and the lift theorem were not verified (the last two are stipulated source inputs).

## 7. Integrity actions
- The frozen packet was never modified. All mutation controls ran on disposable `/var/tmp` copies, which were deleted.
- Own outputs are confined to `t047n-contribution-r1/`. No staging, commits, shared-index edits, counts, uploads or nested agents.
- Original prose and code in this directory: MIT for code, CC BY 4.0 for prose. Third-party bodies remain private and are not copied here.
