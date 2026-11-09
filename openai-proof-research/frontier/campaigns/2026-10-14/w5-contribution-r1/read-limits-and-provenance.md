# Read limits, provenance and rights

Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code (`coefficient_check.py`, `verify.py`) MIT. The third-party files in `private/` are private reading inputs only. They must not be committed, staged or redistributed, and nothing here grants rights to them.

## Author packet (fresh-analytic-discovery-r25), read in full
README, original-scope, candidate, freeze-receipt, mechanism-checkpoint, pre-freeze-comparison, reading-and-comparison, adversarial-audit, screen-log, checkpoint, verify.py, primary-receipt. I did not open source-receipt, input-receipt or the copied context in `inputs/`; the author verifier authenticates them.

## Pinned source (fetched independently into private/source/, all preprint blobs matched to complete preprints-tree.json)
- Family 359 main paper:
  - Read in full: main.tex, 01-introduction, 02-reduction, 05-logarithmic-tests, 06-base-potential.
  - 03-peaks: lines 1–40 (mean criterion and proof) read, plus grep-located definitions and statements of `peaks:polynomial`, `peaks:bounds`, `peaks:patches` and `peaks:profiles`. Their proofs were not read.
  - 04, 07, 08 and 09: fetched only. A grep for embed/Carathéodory across all sections found no embedding claim.
- Companion one-sided paper: 01-introduction scanned with grep for embedding and bounded-function statements, and lines 45–60 read. main, 04-fiber and 08-assembly were fetched but not read.
- Lean: `lean/docs/359.md` was read. In `lean/ComparatorChallenges/PinchedKahler.lean` I read only the declaration list. Both were fetched from pinned raw URLs; they lie outside preprints-tree.json, so their Git blobs are **not** tree-verified.
- Source truth is stipulated. I did not audit the source's correctness.

## Primary literature
- Demailly–Lempert–Shiffman, arXiv alg-geom/9212001v3. Fetched independently and byte-identical to the author's copy (sha256 ea77bfd5…). Lemmas 2.4–2.5 statements and full proofs, and Corollary 2.6 with its proof, read (extracted lines 510–585). The rest was not read.
- Forstnerič, arXiv 1709.05630v5 survey, fetched independently (sha256 9fdb9ba4…). Read: §2.1 (Theorems 2.1 and 2.3, Proposition 2.2 and the proof outline), §2.2 (Theorem 2.4, the Forster minimality remark and the outline start), §4.1 (Theorem 4.1) and §4.3 (complete bounded submanifolds). This is a survey; the original Forster/Eliashberg–Gromov/Schürmann proofs were not read.
- Forster 1970, *Plongements des variétés de Stein*. My retrieval returned the e-periodica "Verification required" HTML, kept as `private/primary/forster-1970-attempt.html`. **Unread.** No conclusion depends on it; DLS Lemma 2.5 and the survey pay for the classical generation and embedding counts. Cartan's original Theorem B papers were not read either; only DLS's use of Theorem B was read.
- Wu–Yau, JAMS 2020. I used the author's retained, hash-verified PDF (sha256 5ff268d1…) and read pages 103–106 (introduction, Theorems 4 and 6, Corollary 7, and Yau Problem 38 context). Proofs were not read. arXiv retrieval failed: the guessed ID was wrong, and the downloaded file (an unrelated paper) was deleted.
- Jarnicki–Pflug 2022 (DOI 10.1007/s12220-022-00970-8). I used the author's retained publisher HTML (sha256 07046021…) and read the text of §1 through Corollary 2.4, including the full proof of Example 2.1. The 2024 correction was not read.
- Hedenmalm 1989: not attempted. It concerns the representing-versus-Jensen distinction, which is not relevant to the operation.
- Two bounded web searches returned leads only (arXiv math/0502435, 2402.16494, 2509.04179, 2407.10295, 2009.13027, and a CCG IBS seminar abstract). None of them was read. This is not a worldwide priority search.

## Project history
grep over frontier/iterations, reviews, findings, scouts, experiments and campaign markdown, excluding copied `inputs/` and `private/` trees. Matching passages were inspected as described in review.md §6. Ledger NEW-TEN-2026-10-14.md: lines 1–140 and 820–905 read. The middle of the ledger was searched only by grep.

## Computation
`coefficient_check.py` is an exact rational identity test with a falsifying control. It supports one algebraic line and is not a proof.
