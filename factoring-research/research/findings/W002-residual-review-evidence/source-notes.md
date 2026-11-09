# W002 Lens A first review — Sources, provenance and reading limits

2026-10-08. These identities preserve evidence; they do not themselves certify
mathematics or acceptance. The review report owns the conclusions.

## Review inputs

intake-verification.json identifies 48 copied project files and the checks of
the submission's 17 frozen inputs and 27 delivery records. Every recorded
snapshot and delivery entry matched. Current STATE and current W001 synthesis
had advanced beyond their submitted snapshots; the versions observed at
capture are saved alongside the submission's earlier copies. No dependency
report or disposition in that inventory differed. The initial live STATE read
preceded its captured coordinator update; the captured resume instructions and
its ending were subsequently read. Historical mutable status does not override
the user assignment or the completed H031 disposition.

original-constructive-task.md preserves the user-supplied constructive wrapper
followed by the byte-identical frozen W002 brief. review-assignment.md preserves
the reviewer assignment preceding the supplied constructive task, intake and
submission. Those latter objects are separately saved without edits under
inputs/research/findings and inputs/research/hypotheses. No earlier review
round or proposer response exists. No registry was inspected to infer one.

The review reads H004's complete reduction/disposition, H029's corrected
construction/disposition, H030's corrected construction/disposition, H031's
disposition, W001 synthesis and the required instructions/checkpoint. It uses
the dependency scopes stated in the report. H029-independent-review.md was
additionally preserved for its accepted dependency identity; it was not
re-reviewed as a new task. No sibling W002 draft was read. File-name inventory
output incidentally showed sibling file names; it did not expose their content.

## Fresh primary-source retrieval and check

The three submission sources were opened through the web tool, then fetched
as complete files with Python's standard-library HTTP client, concurrently,
using a 25-second request timeout. Each returned HTTP 200 and matched the
submission's saved source exactly. retrieval.json records source URLs, response
metadata, byte sizes, hashes and UTC retrieval times. web-checks.json preserves
the targeted web lookup results and the additional failed DOI attempt.
No package was installed. No source was obtained from an uninspected sibling.

1. David Harvey, An exponent one-fifth algorithm for deterministic integer
   factorisation, arXiv:2010.05450v1 (12 October 2020).
   URL: https://arxiv.org/html/2010.05450v1 .
   Fresh artifact: primary/Harvey-2010.05450v1.html.
   SHA-256: bcd347a997cb82fbc918cac33763762537bc01c797fce3a29f0bc3e0c2c6d0cb.
   Checked sections 2.1–2.3, especially Lemmas 2.1–2.3 and Proposition 2.5;
   Remark 2.6; Lemma 3.1 and Remark 3.2; the Lehman comparison and Remark 3.4.
   The text extraction saved with the submission was read in these ranges.
   The introductory comparison and the semiprime-reduction paragraph in the
   proof of Theorem 1.1 were also exposed/read. The complete section 4 algorithm
   and its proof were not independently audited. The review's consecutive
   interval product, monic reciprocal and access arguments are written out
   rather than inferred from an inverse-dependent evaluation shortcut.

2. David Harvey and Markus Hittmeir, A log-log speedup for exponent one-fifth
   deterministic integer factorisation, arXiv:2105.11105v1 (24 May 2021).
   URL: https://arxiv.org/html/2105.11105v1 .
   Fresh artifact: primary/Harvey-Hittmeir-2105.11105v1.html.
   SHA-256: ae7e7ebc34e4295f971c91cc8276aab785fc60fbc05e24291e79d60c3ed8575e.
   Checked the introduction, Theorem 1.1 and immediately following reduction
   to prime/distinct-semiprime inputs. No full independent audit of the later
   algorithm or exhaustive search for more recent records is claimed.

3. Markus Hittmeir, A time-space tradeoff for Lehman's deterministic integer
   factorization method, Mathematics of Computation 90 (2021), 1999–2010.
   DOI: https://doi.org/10.1090/mcom/3623 .
   Author offprint URL:
   https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf .
   Fresh artifact: primary/Hittmeir-Lehman.pdf.
   SHA-256: e1d92d6eb7b40212fc7be9959f62bd6ca0b0df8fb517b5e2a6f7e79e18c0cd30.
   Read Theorem 2.1 on printed page 2001 and its neighboring representation
   attribution, using the browser PDF extraction and saved text. Introductory
   pages were also read. The source is Hittmeir's primary algorithm paper
   reproducing and using Lehman's theorem, not a newly retrieved copy of
   Lehman's original proof. The earlier original-Lehman HTTP 403 limitation is
   retained in the copied H029 source notes; no retry occurred here.

## Additional primary evidence for the continuing-input family

J. Barkley Rosser and Lowell Schoenfeld, Approximate formulas for some functions
of prime numbers, Illinois Journal of Mathematics 6 (1962), 64–94.
DOI: https://doi.org/10.1215/ijm/1255631807 .

The fresh DOI request through the browser failed with an inaccessible-URL
error. No new successful download is claimed. I instead copied the existing
primary PDF from H029's archived evidence:

    input: research/findings/H029-cover-sources/research/findings/H026-review-Rosser-Schoenfeld-1962.pdf
    saved: primary/H026-review-Rosser-Schoenfeld-1962.pdf
    SHA-256: 8e37b06f82e09421bceb2502578c47b61469141f0287e6acedb70e01765ab556

The corresponding text extraction and the already archived page image were
also copied. supplemental-inputs.json records their source paths and hashes.
I read Corollary 1, (3.5)–(3.6), and Corollary 3, (3.8)–(3.9), in the text
and directly viewed the printed-page-69 image. The displayed threshold in
(3.8) is 20 1/2, not sqrt(20), as the image confirms. Only (3.8) is needed
for the report's unbounded family. The rest of this primary paper was not
independently re-audited.

The use of that theorem is an existence argument about inputs reaching the
specified execution, not a performed prime generation or numerical experiment.
The prime count is not supplied as advice to the factorer. No computational
test or additional source is necessary for the reviewed algebraic bounds.

## Limits and unchanged scope

This is a focused verification of the actual cited comparisons. It supplies
no exhaustive novelty conclusion, latest-record assertion or new claim about
general randomized factoring. H004/H029/H030 remain scoped project sources;
their experiments were read as historical context, never rerun or substituted
for the symbolic proofs. The new report's reduction and lower bound are
independently assessed recommendations; shared acceptance remains parent-owned.
