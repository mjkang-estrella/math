# W002 Lens A — Source identity and limits

2026-10-08. Supporting provenance for W002-paired-residual-products.md.
These records identify bytes, not correctness, novelty, or acceptance.

## Project inputs

W002-residual-inputs.json records 17 project inputs and flat saved copies.
The frozen brief hash is
`5f34c276110ba4ad79781b16b4a86d7ea3860671d168939aca9c399b0480f723`.
The researcher read the rules, specification, research/team protocols, STATE,
W001 synthesis, H004 reduction/disposition, H029 corrected construction and
disposition, H030 corrected report/disposition, H031 current disposition, and
the H029/H030 source notes. Combined tool outputs that truncated were followed
by targeted ranges. Inputs were copied before report construction. The initial
STATE and W001 reads preceded the coordinator's W002 update; the later saved
copies already contain the new W002 resume instructions. The saved STATE's
first 215 lines and the saved synthesis were subsequently read to identify
that change. The exact bytes/hashes of the earlier mutable versions were not
captured before they changed; they are not mathematical dependencies. The
preserved corrected reports/dispositions and frozen brief supply those
dependencies. Mutable records may change again after this archive. H031's own
completed disposition and the user's handoff are authoritative over stale
liveness text elsewhere. No sibling W002 draft contents were read.

## Primary files retrieved in this round

All three primary URLs were opened through the browsing tool, then downloaded
with curl, with HTTP 200 and a bounded 45-second timeout. The web result is
saved as W002-residual-web-retrieval.json. Each complete downloaded file was
compared byte-for-byte with its earlier project archive; all three matched.
The corresponding existing text extractions were copied under this round's
prefix. They are reading aids, not independently authoritative documents.

1. David Harvey, *An exponent one-fifth algorithm for deterministic integer
   factorisation*, arXiv:2010.05450v1.
   URL: https://arxiv.org/html/2010.05450v1 .
   HTML: W002-residual-source-Harvey-2010.05450v1.html.
   SHA-256: `bcd347a997cb82fbc918cac33763762537bc01c797fce3a29f0bc3e0c2c6d0cb`.
   Read §§2.1–2.3 through Proposition 2.5, Lemma 3.1/Remark 3.2, the displayed
   Lehman comparison, and Remark 3.4. Existing matching archive:
   H030-block-Harvey-2010.05450v1.html; reading aid from its adjacent .txt.
   The browser also exposed adjacent introductory material. No complete
   independent audit of §4 or the whole proof is claimed.

2. David Harvey and Markus Hittmeir, *A log-log speedup for exponent one-fifth
   deterministic integer factorisation*, arXiv:2105.11105v1.
   URL: https://arxiv.org/html/2105.11105v1 .
   HTML: W002-residual-source-Harvey-Hittmeir-2105.11105v1.html.
   SHA-256: `ae7e7ebc34e4295f971c91cc8276aab785fc60fbc05e24291e79d60c3ed8575e`.
   Read the opening comparison, Theorem 1.1 and its immediate small-factor
   reduction paragraph. Existing matching archive:
   H030-block-Harvey-Hittmeir-2105.11105v1.html; reading aid from its .txt.
   The full later algorithm was not reread or independently reviewed.

3. Markus Hittmeir, *A time-space tradeoff for Lehman's deterministic integer
   factorization method*, Math. Comp. 90 (2021), 1999–2010,
   DOI https://doi.org/10.1090/mcom/3623 .
   Author PDF URL:
   https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf .
   PDF: W002-residual-source-Hittmeir-Lehman.pdf.
   SHA-256: `e1d92d6eb7b40212fc7be9959f62bd6ca0b0df8fb517b5e2a6f7e79e18c0cd30`.
   Read Theorem 2.1 and its adjoining attribution/representation discussion,
   using the matching text extraction from
   H029-cover-sources/Hittmeir-Lehman-time-space.txt. Full original PDF retained;
   no claim to a complete proof audit or new visual inspection.

## Retrieval and scope limitations

There was no primary download failure in this round. The original 1974 Lehman
publisher PDF was not retried; the earlier H029 403 limitation is preserved
in the copied H029 source note. The checked statement is Hittmeir's primary
algorithm paper reproducing/using that theorem, with coverage inherited from
accepted H029. H004 and H030 are read project inputs, not new primary
literature. No claim rests on an uninspected sibling or secondary summary.

This is a focused prior-art check, not a comprehensive search of subsequent
literature. New bound (6), the divisor-only reduction, and the exact envelope
specification are the proposer's symbolic deductions, not claims attributed
to those primary authors and not accepted research results. Their comparison
to known algorithms is deliberately scoped.

Only document retrieval, reads, copies, hash calculations and report editing
were performed. There was no arithmetic validation sweep, example generation,
solver invocation, implementation, benchmark, test suite or proof-assistant
run. W002-residual-delivery.sha256 seals the report and every owned supporting
file, excluding the manifest itself; later coordinator changes do not alter
the identities of the frozen input snapshots.
