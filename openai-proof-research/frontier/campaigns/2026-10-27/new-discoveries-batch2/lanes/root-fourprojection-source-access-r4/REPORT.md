# New author manuscript recovered; journal-body hold retained

29 October 2026 UTC. Root research, no acceptance or count change.
The previous turn made concrete progress (exact BBK criterion/certificates).
This turn independently investigated one new source-access route; no worker
was polled and no browser, account, contact or public-write action occurred.

## New primary evidence

The earlier r3 report covered publisher, repository, author live-page and
publisher-Wayback routes. Its Banica legacy host was unreachable. A new
Wayback CDX query of the **author's former university website** returned
341 distinct successful PDF URLs (limit500, so the result was not truncated
by that limit). Archived homepage -> research/publication pages yielded:

- Original author publication list: http://banica.u-cergy.fr/pub.html,
  archived 2019-10-15 04:17:37 UTC. It lists the precise title, coauthor,
  journal AAM83(2017),24–46 and links `pdf/mop.pdf`.
- Exact archived PDF:
  https://web.archive.org/web/20210122192517id_/http://banica.u-cergy.fr/pdf/mop.pdf
- HTTP200, application/pdf,375000 bytes,22 pages, SHA256
  `7dace127049add291a7097d15e7fb59106efb995d8bf60fcc77858a2331f68e3`.
- PDF metadata reports creation/modification 2020-06-28 01:52:27 UTC,
  pdfTeX1.40.19. Metadata is a file fact, not proof of author revision date.
- A second exact-URL CDX query collapsing digests returned just this one
  successful archived content digest, `LVTEIXILZ2QZEYP75Q4TRP7U3WEIV6IJ`.

The PDF is an author manuscript with pages1–22, not a typeset journal PDF
with pages24–46. It has no arXiv strip; it differs in bytes and typography
from the frozen arXivv3. The full layout-text diff is retained, but most
changes are extraction/font/position effects. No claim of complete semantic
equivalence across all22 pages is made.

## Actual statement read

I rendered and visually read the recovered PDF's page20. Conjecture6.6
retains the six literal hypotheses: P perpendicular Q; R perpendicular S;
the P/R and Q/S ranges have zero intersections; both displayed pairwise
rank balances. Its conclusion is the same unnormalized trace comparison
Tr(PR)+Tr(QS)>=Tr(P'Q')+Tr(R'S'), with the four primed projections defined
by the two inverse-square-root congruences. The following sentence explicitly
specifies Moore–Penrose inverses. Proposition6.7 still claims only the S=0
special case, and the preceding prose still describes the full assertion
as conjectural. The rendered page also contains Conjecture6.5, a separate
algorithmic assertion not proved by our candidate.

This is meaningful new evidence: an author-distributed manuscript associated
with the journal citation and archived years after publication retains the
exact question. It mitigates the possibility of an intervening resolution,
but does not prove the September2016 accepted or journal version is identical.
In particular, a 2020 recompilation could still use an older source file.

## Disposition

**SOURCE: HOLD on actual journal-body comparison remains.** The new copy
must not be called the version of record, accepted manuscript, or journal
conjecture page without additional provenance. No prior hold is silently
cleared. The precise remaining item is the actual published AAM83(2017)
24–46 statement and surrounding definitions.

**NOVELTY: no new clearance.** Targeted fresh searches returned existing
preprints, author bibliographies and related papers. The separate ResearchGate
record titled Universal models exposes arXivv3 in search-index text, so it
was identified as that preprint rather than pursued as a journal copy.
The Academia profile page produced no matching target. OASIS supplied the
legacy homepage URL. No blocked publisher/ResearchGate endpoint was retried,
and no new complete registry/citation corpus audit was performed. Prior
bounded reviews remain as they were; empty searches do not prove absence.

Mathematics, formal files, frozen paper, archive and ledger were not changed.
No replay was needed for this source-only investigation. Credit0; counts
remain3/30 additional,33/60 total. This route is now documented and should
not be rediscovered as if it supplied a typeset journal copy.

## Saved evidence

`banica-pdf-cdx.json`, `banica-html-cdx.json`, the homepage/research/publication
CDX and archived HTML files, `banica-mop-archived.pdf`, extracted text,
`author-page20.png`, full layout diff and provenance hashes. All retrievals
used ordinary public HTTPS to the Internet Archive. CDX queries selected
public status200 captures; no access restrictions were circumvented.
