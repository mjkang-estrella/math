# Independent W004 source inspection and access scope

2026-10-08. Source reading only; no source algorithm, example or test executed.
The original eleven source-artifact identities independently match their SHA-256
and byte counts in W004's ledger. They represent six works, not eleven separate
theorems. The review's input-identities.json maps each actually used archived
object to a byte-identical frozen copy. No recursive historical source tree was
copied. The PDF skill was used for source-page inspection, not PDF authoring.

- Rosser–Schoenfeld (1962): archived PDF and p.69 image; inspected the image
  and the same page via the live primary mirror. Corollary (3.13) is
  p_k<k(log k+log log k) for k>=6. That statement alone is used for the
  auxiliary-prime size bound. The article's analytic proof was not re-audited.
  Source: https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf
- Cremona, corrected second edition, chapter III: archived PDF/text, text
  lines 671–755 (printed pp.75–76), 833–920 (pp.78–79 and beginning of 80),
  1320–1425 (end of 87, p.88, beginning of 89). Inspected the new p.88 render.
  The uses are bounded point-height search, local/global distinction, rank
  bounds, the explicit prime-divisor input in the rational-2-torsion procedure,
  and the quartic covering model. No general 2026 algorithmic nonexistence
  statement is inferred from this historical text.
  Source: https://johncremona.github.io/book/fulltext/chapter3.pdf
- Cremona–Fisher–O'Neil–Simon–Stoll, arXiv math/0606580v1: archived HTML
  introduction independently extracted with the standard-library HTML parser,
  and live introduction read at web lines 63–79. Used only for the Selmer
  exact sequence, quartic 2-coverings, and the distinction between representing
  coverings and finding points. No later algorithm or implementation imported.
  Source: https://arxiv.org/html/math/0606580v1
- Coppersmith (1993): archived PDF/text, lines 1–315 covering printed
  pp.169–175, plus independent p.170 render. The explicit heuristic
  smoothness-transfer qualification, norms, character columns, actual algebraic
  roots and multiple fields with a common modular evaluation are present.
  The simplifying order assumptions and speculative inert-prime/root stage
  are not imported into W004. No packet-success law follows from this source.
  Source: https://link.springer.com/content/pdf/10.1007/BF00198464.pdf
- Shallit: archived PDF/text, lines 1–110 and 325–360, plus independent p.9
  render. The cost estimate is conditional on a least-prime premise. Legacy
  extracted glyphs are damaged, so the rendered paragraph governs that reading.
  Poppler emitted repeated Type-3 glyph bounding-box warnings; the relevant
  rendered paragraph was readable. No source example was calculated. The
  accepted W003 D=-1/base-case qualification remains inherited context;
  the separate referenced fast algorithm was not retrieved or imported.
  Source: https://cs.uwaterloo.ca/~shallit/Papers/pols.pdf
- Boneh–Gentry–Hamburg: archived PDF/text lines 390–500, including §§5.1–5.2
  through Lemma 5.2 and the beginning of §5.2.1; independently rendered and
  inspected printed pp.9–10. Suitable prime generation and integer conic
  inputs are charged. Nonzero integer denominators require separate modular
  unit checks. Appendix C was not re-audited in this W004 review; its accepted
  scoped W003 disposition is retained, not broadened.
  Source: https://theory.stanford.edu/~dabo/papers/bgh.pdf

New access attempts: four direct web opens, to the Rosser mirror, Cremona,
CFOSS v1, and Coppersmith URLs above, all succeeded. Two subsequent opens
inspected the CFOSS introduction and Rosser p.69; both succeeded. Exact tool
results are preserved in primary-open-results.json and
primary-passages-results.json. The local archives, not a claimed new download
identity for those web results, supply the frozen PDF/HTML evidence.

There were no new failed network retrievals. Existing W004 source notes retain
the failed Rosser DOI and unusable Euclid wrapper. The frozen W003 access
record retains the AMS 403. The accepted norm-gate disposition records the
six focused reviewer searches that did not obtain AEM's full primary text.
These are inherited retrieval limitations, not searches repeated here; no
AEM endpoint was opened and no fast Norm2 theorem was granted.

Hashes authenticate files, not mathematical claims. The independent symbolic
proofs in the report establish its elementary algebra and geometry. This
inspection neither establishes novelty nor audits all cited analytic proofs.
