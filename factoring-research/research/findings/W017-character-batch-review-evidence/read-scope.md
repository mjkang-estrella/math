# Frozen sources and exact read scope

This is the evidence ledger for `../W017-character-batch-review.md`.
All writes in this review are confined to that report and this evidence tree.
No finite arithmetic trial, timing experiment, solver test, installation,
delegation, commit, or shared-state edit was performed. Python was used only
for source acquisition, snapshotting, rendering orchestration, and hash/link
bookkeeping. Poppler was already available. The optional certificate was not
run, so there is no unrecorded code revision, seed, failure, or success rate.

## Repository inputs and brief

`input-freeze.json` records acquisition time, byte count, original relative path,
snapshot path, and SHA-256 for each repository input. Copies were made before
the mathematical review was written. The snapshot, rather than a possibly
changing live parent file, controls this review.

Read completely: AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, README.md,
docs/SPECIFICATION.md, and the submitted research/hypotheses/W017.md.
W001-algebra.md is frozen in full; Card C was the load-bearing background read.
Some other cards were exposed during initial reading but no new audit of those
cards was conducted. research/STATE.md is frozen in full for context; only its
opening/current-action material (lines 1-150 in the frozen copy) was used.
The large initial combined output was truncated, so the required candidate
and specification were reread separately. No truncated output is treated as
proof of reading the omitted contents. W016 and W014 were not audited.

`brief.txt` transcribes the full task message with its paragraph boundaries
and a terminal newline. The final delivery manifest hashes it.

The PDF skill was read for the read-only source workflow. No PDF was authored
or edited; rendered images are inspection evidence. No skill-required install
or artifact-authoring flow was invoked.

## Primary PDFs

URLs, resolved redirects, sizes, exact PDF hashes, and retrieval timestamps are
in `source-retrieval.json`. The versioned Hiary URL was deliberately requested;
its visible header is arXiv:1608.06614v2, 17 December 2016. Schoof's supplied URL
redirected to the author's `reneschoof.github.io` copy. These downloaded bytes
are frozen alongside `pdftotext -layout` output. All full PDFs are archived;
archiving is not a claim of reading every page.

### Schnorr-Lenstra, 1984

Source: https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1984c/artc.pdf

This is a scanned PDF. `pdftotext` produced only 12 form-feed bytes; that empty
extraction is retained and was not mistaken for a successful text read.
PDF pages 1-3 were rendered with Poppler. Visually inspected PDF pages 1 and 2:
printed p. 289 and the p. 290-291 spread. The load-bearing introductory passage
on p. 290 was read directly, including its GRH qualification, class-number
approximation route, and 1/4-to-1/5 comparison. The visible start of Stage 1 on
p. 291 was inspected for context, not audited as a complete algorithm. The
right side of that spread is clipped by the scan. Rendered PDF page 3 was not
used or read. Neither the later stages, appendix, smoothness analysis, nor
their proofs were audited. No exact transcription of the small-font error
formula is relied on; Schoof's legible theorem is used instead.

### Schoof, Quadratic Fields and Factorization

Source: https://www.mat.uniroma2.it/~schoof/mcpaper.pdf

Read the introduction and the relevant definitions/class-number context in
the web-extracted primary text; read local extracted section 3 through its
end (printed pp. 244-250) and section 6 through its end (pp. 264-274).
The load-bearing items are the class-number formula on p. 245, interval search
and its qualifications on pp. 247-250, Corollary 6.2 and Theorem 6.3 on
pp. 266-267, and Algorithm 6.4 with its cost discussion on pp. 270-272.
Algorithm 6.5 was read as contextual primary text; no real-quadratic
algorithm is claimed as a new W017 extraction method.

Visually verified complete rendered printed pages 267, 270, and 271
(PDF pages 33, 36, 37, using 1-based PDF numbering). This resolves the OCR
ambiguities in the tail inequality and complex-quadratic algorithm.
Theorem 6.3 is explicitly GRH-qualified, with the threshold
`x > c2 log^2 |Delta|` and right side `c3 log(|Delta| x)/sqrt(x)`.

The proof outline of Theorem 6.3 was read, including its extension to
nonfundamental discriminants, but was not independently reproved. External
zero-counting/Chebotarev estimates, genus-theory references, and all group
algorithm refinements were not independently audited. Reading section 6 is
not a claim to have verified the entire 52-page paper or all dependencies.

### Hiary, arXiv:1608.06614v2

Source: https://arxiv.org/pdf/1608.06614v2

Read sections 1 and 2; the end of section 3, including its cost/error setup;
all of sections 4, 5, and 6; and the opening paragraph of section 7. The
load-bearing locations are Theorem 1.1 on p. 1, the explicit s=1 extension
and algorithm summary on p. 2, composite inclusion/exclusion (22)-(28) on
p. 6, exponential multi-evaluation Theorem 5.1 on p. 7, and the explicit
factorization-sieve accounting at the end of section 6 on p. 8.

Visually inspected complete rendered pages 1, 2, 7, and 8. Page 6 was rendered
and read as extracted text, but its PNG was not separately inspected. The
full auxiliary proofs in section 8 and the full section-3 Taylor derivation
were not audited. The s=1 assertion is the author's explicit introductory
statement; this review does not independently complete its proof from the
critical-line derivation. No promise about a lone unfactored conductor is
inferred from the dense-conductor average.

The Fourier reduction of W017's finite periods is derived explicitly in the
review. It uses the general exponential-sum theorem, not Theorem 1.1's
conductor preprocessing or an unevaluated full-L-value oracle.

### Odlyzko-Schonhage, Fast Algorithms for Multiple Evaluations of the Riemann Zeta Function

Author-hosted primary source:
https://www-users.cse.umn.edu/~odlyzko/doc/arch/fast.zeta.eval.pdf

Read the title/abstract, all of section 3, and the opening of section 4 through the statement of
Theorem 4.1 and the beginning of its proof (preprint pp. 12-17). The section-3
near-coincident-node handling and the separation hypothesis in Theorem 4.1
were explicitly checked. The remaining hierarchical-evaluation proof was not
audited. This supports the method identification; Hiary's Theorem 5.1 supplies
the convenient parameterized exponential-sum statement used in the comparator.

### Brent-Kung, Fast Algorithms for Manipulating Formal Power Series

Author-hosted primary source:
https://maths-people.anu.edu.au/brent/pd/rpb045.pdf

Read the title/abstract and introduction through the coefficient-model
discussion and opening regularity lemma (printed pp. 581-582), not the full
composition/reversion proofs. The report uses this only for established
formal-series background and the distinction between coefficient operation
counts and bit cost. Composite-ring Newton correctness, integer packing,
and signed recovery are proved directly in the review. No general field
theorem from this paper is silently applied to Z/(2^W).

## Discovery and limitations

The three user-supplied primary URLs were opened with the web tool and then
downloaded directly into this directory. Two bounded search rounds sought
formal-series and exponential/rational multi-evaluation precedents. The query
strings were:

- `fast sum rational functions polynomial product tree power series inversion Brent Kung 1978`
- `quadratic Dirichlet L functions simultaneous Euler products discriminants Legendre periodic generating function`
- `Odlyzko Schonhage 1988 fast algorithms multiple evaluations Riemann zeta function rational function sum polynomial product pdf`
- `sum rational functions product tree polynomial fast algorithm primary paper Bernstein`

Search snippets and third-party metadata were discovery aids only. The two
additional author-hosted primary PDFs were downloaded and the actual passages
above read before use. No negative search result establishes priority or the
absence of an earlier identical implementation. No claim is made that this
bounded reading surveys current best factoring algorithms.

## Delivery integrity

`delivery-manifest.json` lists every delivered payload file, including the
report, brief, frozen inputs, primary PDFs, extracted text, rendered pages,
and bookkeeping records. It excludes itself and its separate
`delivery-manifest.sha256` anchor to avoid circular hashing. A final integrity
check recomputes all listed hashes and verifies local report links. Live-input
drift, if any, is recorded separately; it does not replace frozen inputs.
