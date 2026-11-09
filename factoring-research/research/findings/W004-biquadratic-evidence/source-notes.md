# W004 primary-source scope and archival notes

All activity was source inspection and file authoring/archiving. No source
example was executed and no mathematical program was run. Primary-source
identities and exact copied/downloaded bytes are listed in `sources.json`.
The delivery manifest also includes the derived Cremona text extraction.

- **Rosser–Schoenfeld (1962)**: read printed p.69, Theorem 3 and corollary
  (3.13), including the k>=6 condition. Visually inspected the existing p.69
  image, then copied it and the primary PDF into this prefix. The primary
  article's mirror was reopened with the web tool. Used only to bound the
  first O(n) primes; no least-prime-in-progression estimate was imported.
  DOI 10.1215/ijm/1255631807 failed through the web tool with an inaccessible
  URL error. The Project Euclid .pdf endpoint produced an iframe wrapper,
  not usable article text. The existing primary PDF/mirror supplied the page.
- **Cremona, Algorithms for Modular Elliptic Curves, chapter III**: downloaded
  the author's corrected second-edition PDF and extracted text with pdftotext.
  Read section 3.5 opening, printed pp.75–76, on bounded point search;
  section 3.6 opening, pp.78–79, on local/global solubility and rank bounds;
  pp.87–89 on the rational-2-torsion procedure, its `prime divisors` input
  preparation, bounded quartic searches, and the general quartic model.
  These source procedures do not give a polynomial-time witness theorem for
  the W004 curves. Their historical general limitations are not advertised
  as a newly verified survey of everything known in 2026.
- **Cremona–Fisher–O'Neil–Simon–Stoll (2006), Explicit n-descent I**: read
  the introduction through the discussion of quartic 2-coverings, web lines
  63–79. The Selmer exact sequence and distinction between representing a
  covering and finding its rational points are the only imported context.
  Downloaded the exact arXiv v1 HTML inspected. No later algorithm, software
  performance result or complete analytic proof was audited.
- **Coppersmith (1993), Modifications to the Number Field Sieve**: read
  primary archived text lines 1–315, covering the introduction, sections 2
  and beginning of 3, printed pp.169–175. Used the explicit heuristic
  qualification on p.170, norm/character/actual-root structure, and multiple
  field construction. No NFS relation law or cost transfers to W004's rows.
  Copied the actual primary PDF and text. The source URL was recovered from
  H031's provenance ledger; that ledger's historical manifest was not copied.
- **Shallit, An Exposition of Pollard's Algorithm for Quadratic Congruences**:
  read archived text lines 1–110 and 325–360 (introductory modular equation
  and section IV cost qualification); inspected matching search contexts.
  Copied the actual primary PDF and existing text. The text has legacy glyph
  loss; no new formula whose reading depends on those losses is used.
  The accepted norm-gate review later supplied the narrower D=-1/base-case
  qualification, which governs the inherited cost boundary.
- **Boneh–Gentry–Hamburg**: read archived text lines 390–500, sections 5.1–5.2
  through Lemma 5.2 and the beginning of 5.2.1. This checks modular versus
  integral conic setup and the charged suitable-prime inputs. The full PDF
  and text were copied; Appendix C was not independently reread in W004.
  The later accepted norm-gate disposition governs the precise Norm2 match.

No AEM search was made in W004, before or after the lifecycle update. The
reviewer's six-search retrieval limitation is accepted as provided; none of
its search results or recursive manifests were duplicated. No fast Norm2
theorem is inferred from an abstract or from a historical source attribution.

The algebraic packet identities, square tests and curve equations in W004
are symbolic deductions stated as UNACCEPTED. Their primary-source comparison
does not claim those exact field laws are published, novel, or impossible.
