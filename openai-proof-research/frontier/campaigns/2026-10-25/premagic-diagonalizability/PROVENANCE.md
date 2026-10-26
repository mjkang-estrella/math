# Provenance and claim boundaries

- Author of this note and original code: Myeongjin Kang, with AI assistance.
- Prepared 2026-10-25 in the existing mathematics research workspace.
- Problem: MathDB 336488, *Diagonalizability conjecture for premagic matrices*.
- Original statement: Kardi Teknomo, *Premagic and Ideal Flow Matrices*,
  arXiv:1706.08856v2 (2018-05-06), Definition 4.3 and Conjecture 7.2.
- Published statement: DOI 10.32734/jocai.v3.i1-621 (2019), definition on
  page 37 and conjecture on page 44.
- Exact retrieval URLs, timestamps, byte counts and hashes are recorded in
  `sources/source-manifest.json`. Downloaded source bodies are retained
  locally for audit and excluded from the distributable archive.

Separate agents screened source statements, devised and reviewed the
linear-algebra argument, and developed the Lean proof. The parent checked
the proof-to-paper correspondence, compiled the release, ran the exact
arithmetic controls, and visually inspected every PDF page. Later formal
extension/review work explicitly used the requested ultrafast service tier.
These are independent AI checks within one project, not independent human
peer review.

The conjecture is refuted outright, rather than conditionally on an
unverified theorem. The source papers supply terminology and the target
statement, not assumptions needed to establish the counterexample.

A bounded search found no earlier explicit refutation. A related 2026
Springer chapter, *Premagic Patterns and Network Topology*, was identified
but its subscription-only body was not read. No first-in-the-literature
claim is made. General defective stochastic matrices are familiar; the
claimed deliverable is the explicit counterexample to the named statement
and its complete formal certification.

The original source review proposed the shifted matrix `M+I` as the main
witness. The final manuscript uses `M` for the shortest direct obstruction
and gives `M+I` as a stronger invertible example. Both are checked.

Only the mathematical counterexample and stated formal theorems are
certified. Database status, publication status and novelty are observations
or research judgments; Lean does not certify those.
