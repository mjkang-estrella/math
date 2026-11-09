# Bounded source and read-scope ledger

2026-10-08. This is one new review of the joint blinded sampler. No other
W005 mechanism was reassessed or delegated. Eight search queries, seven distinct
primary-document endpoints, and two terminal transport fallbacks were used.
Further opens of successful documents inspected/archived passages, not new
searches. Search stopped with the outcomes below. No TR85-001, Wiley or AEM
retrieval was attempted. This is not an exhaustive novelty search.

Queries, in order:

1. `"Hilbert 90" "uniform" norm one random torus`
2. `"norm one" "Z/NZ" Williams factoring`
3. `Rubin Silverberg torus based cryptography Hilbert 90 parameterization`
4. `Williams 1982 p+1 method factoring alpha conjugate Lucas pdf`
5. `site.shoup.net ntb square roots factoring random self reduction`
6. `"Hilbert 90" "blinding"`
7. `"Torus-based cryptography" "Hilbert" "2" Rubin Silverberg`
8. `"Rubin" "Silverberg" "u+1" "norm" torus`

Primary endpoints and outcomes:

- Rubin–Silverberg, *Torus-Based Cryptography*:
  <https://eprint.iacr.org/2003/039.pdf>, web internal error;
  <https://www.math.uci.edu/~asilverb/bibliography/ceilidh.pdf>, web 502,
  then bounded terminal fallback closed the connection;
  <https://iacr.org/archive/crypto2003/27290348/27290348.pdf>, web internal
  error. Full relevant theorem/proof NOT obtained. Search metadata and snippets
  are leads, not verification of the sampler's full contract.
- Rubin–Silverberg, *Compression in Finite Fields and Torus-Based Cryptography*:
  <https://www.math.uci.edu/~asilverb/bibliography/tbc.pdf>, web 502.
  Full pertinent proof NOT obtained. No additional fallback/retrieval loop.
- Williams, *A p+1 Method of Factoring*:
  <https://www.ams.org/mcom/1982-39-159/S0025-5718-1982-0658227-7/S0025-5718-1982-0658227-7.pdf>,
  web inaccessible and bounded terminal fallback HTTP 403. Full paper NOT
  obtained; no theorem from it is imported. Terminal errors retained in
  [source-access.json](source-access.json).
- Shoup, *A Computational Introduction to Number Theory and Algebra*, v2.5:
  <https://www.shoup.net/ntb/ntb-v2_5.pdf>, successful web PDF extraction.
  Read §§12.5.2–12.5.3, printed pp.351–353, especially unique prime-power
  lifting and the semiprime reduction's conditional-uniform-fiber argument.
  The discussion assumes a deterministic total square-root routine for its
  main example and explicitly leaves generalizations to an exercise. Our
  stopped-certificate proof is supplied independently. This is an author-written
  mathematical exposition, not an asserted earliest historical source.
- Marc Joye, published application WO2010145983A1:
  <https://patents.google.com/patent/WO2010145983A1>, successful primary-document
  text. Read the description's norm-one/Pell-conic parametrization, Proposition 1,
  projective versus affine representations over Z/NZ (web lines 212–256 and
  280–305), plus the explicit Delta=-1 specialization (lines 326–329).
  It treats N=pq with Delta nonsquare at both primes and discusses omitted
  mixed CRT points and nonunit denominators. This supports prior existence of
  composite-ring norm-one arithmetic and the chart issue. It does not by itself
  establish this exact uniform unit-pair sampler, repeated-prime-power law,
  stopping probabilities or W004 interface. OCR is imperfect; no delicate
  formula or claimed completeness theorem is imported as a proof. No legal or
  patent-status assessment is made.

Successful web-tool primary extracts are preserved as
[Joye](sources/joye-primary-web.json) and
[Shoup](sources/shoup-primary-web.json). These are tool-parsed document extracts,
not original PDF bytes; hashes in the delivery manifest identify those objects.
No failed download is represented as an acquired source.

Local read scope: AGENTS.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md, README.md,
docs/SPECIFICATION.md, the full 131-line assessed W005 sampler and 34-line exact
preregistration; W004 disposition; W004 independent review lines 1–160, 152–220,
and 290–459. The complete W004 main construction and accepted W003/W004
responses were supplied in the assignment and consumed as governing context.
STATE was context only: opening 150 and closing 110 lines (of 805) were read;
its historical middle was not reread. The archived task registry was preserved
without lifecycle actions. The full local snapshots do not imply every historical
file was reread. Fourteen direct input snapshots are hashed in inputs.json.

The user's authorized exact primitive screen overrides the earlier symbolic-only
default and general registry/iterate instructions for this task. Consequently
the exclusive standard-library evaluator was used without changing the solver
registry, shared protocols, STATE or any Lean source. The prescribed repository
check ran separately after adding the scratch source.
