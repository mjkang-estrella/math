# W006 rational review: bounded source and input ledger

2026-10-08. Eight search queries only; no novelty conclusion from missing hits.
All local writes use the assigned W006-rational-review prefix. No experiment,
candidate transition, pilot, graph enumeration, model delegation or thread launch.

## Local scope

Read AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, README.md,
docs/SPECIFICATION.md and the full current STATE (825 lines). Read all of
W006-rational-map.md, W006-powered-blindnorm.md and W006-rational-map-prereg.md;
W005-blinded-norm2.md, W005-blindnorm-review.md, W005-blindnorm-disposition.md
and the W005 source ledger. Read W001-dynamics.md for the retained power-image
control. Historical STATE references are context, not fresh audits of those
reports. Did not reopen the coefficient/cyclotomic or reflection branches.

[Input manifest](W006-rational-review-inputs.json) identifies 15 byte-for-byte
snapshots. Original mutable STATE is not an output owned by this review.
Input snapshots were taken after reading and before report authoring; they
are not a candidate/runner execution freeze. No such code was constructed.

## Searches in order

1. `cubic rational maps z (z^2+a) / (a z^2+1) dynamics`
2. `Milnor On Lattes maps fixed point multipliers power Chebyshev maps pdf`
3. `Williams p+1 factoring algorithm 1982 mathematics computation pdf`
4. `Pollard 1974 theorems factorization primality testing proceedings Cambridge`
5. `"cubic" "rational maps" "az" "automorphism" Klein four`
6. `"z(z^2" "az^2" rational maps`
7. `"Williams" "A p+1 method" pdf -site:ams.org`
8. `Pollard 1975 Monte Carlo method factorization BIT pdf`

Secondary indexes were discovery leads only. The first search response was
not archived as an entire raw object; queries and outcomes are retained here.
The second query batch and subsequent saved retrievals are in web-2 through
web-7 JSON files; screenshot transport responses are in web-screens.json.
These are tool responses, not original publisher PDF bytes.

## Primary sources and actual inspected scope

- John Milnor, *On Lattes Maps*, Stony Brook IMS Preprint 2004/01, revised
  September 2004, <https://www.math.stonybrook.edu/preprints/ims04-01.pdf>.
  Successfully inspected extracted text of section 2, Theorem 3.1, Lemma 3.4,
  and Corollary 3.9 with its proof (printed pp. 2-8). These supply definitions
  of power/Chebyshev/Lattes maps and the fixed-multiplier modulus restriction.
  The rational-parameter exclusions and finite-ring basin results in the
  review are deductions made here, not theorems attributed to Milnor.
- Lloyd W. West, *The Moduli Space of Cubic Rational Maps*, arXiv:1408.3247,
  <https://arxiv.org/pdf/1408.3247>. Inspected abstract/introduction and section
  3.3, extracted Table 4 on printed p. 14. The PDF shows an arXiv v1 header
  dated 2014 and an internal date October 14, 2018; this ledger does not
  resolve that version discrepancy. Cubic maps with nontrivial automorphism
  groups and their one-dimensional dihedral strata are established study
  objects. No exact earliest-priority assertion for the present formula or
  finite-ring stopped algorithm is made. The table uses binary-form normal
  forms; it is not treated as a literal match of our parameter a.
- Richard P. Brent, *An Improved Monte Carlo Factorization Algorithm*, BIT 20
  (1980), 176-184, <https://maths-people.anu.edu.au/~brent/pd/rpb051i.pdf> and
  author landing page <https://maths-people.anu.edu.au/~brent/pub/pub051.html>.
  Inspected sections 5-7, printed pp. 181-183, including the explicit
  random-function assumption and gcd/cycle extraction. Supports classifying
  the proposed collision alternative as a Pollard-type control, not a new
  uniform success theorem for F_a.

## Failures and limits preserved

- Pollard 1974 Cambridge endpoint
  <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0305004100049252>
  returned an internal error. No retry or theorem imported from its full text.
- Montgomery 1987 institutional copy
  <https://wstein.org/edu/124/misc/montgomery.pdf> returned a 23-page PDF with
  zero extracted lines. Screenshot calls for pages 0 and 1 produced no
  inspectable image payload through this tool transport. Its substantive text
  is UNINSPECTED here; W001's cited scope is background only.
- The analogous West page-13 screenshot also did not deliver an inspectable
  image; only the extracted text listed above was used. No table equation
  requiring visual disambiguation supports the mathematics in this review.
- Williams's full paper was not acquired. The earlier W005 failed AMS
  endpoint, and its already failed Rubin-Silverberg endpoints, were not
  retried. Search metadata is not substituted for their proofs.
- No search of unrelated coefficient/cyclotomic or quaternion literature.
  These finite searches neither establish novelty nor rule out existing
  exact finite-field graph studies of this family.

The omission decision and all 60 unstarted cases are in
[unstarted ledger](W006-rational-review-unstarted.json). No scratch source
code was added or changed, so the instruction to run scripts/check.sh after
scratch-code changes was not triggered. No test result is claimed for this
symbolic-only review. No Lean proof or complete factoring implementation was
created.

Editorial/tool failures: two apply_patch attempts used unmatched context
while adding final domain clarifications. Both failed before changing a file;
the actual context was read and the subsequent patch succeeded. These were
document-edit failures, not candidate runs or mathematical observations.
