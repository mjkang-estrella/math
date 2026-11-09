# H030 source identity and reading scope

2026-10-08. Supporting evidence for H030-root-product-blocks.md. This file is
proposer provenance, not an independent mathematical review. No finite research
experiment or candidate implementation was run.

## Project inputs

Read completely: AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, the intake version of research/STATE.md, H030.md, corrected
H029-power-cover-construction.md (306 lines), H029-disposition.md (76),
H029-independent-review.md (622), H004-reduction-review.md (464), and
H004-disposition.md (30). Long files were read in successive ranges; truncated
combined outputs were followed by the missing ranges.

The four task-supplied H030/H029 hashes matched before construction work. The
report preserves those hashes. Twelve project documents were copied to flat
H030-block-input-* filenames and hashed in H030-block-inputs.sha256. The hash
manifest was checked against every saved copy. Copies do not modify originals.

STATE changed legitimately while this child was working. The completely read
intake version had 542 lines and the stale instruction to consume H029's
review. The later archived copy has 555 lines and records H029's acceptance
and H030 as the active task. The opening 35 lines of that copy were inspected
to identify this change; the entire newer copy was not reread. Its hash is
an archival identity, not a claim that it equals the earlier read bytes. In
both cases the user's authoritative handoff and H029-disposition.md govern.
No prior-task registry or child status was polled, and no coordinator work was
duplicated. The original 300-line H029 submission was not changed or newly
reviewed in this round.

## Primary literature actually inspected

### David Harvey, arXiv:2010.05450v1

Title: *An exponent one-fifth algorithm for deterministic integer factorisation*.
Primary URL: https://arxiv.org/html/2010.05450v1 .
Saved HTML: H030-block-Harvey-2010.05450v1.html.
SHA-256: `bcd347a997cb82fbc918cac33763762537bc01c797fce3a29f0bc3e0c2c6d0cb`.

Read §§2.1–2.3 (integer arithmetic, polynomial tools, and Strassen's method),
including Lemmas 2.1, 2.3 and 2.4 and Proposition 2.5 with their displayed
arguments. Also read Lemma 3.3 and its proof, and all of Remark 3.4. The web
tool exposed neighboring text in §4; no complete §4 or whole-paper audit is
claimed. H030-block-Harvey-2010.05450v1.txt is a newly extracted reading aid
from the saved HTML, retaining MathML alttext. The existing H029 Harvey text
was also consulted to locate passages; it is not treated as a second source.

Scope used: general packed coefficient widths, product trees with input
lists, the familiar small-factor routine, and the already stated question
about a full square-root speedup at Lehman's original search parameter.
Harvey's unit-based geometric evaluation lemma is not the arbitrary-point
monic remainder routine used in the H030 construction.

### Alin Bostan, Pierrick Gaudry, Éric Schost (2007)

Title: *Linear Recurrences with Polynomial Coefficients and Application to
Integer Factorization and Cartier–Manin Operator*.
SIAM Journal on Computing 36(6), 1777–1806.
DOI: https://doi.org/10.1137/S0097539704443793 .
Author-hosted primary PDF: https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf .
Saved PDF: H030-block-Bostan-Gaudry-Schost-2007.pdf.
SHA-256: `aa0c8f3f59acea0dc538a61ad21b1e376e38783d70dc511edff384fa64b9393f`.

Read the introduction and algorithmic ideas on printed pp. 1777–1780, the
opening computational-model discussion on p. 1781, the end of §3 around its
Remark 2, §4's setup, Lemmas 6–7, Theorem 8 and the beginning of its proof
(pp. 1786–1787), and Lemmas 12–13 with their proofs (pp. 1790–1791).
Theorem 8's entire recursive proof and the whole paper were not audited.
The scope distinguishes the ordinary arbitrary-ring factorial method from
the more refined procedure with explicit invertibility hypotheses and its
factoring-specific nonunit handling.

The adjacent .txt is `pdftotext -layout` output. Formulas were read from the
local extraction and the web tool's primary-PDF text. The web tool was also
asked for page screenshots (PDF indices 3 and 14); only screenshot references,
not inspected image contents, entered this transcript. No claim of visual
verification depends on those references. No source theorem is credited with
constructing the unknown rounded-root sequence.

### David Harvey and Markus Hittmeir, arXiv:2105.11105v1

Title: *A log-log speedup for exponent one-fifth deterministic integer
factorisation*.
Primary URL: https://arxiv.org/html/2105.11105v1 .
Saved HTML: H030-block-Harvey-Hittmeir-2105.11105v1.html.
SHA-256: `ae7e7ebc34e4295f971c91cc8276aab785fc60fbc05e24291e79d60c3ed8575e`.

Read the abstract, opening introduction through Theorem 1.1 and its
small-factor reduction paragraph, including the definition of the finite-tape
bit model. Web results also exposed later neighboring passages; the full
algorithm/proof was not audited. The adjacent .txt is a new extraction from
the saved HTML. The sole complexity comparison used is the stated full
deterministic factorization upper bound.

## Limits and evidence operations

These are a focused primary-literature check, not an exhaustive novelty
search or a certification of the latest worldwide factoring record. The
matched exponent-1/5 reference is inherited from the task and checked in the
primary theorem. Lehman's original paper, the complete Hittmeir cover paper,
Umans–Wang, and the polynomial-arithmetic textbook were not newly read for
this H030 attempt. H029/H004's accepted local reductions were read directly;
their mathematical prerequisites are inherited within that accepted scope.

All three primary documents downloaded successfully. An initial HTML-reading
aid command mistakenly treated the dot in an arXiv identifier as a suffix;
it failed to open a filename before writing anything. The corrected extraction
used the exact filenames above. This was an evidence-conversion error, not a
candidate execution or research outcome. Full primary files are preserved;
reading aids and hashes do not imply complete reading.

H030-block-delivery.sha256 hashes the completed report, this note, all input
copies and their manifest, and the three primary snapshots with their reading
aids. It excludes itself. Final checks are artifact identity and link checks
only. No `scripts/check.sh`, factoring solver, arithmetic experiment, numerical
case calculation, benchmark, proof assistant or package install was run.
