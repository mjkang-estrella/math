# H030 independent-review provenance and reading scope

2026-10-08. Evidence handling only; no finite research computation was run.

## Frozen project inputs

Read completely: AGENTS.md (26 lines), README.md (73), docs/SPECIFICATION.md
(122), RESEARCH_LOOP.md (77), RESEARCH_TEAM.md (63), start-of-review research/STATE.md
(580), research/hypotheses/H030.md (95), H030-submitted-draft.md (482),
H030-intake.md (56), H030-block-source-notes.md (117), the corrected
H029-power-cover-construction.md (306), H029-disposition.md (76), and
H004-disposition.md (30). Long/truncated combined outputs were followed by
smaller complete ranges. The user-supplied original brief and handoff also
governed the audit. No task registry or live child status was read or polled.

Accepted dependency reading was deliberately focused: H029-independent-review.md
lines 131-208 (section 3), 300-622 (the end of Card A, all sections 5-7), and
H004-reduction-review.md lines 1-280 and 317-407 (sections 1-4, 5B-6). The
corrected H029 report and both dispositions were read in full. These are accepted
dependencies; H004's old finite checks were not replayed or newly reviewed.

The read STATE version describes H030 as live. The authoritative task message
says it is completed; this review did not resume or duplicate construction.
H031 is mentioned in required STATE reading, but no H031 brief, intake, draft,
evidence, or status was opened separately. No H031 work was attempted.

Both H030 proposer manifests were checked before the review: 12 frozen-input
and 21 delivery entries all matched. The report and submitted snapshot both
matched f66360ee379188f50b83fb1f11fff43536aa3c2beb18c6a05118d4986b864581;
the intake matched
7cfe2a8d1c53a8b4c2946de9a7082c5cf850bb3bb29b6716de3abd6f3d124777.

Thirty-six byte-identical snapshots were created as flat adjacent
H030-review-input-* files. Their original paths and identities are recorded in
H030-review-originals.sha256; the review-copy paths are in
H030-review-inputs.sha256. These include every original H030-block-* artifact,
both of its manifests, current governing documents, and the accepted dependency
files above. Duplicate source identities across snapshots are intentional.

The H030-block-input-STATE copy is a historical proposer snapshot; it was
preserved and hashed, not conflated with the 580-line STATE actually
read here. No claim of rereading all nested historical copies is made.

## Primary evidence actually inspected

The three primary URLs below were opened successfully through the web tool in
this review. The archived source files and reading aids are included in the 36
review snapshots. Local reading aids were consulted alongside the refreshed
online passages. There was no new local source download or extraction: frozen
proposer source files were reused. No hash comparison between a freshly
downloaded file and the old web snapshot is claimed.

### David Harvey

*An exponent one-fifth algorithm for deterministic integer factorisation*,
arXiv:2010.05450v1, 12 October 2020.
[Primary HTML](https://arxiv.org/html/2010.05450v1).

Archived HTML SHA-256:
`bcd347a997cb82fbc918cac33763762537bc01c797fce3a29f0bc3e0c2c6d0cb`.
Archived reading-aid SHA-256:
`9884f58cfae3c92a875b5af39d2c06e774dab479b71f8731781722ea0c533630`.

Read sections 2.1-2.3 (including Lemmas 2.1-2.4, Proposition 2.5 and their
arguments), Lemma 3.3 with its proof, and all of Remark 3.4. HTML source lines
101-192 and 219-268 locate these passages. Incidental neighboring material was
exposed; no whole-paper or section-4 audit is claimed. The report uses only the
listed arithmetic/tool attribution and the final question in Remark 3.4.

### Alin Bostan, Pierrick Gaudry, Eric Schost

*Linear Recurrences with Polynomial Coefficients and Application to Integer
Factorization and Cartier-Manin Operator*, SIAM Journal on Computing 36(6),
1777-1806 (2007), DOI 10.1137/S0097539704443793.
[Author-hosted primary PDF](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf).

PDF SHA-256:
`aa0c8f3f59acea0dc538a61ad21b1e376e38783d70dc511edff384fa64b9393f`.
Archived pdftotext reading-aid SHA-256:
`c123b7df59199562a819f6972500f776872c3d4dd2e3f61b2381a523ae1805e7`.

Reading: title/DOI and selected introductory/model passages on pp. 1779-1782;
section 4 setup, Lemmas 6-7, Theorem 8 and
opening proof, pp. 1786-1787; Lemmas 12-13 and proofs, pp. 1790-1791;
appendix through evaluation/interpolation, pp. 1802-1803. Unrelated neighboring
text appeared in one locating read. No whole-paper, whole-Theorem-8-proof, or
visual-rendering audit is claimed. The original PDF was web-accessible; local
text and primary web extraction supplied the formulas inspected here.

### David Harvey and Markus Hittmeir

*A log-log speedup for exponent one-fifth deterministic integer factorisation*,
arXiv:2105.11105v1, 24 May 2021.
[Primary HTML](https://arxiv.org/html/2105.11105v1).

Archived HTML SHA-256:
`ae7e7ebc34e4295f971c91cc8276aab785fc60fbc05e24291e79d60c3ed8575e`.
Archived reading-aid SHA-256:
`5c42d9b061324eb52b3ffb2a0ae80fd4cb0d6336040155484935ad01d676ed0a`.

Read abstract, introduction through Theorem 1.1 and the following small-factor
reduction paragraph, including the finite-tape bit-model definition (HTML
lines 29-50). Neighboring overview text was exposed. The proof of the full
algorithm was not re-audited. The comparison is deliberately historical.

## Retrieval limitations and final checks

No primary retrieval failed in this independent review. This does not erase
the proposer's recorded failed filename-conversion attempt, which remains in
the unchanged H030-block-source-notes.md. H029's accepted report records HTTP
403 for the original Lehman publisher PDF; this reviewer did not retry it or
claim to have read that proof. The complete polynomial-arithmetic textbook was
not fetched or read. No current-record or exhaustive novelty search was made.

No numerical examples were generated to test any lemma. File copying, source
inspection, SHA-256 checks, report authoring, and report/link validation are
evidence operations only. There was no candidate program, test script, solver,
timing call, Lean invocation, shared check, package installation, or delegation.

H030-review-verification.json records final identity and local-link checks.
H030-review-delivery.sha256 seals the report and all owned review artifacts
except the delivery manifest itself. Original-input rechecking found only a
shared STATE change during this review. Its read-version hash is
`a9b0db6cc6d02fc8e8034870e3e4bf149f56582ec40b318e3b6a885f4d0f26a5`;
the subsequently observed hash is
`02bb3188735ca112b4c68bb5e5b8e8b0aaecba35f1ceca0377da8fcfd56d5c03`.
This reviewer never wrote STATE and did not replace its frozen read version.
All original submissions, accepted dependencies, H030-block-* evidence, and
the 36 review snapshots matched. No claim about the cause or authorship of the
external STATE edit is needed. Acceptance of proofs comes from the reasoning
in H030-independent-review.md, not the seals.
