# T088P133 contribution review, round 1 — REPORT

Provenance: Factory Droid / claude-opus-5-5 / high, 2026-10-20. Reviewer prose author: Myeongjin Kang (no
affiliation), CC BY 4.0; original code MIT. Role: independent SUBSTANTIAL-CONTRIBUTION review, conditional on
correctness, entire unchanged frozen scope. This report assigns no correctness verdict, no acceptance, no
count, and no priority or worldwide-novelty finding.

## Verdict

**SUBSTANTIAL (conditional on correctness)** for the entire unchanged frozen scope: every convex polytope K in
R^4 with nonempty interior and at most 6 facets satisfies V_4(ΠK) <= (160/3) V_4(K)^3, equality iff K is a
simplex. This is a bounded-class partial case of Brannen's reverse projection problem, reviewed as exactly
that, never as a solution of the general question.

The full reasoning, strongest-reduction comparison, primary-literature record, calibration against campaign
precedents, honest residual limits and positioning requirements are in
[packet/public/review.md](packet/public/review.md). Read and search extents and access failures are in
[packet/public/reading-limits.md](packet/public/reading-limits.md).

## Summary of the contribution analysis

- Strongest actual reduction: FHLX arXiv:2610.13953v1 Section 4 (independently obtained e-print/PDF/HTML; full
  TeX read) supplies only the lower bound and the n >= 9 counterexamples in the same n+2-facet class; no upper
  bound, no small-dimension positive result. Project r132 (PREFREEZE) reduced the class to the sharp
  inequality (★) and abandoned it unproved. The author's Lemmas 1–4/Proposition A complete that reduction and
  are explicitly credited/routine; this review agrees.
- Unpaid after that reduction: (★) at n = 4 with strictness. The new bridge paying it: log-concavity ⇒
  conditional-parts HNBUE Laplace majorization (classical tool, Klefsjö 1982/1983, new use here), an
  affine-in-scale separation to the scale-free condition (S)_n for b and −b, and an exact rational-coefficient
  certificate for (S)_4 over all ten sign patterns with strictness. (S)_n is a new sharp inequality for sums
  of independent exponentials, true exactly at n <= 4 and false for n >= 5 — a real threshold, not slack.
- Not REDISCOVERED: no prior statement of the theorem, of (S)_n, or of the bridge located (bounded searches
  and actual primary bodies recorded in reading-limits.md). Not TECHNICAL: no located composition yields the
  theorem; the integration closes a recognized open case (minimal counterexample class, first open dimension)
  with sharp constant and full equality characterization. Consistent with campaign SUBSTANTIAL precedents
  (t205m, t117q) and distinct from the TECHNICAL ones (t184i134, t106o133).
- Residual honesty: individual ingredients classical; (S)_4 is an exact computer-algebra certificate; scope is
  one dimension and one facet count; correctness not assessed here.

## Anchors

Author packet (immutable, verified against actual bytes at start and at sealing):
- FINAL `4656a93d80d1b67f4d349f3f95382ab8b03e644e45ad61b22629a86bd5c2cd09`
- MANIFEST `9ab6adfb17b4e612ad8bee1175109c15b73a1975b67dcc4c580dd955e3306324`
- REPORT `3659f82ea364b41303f4097e7df0d12ef380cab5a2d43b0f6bc39ed1405d49fd`
- frozen scope `86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354`
- proof `971506a4ea3de75a883da6d0eced6b11b0b997cc2a6598c2e0487ee5a6e2bc84`

This review packet (detached hashes also in FINAL.sha256 / REPORT.sha256 / MANIFEST.sha256):
- review MANIFEST (packet/MANIFEST.json) `66405c96dd6b76d25e7a290dc8d17d1f24abf489bcb2c45fd7e4deb8eef13656`
- review FINAL (FINAL.json): see FINAL.sha256
- review REPORT (this file): see REPORT.sha256

## Integrity and preservation

- All 39 start-hashed input files (author root, parent root, common brief, AGENTS.md, upstream.json,
  preprints-tree.json) re-verified unchanged at sealing (work/unchanged-final.json, 2026-10-20T17:57Z). The
  author root was never written or executed in. Two parent-side files added after the start snapshot
  (commit-validation.json, contribution-r1-dispatch.json) are recorded in work/parent-late-additions.txt; all
  originally hashed files unchanged.
- Copied controls inside this root (artifact checks, not mathematical gates; controls/control-runs.log):
  author verify.py PASS (files=24, directories=14) against the detached author anchors on a copy;
  certificate.py CERTIFICATE PASS (ten patterns, identity checks, strict monomials, negative control rejects
  (S)_5); geometry_control.py GEOMETRY CONTROL PASS (40 random 6-facet 4-polytopes, max ratio 0.999891 < 1,
  float only).
- This review's own read-only verifier: packet/public/verify.py with the detached review anchors reports PASS;
  copied tamper controls (packet/public/controls.py) behave as expected (CONTROL-RESULTS.json).
- Independent acquisitions: FHLX v1 (source/PDF/HTML), Saroglou 2011 via archive.org (origin host TLS failure
  reproduced, not bypassed), Saroglou 2015 v2 e-print, Crossref metadata (Klefsjö 1982/1983, Brannen 1996),
  all 13 pinned preprint blobs authenticated against the complete tree (SHA-256
  eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b). Register: work/acquisition-register.json.
- All work confined to frontier/campaigns/2026-10-14/t088p133-contribution-r1/. No nested agents, no
  git/shared-index writes, no author/input mutations, no publication/uploads/submissions/contacts/browser UI,
  no formal/manuscript/release stages. Active roots fresh-structural-discovery-r135 and
  t164f99-contribution-r1 were not entered. Private primary/upstream bodies remain local under their original
  rights.

## Handoff

Verdict SUBSTANTIAL (conditional on correctness) at the entire unchanged frozen scope. Next required gate is
the independent adversarial correctness review of the frozen author proof (sha256 971506a4…2bc84), which this
review did not perform; in particular the certificate interpretation, boundary/strictness and equality
arguments remain unreviewed mathematically. Positioning requirements PQ1–PQ5 (review.md Section 7) constrain
any later manuscript or acceptance record without changing this verdict.
