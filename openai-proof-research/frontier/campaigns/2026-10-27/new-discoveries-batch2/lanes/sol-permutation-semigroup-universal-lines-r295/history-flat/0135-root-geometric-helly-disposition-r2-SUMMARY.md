# r271 handback (Claude Opus 5.5, solo)

**No full solution or refutation; no PROOF.md; no nomination.** Counts unchanged: 9 additional / 39 total / next 40. Root alone accepts and counts.

**Main lead: Swanepoel's c.s.c. Helly question** (Garber–Roldán-Pensado arXiv:1801.07238v1 p1; Period. Math. Hung. 79 (2019)). Source PDF frozen, and a fresh arXiv fetch is byte-identical. Single arXiv version; OpenAlex shows 0 citing works; Semantic Scholar 429 (not retried); no arXiv successor; no project alias.

Rigorous results here. All are ordinary reductions or helpers, not credit:
* **Literal scope.** "Any planar set" is false for every k: every finite subset of the parabola y = x² is c.s.c., but the parabola is not (domain correction). Vacuity forces |X| ≥ k.
* **Theorem T (transfer).** The finite property for k implies the bounded-set property for k. Proof via FIP compactness and a recession-direction argument when centers escape to infinity. So the real question is exactly the finite one.
* **Lemma A.** An exact critical-direction criterion for admissible centers gives an exact Fraction decision procedure. It is validated against brute force (0 mismatches in ~50k pairs) and reproduces the source's nine-point minimal example.

Mechanism (a), near-symmetric perturbations: first order, this regime is exactly an ordered line-transversal problem. Hadwiger's theorem then caps minimal obstructions at 3 antipodal pairs (6 points). The model matched the exact test on 504/504 instances. So symmetric perturbative families cannot produce unbounded minimal obstructions. This is the strongest classical objection to route (a).

Mechanism (b) and the triangle route: the tempting "three triangles always witness" (which would give k = 9) is **refuted exactly** by a six-point minimal obstruction. Triangle center-set intersections have up to 8 components, which blocks a direct topological Helly argument.

Exact adversarial searches never produced a minimal obstruction with more than 9 points:
* about 8,300 greedy reductions;
* perturbed regular 11-gons gave zero minimal obstructions;
* hill climbs to 10 or 11 points stalled at 9 c.s.c. deletions.

This is finite evidence for the **conjecture k = 9**, not a proof.

Scouting: 13 distinct attributed families screened (SCOUTING.md). Six are answered in-source or publicly (Bárány ellipses, Bárány–Jerónimo-Castro norm lemma, FLM 3.7, Kolountzakis, Matheron planar covariogram, Socolar parquet). Four are rejected as open-ended or famous-hard (Dougherty, Elkies, Kenyon–Solomyak, Siersma–van Manen). Ranked leads: (1) Swanepoel; (2) Bergman's octahedral-skeleton mapping radius in the Euclidean plane, Question 6 (interval [1/√3+1/2, 7/6]); (3) Konyagin–Łaba arbitrary-slope polygonal Falconer question (partly answered by math/0407503).

Files: discovery.md (proofs, mechanisms, missing statement), SCOUTING.md, progress.md, FAILURES.md, exact-checks.json (run_checks.py), scripts and logs, primary/ with access.jsonl, derived/, bindings.jsonl, source-postcheck.json, history-coverage.json (876 refs verified in place), provenance.json, final-manifest.json (excludes itself and verification-receipt.json), and a separate guarded verify.py.
