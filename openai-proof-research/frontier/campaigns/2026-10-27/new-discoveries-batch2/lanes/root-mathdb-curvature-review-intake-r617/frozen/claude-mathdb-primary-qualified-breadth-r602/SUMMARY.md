# Claude r602 — MathDB primary-qualified breadth (50 literal records)

Assignment: `lanes/root-mathdb-breadth-intake-r601/reserved-ids.json` + `queue.json` (immutable). Current authority bound: `lanes/root-mathdb-breadth-intake-r603` (coverage 6,033 record reviews; active lanes r600, r602, r604). Integrity pre-check `runs/check_intake.r2.json` PASS: r601 and r603 manifests (84/52 files, no extras), 72+40 original/copy pairs, r301 manifest, its 20 corpus chunks and 8 frozen inputs checked in place, reservation disjoint from current coverage, r600/r604, protected/adjudicated/hypothesis IDs and the r304/r363 ID tokens; completed r504/r598 IDs are in coverage, not re-reserved. The first check (r1) failed on an over-strict comparison and is kept.

## Coverage (honest)
- 50 new literal record reviews (IDs 334257–341382), each with chunk/line, line hash, canonical record SHA256 and exact UTF-8 statement (`dispositions.json`).
- Statement assessment: 26 self-contained, 14 definition-dependent, 6 scope-ambiguous, 4 incomplete. Only the 26 are counted as complete statements.
- Evidence: 5 primary passages read (338366, 338408, 334780, 340750, 339478); 42 abstract-level; 3 statement-only. No row is body-confirmed, proof-audited or registry-cleared.
- Retirements are abstract-level only: 334257 (Harper's own 1802.08355 abstract), 334674 (source proves it), 336053 (source refutes it), 335754 (Haslegrave proves the connected case; disconnected residual not cleared).

## Findings
- **338366 (Benson–Ralli–Tetali Conj. 4.1): exact counterexample, executed.** H = Cay(AGL(1,5), {a, a⁻¹, c, d}) has 20 vertices. Exact lazy Ollivier curvature κ ∈ {0, 1/8} on edges and ≥ 0 on all pairs. Spheres are [1,4,9,6] vs Z² [1,4,8,12]. H×Z (infinite, κ ≥ 0) has S₂ = 19 > 18 = S₂(Z³). **Likely fatal prior objection:** Bai–Lu–Yau (arXiv:2103.00941, Thm 11/Fig 35) publish a 4-regular Ricci-flat graph whose S₂ = 10 by a two-line count (hand deduction, adjacency not extracted). → Proposal P1, credit 0.
- **338408 (Dourado–Ehard–Penso–Rautenbach Conj. 1.3): literal counterexample K₃, b=3.** vacc = 1, but only the empty matching is affordable, with dyn = 0. Exhaustive n ≤ 5 finds only "boundary" failures (budget below every nonempty matching), and 150 random n=6 graphs find no non-boundary failure. Likely an endpoint correction. → Proposal P2, credit 0.
- Literal flaws with no credit:
  - 334780: the source intends symmetric K; the 1-D non-symmetric failure is K = [−1/4, 1].
  - 340750: the source restricts to l > n/2; the literal (6,4,1) fails through the swapped families. Exact (7,2,4): M = star, unique.
  - 339478: MathDB swaps bond and physical dimensions; in source notation the conjecture is routine for physical k ≥ 8 (injective EPR PEPS).

## Gates
Integrity PASS is not a math, novelty or acceptance PASS. Zero MathDB requests; current registry HOLD. No parked route touched (AIM/Kourovka/EGRES/AIProofWatch, DMGT, ProjectEuclid, ResearchGate, OEIS A274199). All 20 HTTP fetches (all 200) went to arxiv.org/export.arxiv.org over https with a generic User-Agent and no personal identifiers. All computation ran through the fixed helper guard (512 MiB / 210 s CPU / 230 s wall, unchanged). No Lean, manuscript, ledger or credit changes; no git; no children.

Counts unchanged: 9 additional / 39 total / next 40. Proposals: 2 briefs (P1, P2), both credit 0 pending root adjudication.

Failures/deviations: `failures.json` (F1–F8). Verify with `python3 -B verify.py <batch-dir>` (read-only, nonzero exit on mismatch).
