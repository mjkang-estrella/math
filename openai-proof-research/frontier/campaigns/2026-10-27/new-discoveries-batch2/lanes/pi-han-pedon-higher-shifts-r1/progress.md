# progress.md — pi-han-pedon-higher-shifts-r1

## 2026-10-28 07:15 UTC — setup
- Read ancestor AGENTS.md, batch AGENTS.md, ledger.json, prior-campaign-context.json,
  NEXT.md; checked prior metallic-Hankel credit (2026-10-26 campaign proved old E(1)
  at shift n+2 in Lean — excluded).
- Created lane directories; downloaded primary sources (curl); cloned metallicplus
  (read-only). Hashes in provenance.json. Access date 2026-10-28 UTC.

## 07:40 — machinery built (checks/metallic.py)
- Exact coefficients of Phi_n from eq (2.13) (O(N^2); capped N for memory).
- Shift triples (A^(ell), B^(ell), C^(ell)) by iterating source Lemma 2.6 with
  f_0 = kappa_i; series-level sanity assertion at the end of shift_triple (check_N=200).
- NextABC (Alg 2.3) with exact Q-arithmetic: D from the Step-2 congruence mod q^{k+2}
  (degree asserted <= k+1, D(0)=1); A*, B*, C* by Step 3; polynomiality asserted.
- Extraction of all Delta values via Han16 Thm 2.2 with prime-exponent bookkeeping
  (sigma_j = k_{j+1}, v_j = -a_{j+1}; integrality asserted at every s_j).
- Bug found & fixed during validation: missing q^k factor in the Step-2 second term;
  and an off-by-one in the sigma/v indexing (validated against direct Bareiss).

## 08:10 — validation against the source (all exact, zero mismatches)
- n=1, ell=3: pre-period 1, period 2, K-sequence matches Appendix A; determinants
  {-1,0,1}, antiperiod 4 (Theorem B).
- n=2, ell=4: period 9 from m=2; a-values (2, 1/4, 4, -1/4, 4, 1/4, 2, k=3, 1);
  determinant period string 1,1,-2,-1,2,-1,-2,1,1,0,0,0 = the string printed in the
  source introduction.
- Higher shifts: spot cross-validation vs Bareiss at j <= 15..40 for all seven shifts
  used in the data collection (see FINDINGS.md Section 3 list).

## 09:00 — structure probes
- k_m / a_m / triple-degree signatures for n=1, ell=4..9 (up to 150 steps).
- Consecutive-shift tail test: triple of Phi^(ell+1) not in orbit of Phi^(ell)
  ((1,4),(1,5),(2,5), 150 steps) -> higher shifts are not tails of one orbit.
- Partial products w_m extracted; explicit quasi-rational laws for n=1, ell=5.

## 10:30 — T-system
- Derived and proved the Hankel T-system; verified on 48 exact instances
  (checks/check_tsystem.py); wrote the reduction Proposition 2 with the double-zero
  gap analysis.

## 12:40 — data collection (checks/run_data_collection.py)
- 10 (n,ell) pairs, j <= 440, all residue classes mod rho_n fit exact quasi-polynomials;
  binomial coefficients + sympy factorizations recorded in notes/conjectureC-data.json.
- One timeout incident (O(N^2) coefficient generation at N=12000) fixed by capping the
  shift-triple sanity check to 200 coefficients; memory stayed well below 512MiB
  (peak usage dominated by a few MB of Python ints/rationals).

## 13:00 — write-up
- FINDINGS.md (full technical report: theorem, reduction, mechanism, data, failed
  routes, prior art, falsifier, scope), SUMMARY.md, discovery.md, this file,
  provenance.json.

## Limits / failures (candid)
- No uniform orbit law across ell found (slope-20 factors at ell=7 defeat the 4m+c
  ansatz; block lengths differ: 3 for ell=4, 4 for ell=5, other for ell>=6).
- Double-zero classes not closed within the T-system route.
- Wang–Xin–Zhai published body not read (HTTP 403); flagged in provenance.json.
- No Lean bridge produced (no complete theorem; explicitly out of scope per SUMMARY).
