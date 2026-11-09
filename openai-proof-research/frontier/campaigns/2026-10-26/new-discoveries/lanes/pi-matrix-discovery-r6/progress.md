# Progress log — lane pi-matrix-discovery-r6 (pi, solo)

Timeline of the run (all times relative; single session, no children, default speed).

## Phase 0 — Setup
- Read AGENTS.md, RESULTS.md, NEXT.md, ledger.json at campaign root. Counting standard
  and exclusion list internalized (332939, 332318, 375999 dead; 21 accepted outcomes).
- Confirmed output constraint: write only in `lanes/pi-matrix-discovery-r6/`.

## Phase 1 — Kill the supplied leads
1. **373707 (matrix zero-diagonal Conjecture 5, arXiv:2603.18253) — KILLED.**
   Careful read of the paper shows the "geometric proof of Theorem 5" never uses
   distinctness of the x_i/y_i. Verified numerically: 300k random repeated-row/col
   instances, zero violations, ratio ≤ 1 exactly. The repeated-pattern residue is
   already settled by the source's own Lemma 3.8 argument.
2. **369189 (Liu–Cheng reverse log-majorization, 2507.05242) — KILLED.**
   Literature search: Shi–Wei–Wang (LAA 739, 2026, DOI 10.1016/j.laa.2026.03.011)
   proved q ≤ 2p; Trung (arXiv:2607.01263, June 2026) completed the phase diagram with
   sharp counterexamples. Fully public; no residue.
3. **332493 (four-projection trace inequality) — HOLDS.** Refetched record (open, no
   solutions); exhaustive complex search over (K, a, b) rank configurations with
   Moore–Penrose constructions; min margin ≈ 4.7e-4.
4. **361461 (Bourin–Lee Conjecture 3.2, 2401.05456; = MathDB 365564) — HOLDS.**
   Derived a von Neumann necessary condition; large searches n = 3–5, m = 2–4,
   p ∈ [0.5, 6]; margins decisively negative.

## Phase 2 — Broad numerical screening of open matrix records
Fetched via MathDB API: 324727, 355466, 361693–96, 362175, 365564, 367551, 371031,
372905, 375342/3, 380287, 405532, 406427.

- 362175 (weighted-Frobenius commutator, 2403.04199): conjectured bounds TRUE and tight
  (after fixing two reduction-algebra traps); verified against the paper's equality case.
- 361693–96 (Lu–Wenzel/DDVV cluster): TRUE/tight; T_X superoperator formula verified to
  1e-14; earlier "violation" traced to a missing hypothesis (Conj 4.9 needs Frobenius
  orthogonality AND tr(B_α[B,B_β]) = 0).
- 372905 (sharp 3-operator Clarkson): no violation at p = 3, 4; p = 2.5 run numerically
  unstable — unresolved.
- 406427 (Lin–vdD compression): no violation at p = 1, 1.5, 2.

## Phase 3 — The 371031 campaign (Tang–Zhang closed form)
1. Fetched full text of arXiv:2510.16846 (published LAA 731 (2026) 196–204).
   Conjecture 3.1: closed formula for c_p(m) for ALL p > 1; extremal conjectured to be
   the shared-left equiangular rank-one family (sharp at p = 2).
2. Built the correct reduction for rank-one A_k = u_k x_k*:
   ‖ΣA_k‖_p^p = Σ λ_i^{p/2} (λ_i = eig of S*S), ‖Σ|A_k|‖_p^p = Σ δ_i^{p/2}
   (δ_i = eig of Σ x_k x_k*), with per-k scales t_k = ‖u_k‖‖x_k‖ entering linearly.
   (Three wrong variants of |A_k| were identified and discarded — see discovery.md.)
3. Structured family optimization (Gram magnitudes ρ_u, ρ_x + phases): violations found
   at p = 1.1, 1.25, 1.5 (m = 2, 3, 4); best margin p = 5/4, m = 3: +8.31e-3.
   No violation at p ≥ 1.75; converges to the formula as p → 2⁻ (consistent with the
   proven sharp p = 2 case).
4. Verified the paper's own extremal family reproduces the formula exactly (15 digits)
   for all tested p — the refutation requires two-sided (non-shared-u) configurations.
5. Exactification: 3-decimal rounding → stereographic projection to EXACTLY rational
   unit-norm columns (Q[i]³) → excess preserved at 8.3144e-3, stable across rounding
   depths 3–10.
6. **Exact certificate** (`certificate.py`): char polys of S*S and Σ|A_k| have real
   rational coefficients; roots isolated by sympy; c^{5/4} = y^{5/2}/(2(y⁴+2)^{3/8}),
   y⁵ − 2y⁴ − 2 = 0, monotone (symbolic derivative check); 80-digit interval comparison.
   **Certified gap +0.0357923.** Secondary 60-digit direct check agrees (ratio
   1.01906799113… vs 1.01075360838…).
7. **Mandatory prior-art search — SCOOPED.**
   - MathDB 371031 live: status open, solutions [] (no posted solution there).
   - GitHub trureturing / count-ex-machina: no file hits for 371031 / 2510.16846.
   - Web search on the paper's citers: **arXiv:2608.15558** (2×2 real rank-one
     counterexample at p = 3/2, ratio > 207/200, seven rational inequalities) and
     **arXiv:2608.18112** (disproof for every m ≥ 2 and every 1 < p < 2).
   - Conclusion: conjecture publicly refuted in Aug 2026; independent refutation has
     no credit. Target closed as *rejected: scooped*.

## Phase 4 — Write-up
- discovery.md (honest outcome + full technical documentation), provenance.json,
  artifacts (witness_exact.json, certificate.py, final_verify.py, build_exact.py,
  rounded-witness npy files, best_fam4.pkl).

## Honest gaps
- Records 324287, 324727, 329181, 329636, 336251, 342339, 351613/614, 355466, 359049,
  360938/9, 361460, 365563/5/6, 367551, 369147, 370004, 372758: **never screened**.
- 372905 p = 2.5 numerical blowup unresolved.
- No PROOF.md written (no eligible discovery).
