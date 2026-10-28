# progress.md — pi-qmotzkin-even-positivity-r1 (work log)

Solo lane (no subagents). All files confined to this lane. All arithmetic exact (dict-of-monomial /
fraction-free Bareiss); all jobs < 512 MiB; no floating-point surrogates anywhere.

## Chronology
1. Read batch/ancestor AGENTS.md; root screening lane (`root-qmotzkin-screen-r21`: SCREENING.md,
   source.txt 702,537 chars, retrieval.json). Confirmed A.4 text at offsets ~680,470–680,508 and that
   the first-batch record covers MathDB 339076 (typo refutation), NOT A.4/339078.
2. `compute.py`: exact recurrence (M_n, n ≤ 25), `hankel_det(r, n)` (fraction-free Bareiss);
   confirmed Δ_n^{(0)} = q^{β_n}, reproduced the source's shift-5 3×3 negative counterexample.
3. `reduce.py`, `wstudy.py`, `tp_test.py`, `tfact.py`: walk model (B = KD), Claim R (verified r ≤ 7,
   n ≤ 5), square identity with T = B^kD^{−1}; found T-minor mixed signs for k ≥ 2 (bug-fixed
   walk-weight convention: weight q^b for the new source height b).
4. Prior art (web, primary fetches): MathDB 339078 page (open, 0 solutions); Cigler 2204.09910v4;
   Cigler 2309.15557; Chen–Shi 2608.27208 (constant-parameter only); confirmed no resolution of A.4.
5. **Theorem A**: Desnanot–Jacobi identity on the Hankel array + A.2 + A.3 ⟹ first-order recursion
   and explicit monomial closed form for Δ_n^{(2)}; `toda.py`/`toda2.py` verify n ≤ 12 / n ≤ 14.
6. `gencheck.py`: exact positivity scan k ≤ 4 (n ≤ 7) all positive; odd shifts r = 3, 5 negative at n = 3.
7. Lean layer 1 (`lean/AxiomFreeMotzkin.lean`, sorry-free, dependency-free) + pins + BRIDGE.md roadmap.
   Sandbox has no Lean toolchain — file flagged compiler-unverified.

## Open (honest)
- k ≥ 2 of A.4: the central gap is a positivity mechanism for det[(B^{2k})_{n×n}] — either a
  sign-reversing/cancellation argument on the square identity's cross-terms, a closed form (or
  sign control) for the odd columns Δ^{(2k−1)} feeding the Toda recursion, or a new LGV model.
- Lean layers 2–3 (Claim R, Theorem A) need mathlib + a toolchain.

## Failed routes (documented for posterity)
- Direct total positivity of the Krylov matrix U: false (exact counter-minors).
- Naive Cauchy–Binet square-sum positivity for k ≥ 2: false per-minor (mixed T-minors).
- Specializing the constant-parameter Catalan-like machinery (Chen–Shi/Cigler): inapplicable.
