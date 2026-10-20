# r133 analytic discovery: report (outside-packet anchor)

Author: Myeongjin Kang (no affiliation). CC BY 4.0. Runner: Factory Droid / claude-opus-5-5 / high.
Start 2026-10-20T16:47:42Z; freeze 17:21:32Z; sealed after FINAL.json. No gates, verdicts or count are assigned here.

**Status: full author-proof nominee at the frozen bounded-facet scope (unreviewed).**

Frozen theorem (packet/public/FROZEN-THEOREM.md, sha256 86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354):
every convex polytope K ⊂ R^4 with non-empty interior and at most 6 facets satisfies V_4(ΠK) <= (160/3) V_4(K)^3,
with equality if and only if K is a simplex. This is a partial case of Brannen's reverse projection inequality,
which is open in general for 4 <= n <= 8. It is not a solution of the general problem.

The proof is in packet/public/proof.md. It has three parts:

1. A credited reduction, completing r132's R1–R4 and (★) with full proofs. It gives P_4/c_4 = Ψ(α, b).
2. A new comparison step. Log-concavity of W makes its conditional positive and negative parts HNBUE, and the
   resulting Laplace bound reduces (★), through an affine-in-scale decomposition, to the algebraic inequality
   (S)_4: D(b) P(W>0)^2 <= 5 E W^+.
3. An exact non-negative-coefficient certificate for (S)_4 over all ten sign patterns (certificate.py).

The method stops at n = 4 because (S)_n fails for n >= 5.

Strongest integrated reduction: FHLX §4 + Minkowski equality + Gale + coarea/Gamma–Dirichlet, all routine. The
unpaid part for n = 5..8 is the unseparated box condition (the linearised inequality plus box faces). It is unproved.
Reading limits and late reads are in packet/public/reading-limits.md. Saroglou 2011 was not read (TLS failure).

Detached anchors:
- MANIFEST packet/MANIFEST.json sha256 9ab6adfb17b4e612ad8bee1175109c15b73a1975b67dcc4c580dd955e3306324
- FINAL FINAL.json sha256 4656a93d80d1b67f4d349f3f95382ab8b03e644e45ad61b22629a86bd5c2cd09
- REPORT: this file. Its hash is given in the final handoff and in CONTROL-RESULTS.json.

To verify, run from the root:

    python3 -B packet/public/verify.py --root . --manifest-sha256 <M> --final-sha256 <F> --report-sha256 <R> [--project-root ../../../..] [--math]
