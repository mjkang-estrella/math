# 321413 focused completion result

**Zero credit; no Lean endpoint or acceptance claim.** The mathematical mechanism survived this investigation. There is now an explicit ordinary finite-certificate counterexample argument for **arXiv:1104.0904v1 Conjecture 2.10**, not just ranks or a generic-retraction example. Published-version comparison and the complete Lean proof remain unmet. Parked at those completion requirements; no new fatal mathematical obstruction was found.

The concrete admissible reduction is

    P* = P0 − (47/864) Q.

P0 comes from 713 thesis fundamental-identity terms; its complete multilinear top part was re-expanded exactly. Q is the 1374-term unnormalized polarization of the bound q. Both expanded polynomials are in `explicit-reduction.json`. Every term is multilinear with factors of length at most six; Q preserves the source Ax=e1 normalization.

The old interpretation gap is replaced by the explicit ten-term polynomial p in the **literal Lemma 3.2 polynomial generators**, with

    p = (T1 T35 + T4 T34 + T5 T33)/6
        − T7 T20/3 + T10 T23/3 + T11 T22/3
        − T12 T19/3 − T14 T18/3 + T16 T21/6 − T17 T24/2.

Its formal CE evaluation at T1=6,T35=1 and all other generators zero is 1; its actual matrix evaluation is zero. Explicit lower-identity combination witnesses connect q to p. No assertion that a computed lower span equals an elimination ideal is needed.

For the first selected tuple and its equal-multidegree stabilizer swap, exact certificates give

    R0(F(M)) = −47p/12,       (Rt−R0)(F(M)) = −72t p.

Both vanish at t=−47/864. The swap check matters: it would be incorrect to assume all other letter permutations have different multidegrees. Other degree-seven selected relations have different multidegrees; higher-degree generators cannot supply the missing nonzero degree-(3,2,2) relation. No one-dimensionality assertion is used.

Finite evaluation/inverse certificates prove injectivity of every centered CE component below degree seven: 80 components, 308 monomials, maximum square matrix size 21. This removes a large low-degree invariant-theory dependency from the ordinary argument. The proof explains the triangular centered-trace change of coordinates, the CE embedding, the source reduction constraints, recursion termination and the extension from traceless computations to full CE. See `ORDINARY-PROOF.md`.

Verification:

- `challenge.py` constructs the explicit elimination certificates and extracts the thesis reduction; limit 90 seconds, actual run under one second here.
- `low_injectivity.py` constructs exact matrix/inverse certificates; limit 90 seconds, actual run under one second here.
- `verify_certificates.py` independently re-expands the fundamental identities, polarization, thesis reduction, CE expressions, two stabilizer cases, scalar separator, all evaluation matrices and inverse products. It imports neither constructor and uses no ranks. Limit 60 seconds; actual run about one second. `verification.log` records PASS.
- All eight inherited input hashes match, recorded in `input-verification.json`. No inherited files were edited or evidence trees copied.

These certificates are **exact Python rational arithmetic, not Lean kernel certificates**. There is no theorem, #print axioms audit, Lean project or fresh extracted warnings-as-errors replay. No partial or conditional Lean theorem is presented as progress toward acceptance. The necessary formal work still includes the literal source definitions and all semantic and finite-arithmetic bridges.

Live prior/source checks: Palomar revision651 confirmed, Hoge query empty, trace-reduction query gives two unrelated hits. OpenAI math head remains 4eaee87548250b2682affda7d05d947c05554bae. Actual Benanti–Drensky Theorem3.1 and proof were read; the known degree-seven relations do not address every Hoge reduction. Meir's general infinite presentation and the later Poisson C42 presentation were inspected at the relevant theorem bodies; neither inspected result resolves the precise deformation assertion. This is a bounded screen, not novelty clearance.

The current arXiv page lists only v1. The author university page and bounded title/DOI searches did not supply the published 2012 body. The historical publisher403 was not retried or bypassed. No claim is made that the published conjecture is unchanged. Detailed provenance and remaining limits are in `source-provenance.json`, `prior-checks.json` and `results.json`.

No subagents, git operations, public posting, browser tabs, or writes outside this lane were used. Independent fidelity/significance reviews remain separate.
