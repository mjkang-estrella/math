# I311 — independent quantitative nilpotent scalar-gap proof review

**PASS unchanged. No necessary repair and no unpaid mathematical operation.** All 105 lines of I310 were independently checked at SHA256 `502d91e44fefdc9a0e396c7cad9a52e0cbd946873bad4cef2468eebc6e8fe7ef`. Its authentication metadata matches every recorded whole-file and passage hash. The proposal was not edited.

For every integer L≥2, every finite complex matrix A with A^L=0 and w(A)≤1, and every scalar Schur function f on the open unit disk, the exact reviewed conclusion is

    δ=2-max{1,||A||,...,||A^(L-1)||} ∈ [0,1],
    K_L=1+17·6^(L-1), D_L=1+2 sqrt(L) K_L,
    ||f(A)|| ≤ 2-(δ/D_L)^(2^L)/4.

L need only be a nilpotence bound. No dimension, degree, coefficient-complexity, boundary-continuity, or genericity hypothesis is added. A positive δ gives the stated explicit uniform gap.

The independent derivation in [analysis.md](../experiments/i311_quantitative_nilpotent_proof/analysis.md) verifies the complete quantitative chain:

- Radial Hardy estimates and conjugate coefficient tests yield the unweighted ordered-test bounds. The original positive resolvent compression gives γ²≤a²≤2γ²/(γ²-2)≤6 when γ²≥3. The diagonal nonconstant moments are bounded by ε/(2-ε)≤ε.
- The cross constant is 2m_0 because l_0=conjugate(m_0). Exact Parseval gives b=3|m_0|²+∑_(k≥1)|l_k|². Since 2/γ²-1<0, the lower bound a²≥γ² correctly gives b≤ε. This also bounds the entire backward resolvent by sqrt(ε).
- Positivity and the diagonal deviations give the determinant-slack budget 3ε and the L¹ flatness constant 17. The polynomial q(z)=∑conjugate(m_k)z^k/2 is the reflected conjugate of M/2; Haar reflection preserves its flatness. The exact identity is ||f-q||²=||f||²+a²/4-γ, yielding ||f-q||²≤ε without boundary continuity of f.
- The highest autocorrelation is c_d conjugate(c_0). Deleting a small endpoint, and dividing by z when deleting c_0, preserves the H² bound and propagates η_1≤6sqrt(η). The η≥1 and η=0 cases, padded degree, and zero polynomial are covered. Induction gives exactly C_d=(16·6^d-1)/5, with C_d≤4·6^d; conversion gives K_L and exponent 1/2^L.
- Evaluation uses exactly the first L coefficients and the pinned monomial bounds, giving 2sqrt(L)K_L. The j=0 case uses ||I||=1≤2-δ. The final inversion gives the claimed exponent 2^L and factor 1/4. The cases γ<sqrt(3), δ=0, and ε=0 satisfy the same bound unchanged.

Only the pinned original `thm:main` upper bound is stipulated. Its open-disk Schur extension and the disk resolvent calculation are explicitly justified; `thm:domain` is not misapplied when W(A) touches the circle. No equality theorem or qualitative compactness supplies any quantitative constant.

Finalized I308 review and analysis were authenticated and read under the dispatch authorization. Their qualitative PASS is background evidence; it was not treated as validation of Q310. The stale live-review wording in I310 and its metadata is superseded by that authorization. R019 is an application, not a premise of this general proof. I309 was not read, and no contribution or acceptance decision is made. This remains a quantitative part of the I307/I306 package.

**Repairs:** none. **Expanded justification:** the finite dual tests, negative-sign substitution, determinant-slack integral, conjugate reflection, induction factor 6^(1/2^(d-1))≤6, and boundary cases expand valid compressed steps without changing the statement or constants.

All actual input reads, provenance hashes, semantic extents, and bounded command failures are recorded in [input-authentication.json](../experiments/i311_quantitative_nilpotent_proof/input-authentication.json), [reading-and-failures.md](../experiments/i311_quantitative_nilpotent_proof/reading-and-failures.md), and [literature.md](../sources/i311_quantitative_nilpotent_proof/literature.md). No subagent, live sibling content read, git operation, publication, numerical scan, or shared-index edit was performed. Detached SHA256 hashes of the five authored files accompany the returned report.
