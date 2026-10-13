# I308 — independent full proof review of I307

**PASS unchanged. No necessary repair.** The complete I307 theorem and proof, all 101 lines, were independently reviewed at SHA256 `597263620687b02e8f98a9558b9816cfe539af34b24d95aa1dee7b21394f7e1b`. The supplied authentication metadata and all its whole-file and passage hashes match; passage hashes use joined lines without a terminal newline. The target was not edited.

For every finite complex matrix A with w(A)≤1 and spectrum strictly inside the unit disk, every open-disk scalar Schur function f satisfying ||f(A)||=2 has exactly the necessary form

    f(z)=η z^r ∏_(λ∈σ(A), λ≠0) ((z-λ)/(1-conjugate(λ)z))^(k_λ),
    |η|=1, 1≤r≤ν_0-1, 0≤k_λ≤ν_λ.

Here zero must be an eigenvalue with ν_0≥2 and ν_λ is the largest Jordan-block size at λ. No initial zero, polynomiality, rationality, boundary regularity, irreducibility, or nilpotence assumption is added. This is a necessary condition; no converse for arbitrary listed products is proved.

The independent derivation in [analysis.md](../experiments/i308_disk_extremizer_proof/analysis.md) checks each critical operation:

- Spectral-radius decay, rather than ||A||<1, makes the Taylor calculus and ordered products absolutely convergent. The bilinear coefficient functional pairs h_k with m_k, so the dual tests and equality recovery require complex conjugation.
- Radial Parseval proves the Schur H² multiplier contraction without boundary values. Polynomial tests give the improved unweighted bounds ∑|p_k|²,∑|q_k|²≤a²/4. The source's weighted Faber estimate is not silently strengthened.
- Direct congruence proves H=R+R*≥0 even when W(A) touches the circle. The positive compression and all Parseval constants give 2a²≤4+a²; p_0=q_0=1 gives the reverse bound. Equality forces a²=4, every nonconstant diagonal moment to vanish, m_0=0, and every backward moment to vanish.
- Cauchy–Schwarz recovers **every** Taylor coefficient, f_k=conjugate(m_k)/2, not just the finite evaluation jet. Thus f(z)=x*(I-zA*)^(-1)y/2 and f(z)=conjugate(M(conjugate(z)))/2. This also checks the orientation change from the source's boundary R(w^(-1)).
- Rational inner factorization and the reversed minimal polynomial locate uncancelled poles. Restoring cancelled factors of q gives numerator degree r+ℓ-ν_0≤ℓ-1. With zero absent the degree computation gives r≤-1; with ν_0=1 it gives r≤0. Both are impossible.

The nilpotent supremum criterion also **PASSes unchanged**, with the inherited w(A)≤1 hypothesis. For nilpotence index L, every norm-two Schur function is ηz^r with 1≤r<L, and the scalar supremum equals two iff one of those powers has norm two. Coefficient compactness makes a Schur supremum a maximum because evaluation uses only L coefficients. Radial dilation, uniform Taylor approximation, and normalization prove equality with the polynomial supremum. Consequently absence of a power equality gives a strict supremum gap. For L=1, A=0, the supremum is one and the empty power condition is false.

The claimed I306 consequence also **PASSes**: independent height-block multiplication gives

    ||N||²=(71+3√105)/32<4, ||N²||²=25/8<4, ||N³||²=7/4<4,
    N⁴=0, N³≠0.

The generic criterion therefore gives C_scalar(N)<2. R019's disk-bounded matrix polynomial attains two, and the stipulated pinned complete inequality gives C_complete(N)≤2, hence C_scalar(N)<2=C_complete(N). This does not rely on I287's polynomial-only monomial theorem or ACV Theorem 11.7. I306 and I307 are one downstream package, not two independent findings.

The actual pinned direct manuscript's `thm:main`, `thm:domain`, and ordered-test/positive-block proof were read. Only its polynomial upper bound is stipulated; no new equality theorem is imported. The extensions, compactness, factorization, and degree deductions were checked independently. The additional details in the analysis expand the existing proof; they do not replace a false step, add a hypothesis, or repair its statement.

This is a mathematical proof verdict only. No contribution verdict, new acceptance, count change, or priority claim is made; the supplied thirteen accepted findings remain thirteen. No subagent, live sibling review, git operation, numerical scan, publication, or shared-index edit was used. Input provenance and reading limits are in [input-authentication.json](../experiments/i308_disk_extremizer_proof/input-authentication.json), [reading-and-failures.md](../experiments/i308_disk_extremizer_proof/reading-and-failures.md), and [literature.md](../sources/i308_disk_extremizer_proof/literature.md). Detached hashes of the five authored files are returned separately.
