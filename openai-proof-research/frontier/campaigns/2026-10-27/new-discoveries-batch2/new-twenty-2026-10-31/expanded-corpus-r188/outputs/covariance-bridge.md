# 355321: complete ordinary proof, excluded as a classical bridge

The literal target is Conjecture 6.8 of Reitzner–Römer–von Westenholz, arXiv:2207.05450v1, not the critical-regime Conjecture 7.9. The hypotheses in Section 2 are −d/2 < τ₁ < ⋯ < τₙ. Section 6, equations (7)–(8), writes Σ = c C, where c = V(W)dκ_d/2 > 0 and Cᵢⱼ = 1/(xᵢ+xⱼ), with 0 < x₁ < ⋯ < xₙ and xᵢ = τᵢ+d/2. The nondegenerate body W and positive dimension are the source's setting; replacing them by degenerate data would be an inadmissible endpoint correction.

For increasing row indices i₁ < ⋯ < iₖ and column indices j₁ < ⋯ < jₖ, the classical Cauchy determinant identity gives

 det C[I,J] = (∏_{a<b}(x_{i_b}−x_{i_a})(x_{j_b}−x_{j_a})) / (∏_{a,b}(x_{i_a}+x_{j_b})) > 0.

Thus C is strictly totally positive. Pinkus, *An interlacing property of eigenvalues of strictly totally positive matrices*, Linear Algebra Appl. 279 (1998), pp. 201–206, Theorem A, states that every such square matrix has positive simple eigenvalues. This yields the conjecture immediately, since multiplication by c preserves simplicity.

For clarity, the simplicity implication is also the standard compound-matrix Perron argument. C is real symmetric positive definite (also the source's Corollary 6.2), so let λ₁ ≥ ⋯ ≥ λₙ > 0 be its eigenvalues with multiplicity. For each k < n, the kth compound matrix has strictly positive entries (the minors above), and eigenvalues the products of k distinct indexed eigenvalues of C. Its spectral radius is λ₁⋯λₖ and is simple by Perron–Frobenius. If λₖ = λₖ₊₁, that product occurs at least twice, a contradiction. Consequently all λᵢ are distinct.

Credit verdict: do not nominate. This is a routine consequence of the source's own displayed Cauchy matrix and classical determinant/Perron–Frobenius theory. No new structural lemma is required. The source conjecture label does not change this assessment. No Lean formalization was attempted, since a formalization would earn no discovery credit. Publisher-version body was not recovered; no claim is made that the 2024 journal retains this exact conjecture unchanged.

Primary evidence: sources/355321-v1.txt lines 127–158 and 512–538, sources/pinkus-primary.txt Theorem A. HTTP bodies and receipts are retained beside them. The older source arXiv:1709.09011 versions were also acquired; their independent full proof audit is not claimed.
