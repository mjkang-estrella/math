# Publication check

The publication assistant read R016, the completed I242 equality proof, the full I245 proof review and analytic expansion, and I246 contribution review at public research revision `013c239d257cb6f9956d3d5724fd7a726770c43b`. These are AI research records, not human peer review. The source proof was checked rather than treating its PASS label as external verification.

The manuscript states the complete polynomial bound and analytic Faber coefficient estimate as Assumption 1.1. Their exact source is OpenAI's direct Crouzeix manuscript, Theorem 1.1 and Proposition 2.2, at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The primary source's main theorem and Sections 2–3 were read, including both ordered multiplier tests and the unnormalized Hilbert–Schmidt conventions. Its analytic outer approximation lemma was also inspected. These stipulated source results were not independently audited for truth.

The structural companion's representation and density statements were inspected to distinguish the original matrix's mass-two resolvent from the similar matrix's mass-one density. No inference of scalarity is taken from matrix-valued maximum-modulus saturation.

The new deduction was checked at its potentially delicate points: fixed active irreducible block; exclusion of boundary spectrum; exterior derivative bound; uniform 1/k Fourier tails; strong L2 rather than weak boundary convergence; bounded fixed-pair Faber norm; exact residual with coefficient three; L1 passage of the quadratic trace; total isotropy and inertia; simple-support existence in dimension four; positive curvature; base-first tensor conjugations; and the confinement of all other reducing summands by the extracted scalar monomial. No proof gap was found in the stated conditional deduction.

External scalar inputs are separately credited to Shanmu Jin, version 2, Theorem 1 and Lemma 4. The live primary page confirmed the version and scalar statement. A direct HTTP download returned 403, so the full retained primary excerpt at the research pin was used to inspect the interpolation lemma and its proof. The manuscript includes the radial-dilation argument needed to pass the assumed polynomial bound to bounded analytic interpolants on the disk.

The closest comparison was updated from Åhag–Czyż–Virtanen v3 to v4, dated 21 September 2026. Its primary HTML, title, authors, Theorem 1.6, introductory dimension-four reduction, and Section 12 through its equality corollaries were inspected. It still treats complete equality through dimension three, while scalar polynomial equality is all-dimensional. The v4 title and renumbered Section 12 are used in the paper. No literature-wide priority certification is made.

The result concerns attained finite matrix-polynomial witnesses with base dimension at most four. It does not claim a uniform gap over varying polynomials, a nonattained complete-supremum result, a quantitative stability exponent, or higher-dimensional scalarization. The weighted-shift example prevents the unrelated false output-block classification.

Validation: `validate.py` checks the exact complex base-first pairing, block trace identity, weighted-shift example, and finite inertia cases. These identities supplement the written proof. All eight pages were visually inspected at 105 dpi; the standalone ZIP rebuilds without LaTeX warnings and has identical extracted PDF text. The requested unslop edit and established disclosure wording were applied.

Disposition: suitable for release as an explicitly conditional author preprint. No independent human or formal verification is claimed.
