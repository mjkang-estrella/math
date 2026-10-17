# Adversarial audit of O234 (author, not independent)

The complete frozen scope is unchanged. These are proof checks and bounded diagnostics, not an independent PASS or numerical proof.

1. **Deleting all low-rank perturbations is false.** Candidate Section9 computes the actual one-positive-eigenvalue model, with mu=delta0. Its limiting pressure psi(s) is zero up to s=1 and positive above1, with slope1/pi. Thus a rank/N bound on pressure cannot replace Section4. Probability normalization and the quadratic factor1/2 are checked directly by the Hubbard–Stratonovich identity and by maximizing the rank-one quadratic form over signs.

2. **The capped transform at vanishing mass is explicit.** For nu_e=(1-e)delta0+e delta_theta, theta>0 and e>0, solve x=(1-e)/b+e/(b-theta). The admissible root is b=[1+theta x+sqrt((1-theta x)^2+4theta x e)]/(2x), so R=[theta x-1+sqrt((1-theta x)^2+4theta x e)]/(2x). As e decreases to zero this tends to (theta-1/x)_+, including x=1/theta. At x=0, R(0)=e theta tends to0. This agrees with Lemma3 and the exact rank-one stress example; the uniform near-zero bound is essential and is supplied separately by(16).

3. **A maximum of correlated pressures needs an exponential tail.** Fourth moments alone cannot control exp(c epsilon N) directions. Candidate Section2 explicitly invokes Fan–Wu's classical exponential Haar concentration proof, not just the pinned source's fourth-moment estimate. Every net direction has the same mean by a rotation of a scalar spectral block. A union bound and integrated tail require no independence. The two components of O(N) have the same pressure law under eigenvector sign flip. The exponent and finite-N constants in(5),(13) have been traced through this normalization.

4. **The bulk must be flattened.** Replacing arbitrary directions within a nonflat block can alter the rank-one model's eigenvalues. The proof first makes the top k clean eigenvalues exactly b. Its norm cost is b-c_k, and the double limit in(23) pays this cost even for atoms, gaps and point masses. No statement about independent spike and bulk is made.

5. **Fixed epsilon before N.** The source theorem is only used on B_(N,epsilon) for each fixed positive epsilon. Its limiting top atom has positive mass. Lemma2 then permits epsilon to zero; no theorem uniform over vanishing spectral masses is presumed. k=floor(epsilon N) and quantile truncation retain the exact total probability. No continuity of the quantile at the truncation point is required.

6. **Lower outliers and ties.** Lemma1 raises only coordinates below a-delta, an o(N) set. They stay below all unaltered coordinates throughout the path. Convex symmetric derivatives are ordered even at ties; their sum is1/2. The additional delta-norm change is kept and only then sent to zero. The proof neither divides by a vanishing bottom multiplicity nor assumes minimum convergence.

7. **Top-edge case and point masses.** theta=b is proved separately using small operator error after lower clipping. The theta>b proof works unchanged when a=b, since the clean bulk is already scalar and its flattening cost is zero. Its nu_e has both support edges attained with positive mass, so the source applies. Zero spectrum, zero temperature and beta=0 are handled explicitly.

8. **Arbitrary numbers of outliers.** For every fixed epsilon, weak convergence gives o(N) eigenvalues above b+delta for each delta>0. Hence the (k+1)-th eigenvalue's positive excess tends to zero; this is what proves(27). It permits every sublinear count with no specified rate and includes outliers accumulating at the edge. Uniform boundedness, largest-eigenvalue convergence and Haar law are never removed.

9. **Full temperature quantifier.** Pointwise expectation convergence for scaled spectra plus the deterministic K/2 Lipschitz bound gives locally uniform expectation convergence. Exponential concentration on the countable rational temperatures gives one probability-one event; finite rational meshes then cover every beta>=0. Dependence across dimensions is irrelevant to Borel–Cantelli's first implication.

10. **Contribution risk remains distinct from proof.** Nets, concentration, convex ordering, Gaussian recursion and the inverse-transform cap all have antecedents. The proposed additional operation is their scalar-block quenched rank-thickening comparison. Independent review must decide whether this operation is substantial, technical, subsumed, or ineligible. The author's complete deduction is not a self-awarded contribution verdict.
