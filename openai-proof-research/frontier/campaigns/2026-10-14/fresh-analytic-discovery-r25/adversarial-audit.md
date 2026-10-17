# W5 author adversarial audit

These are mathematical diagnostics by the author, not independent gates. No numerical evidence is used as proof.

1. **A divergent normalization product.** Replacing each regularized logarithm by log|1−aP_j|² loses a factor 1+ε² at every scale. That route gives (1+ε²)^N and fails. Candidate §3 instead uses the minimizing coefficient c₀=a/(1+ε²); its loss is exactly 1+κ|c−c₀|². The accumulated cost is bounded by exp(κρ²/3), independent of z and the number of factors.

2. **A zero caused by a convergent product rather than a factor.** Pointwise convergence alone would not suffice. Here Σ|c_j P_j(z)|<∞ and the logarithmic tail is absolutely convergent; hence all zeros come from individual factors. This exact implication is proved in §3 and is necessary in §4.

3. **The algebraic relation might vanish identically after substitution.** Each rational substitution t↦1/(c₀+η_jt) is nonconstant and has no pole on D_ρ. Their product maps onto an open subset of C³; nonzero R_J cannot vanish there. Repeated indices do not destroy this argument because the three parameters remain independent. For example identical polynomials have relation X₁−X₂, but independent rational targets do not satisfy it identically.

4. **Uncountably many points cannot be avoided by a countable argument.** The proof does not enumerate points. Every common zero selects a triple of factor indices. Those triples are countable, and a single algebraic relation for each triple covers all its possible zero points at once. Baire category is applied only to this countable union of proper analytic zero sets.

5. **Fractional powers at zeros.** The source permits every sufficiently large finite amplitude, including integers. L is fixed as an integer before the metric parameter. The functions are q_l^L, never a holomorphic branch of q_l^α for nonintegral α. No branch issue is suppressed.

6. **Injection is weaker than an embedding on a noncompact domain.** The inverse is written explicitly on three relatively open image patches by division by a nonzero f_l. This proves continuity on the whole image. Properness is neither used nor asserted. Likewise the derivative check uses the first two base coordinates and all three fiber coefficients, not a single scalar Jacobian.

7. **Conflict with the source obstruction.** A given f_l need not be everywhere nonzero; in fact an everywhere nonzero f_l with (5.1) would itself contradict the source minorant property. The three zero divisors have empty common intersection. Cartan B could find holomorphic coefficients expressing 1 as a combination of the f_l, but it gives no bounded coefficient norms. Using such coefficients to build one bounded fiber coordinate would be unjustified. The candidate never does so.

8. **Metric/parameter feedback.** The polynomials, regularization and integer L define φ and M. The source chooses the metric parameter after their finite jet constants. Choosing the t_l constructs functions on M without altering φ or the metric, so all geometric quantifiers still concern the SAME M. There is no limit of metrics or degeneration of pinching constants.

9. **Too-strong finite-dimensional projection claim.** No global bounded generic projection theorem is assumed. The proof uses explicit scalar infinite products and their exact global estimate. Classical finite generation and algebraic avoidance are acknowledged rather than presented as new. The quantitative weighted estimate is the only proposed added analytic operation; whether it crosses the substantial-contribution threshold remains an independent question.

10. **The scope was allegedly frozen before any idea existed.** It was not. mechanism-checkpoint.md contains the actual feasibility argument, pre-freeze-comparison.md records the literature comparison, and freeze-receipt.json binds both before the full candidate was written. This is mechanism-before-freeze chronology, not retroactive freezing.
