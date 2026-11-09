# MathDB 333569: remaining literal-endpoint obligations

Status: unresolved; no `SourceClaim` theorem and no theorem about an actual two-sided law.
All items below are obligations, not assumptions attached to a claimed endpoint.

1. **Two-sided source space and Markov laws.** Define the Borel space `ℤ → Fin 2`, its shift, rank-zero partition, probability laws, stationary one-step Markov class (including boundary/nonergodic laws), and relative weak topology. Extend the proved finite normalized distributions to a unique two-sided measure. Prove both endpoint consistency/translation consistency for all arbitrary finite coordinate sets, the shift-invariance and Markov property, cylinder evaluation, and full topological support. `marginal_pos` supplies positive finite weights, not a full-support measure theorem. Right-extension consistency alone does not construct the law.

2. **Entropy-chain bridge.** For any sorted nonempty subset `s₁<…<sₖ` of an N-block, prove that the `marginal` in Target333569 is the initial stationary distribution times the product of gap transitions. `steps_eq` proves the transition-power identity, but this selected-time marginal identity is still missing. Prove the finite Shannon entropy product/conditional-chain rule and then
   `H(X_S)=H(pi)+∑_{j=2}^k conditionalEntropy(l^(s_j-s_(j-1)),t)`.
   Include singleton and empty cases (only empty entropy is currently proved), and derive the full block entropy `H(pi)+(N-1)H(l,t)`.

3. **Fair-subset averaging and actual limit.** Prove the exact finite count `(N-i)2^{-(i+1)}` of consecutive selected pairs at gap i, nonempty mass `1-2^-N`, and complement symmetry for uniform coefficients. Derive
   `2 Asc_N=2(1-2^-N)H(pi)/N+∑_(1≤i<N)(1-i/N)2^-i H(l^i,t)`.
   Establish convergence, identify the `limUnder` definition with the limit, and prove the source intricacy/entropy-series identity for every parameter in a neighborhood. The proved geometric summability lemma is not this limit theorem.

4. **Actual coefficient and uniform differentiation.** Identify `transverseCoeff r` with half the second t derivative at zero of `conditionalEntropy r t`; no such derivative identification is currently proved. Prove joint continuity and uniform bounds for H and its first two t derivatives on compact parameter rectangles, termwise twice differentiation of the geometric series, and continuity of the summed second derivative. Only the explicit coefficient's r derivatives, monotonicity, and its strictly negative weighted difference series are proved. No theorem currently calls that series the derivative of the intricacy.

5. **Full local promotion.** Use the diagonal maximizer, evenness, and negative continuous transverse second derivative to prove the full two-dimensional local maximum on an actual open rectangle. Neither a local Hessian lemma nor an endpoint under unproved differentiability assumptions has been substituted for this step.

6. **Topology and literal final theorem.** Prove continuity of the chart into weak laws, recovery of transition parameters by positive cylinder ratios, local coverage of all stationary one-step Markov laws (including exclusion of boundary laws from the chosen neighborhood), and equivalence of source finite-cylinder entropy with rank-zero partition entropy. Transfer the parameter maximum to a local maximum relative to *all* stationary one-step Markov laws. The algebraic inverse chart is proved, but these topology and measure identifications are not.

7. **Acceptance artifacts.** After the mathematical endpoint exists: separately review source-statement fidelity/formal endpoint, prepare a complete ordinary proof/paper with exact mapping, and create a full endpoint packet with fresh strict extraction/replay and axiom audits. The present fresh replay covers partial components only. No acceptance count change is authorized or made.

The analytic and measure-theoretic parts are independent large remaining developments; none is a one-line application currently recorded in this lane. The present work makes no claim that a single remaining tactic or import completes the proof.
