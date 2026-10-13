# I281 — adversarial discovery for uniform GAD stability

**U remains unresolved; no counterexample or independent acceptance claim.** Eleven accepted findings and the target of twenty are unchanged. All pinned OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

The [complete analysis](../experiments/i281_gad_uniform_stability_adversarial/analysis.md) independently confirms I279: opposite-phase cats have marginal determinants tending to nu(1-nu), exponentially suppressed output cross blocks of norm sqrt(1-4gamma nu(1-nu))^n, and entropy excess tending to log 2. LP is false; these cats do not refute U.

The completed adversarial fallback is a dimension-independent lower bound. For every pure n-qubit input, let P be its computational-basis probability law and Q the Bernoulli(nu) product law. Retaining *conditional* populations in the actual pinned entropy recursion gives

    S(A^tensor n(P_psi))-n s0
      >=2gamma(1-gamma)nu(1-nu) K_cl(P||Q).

Consequently U holds, with K=2/[gamma(1-gamma)nu(1-nu)], for inputs whose amplitudes are nonnegative after local diagonal phases. This includes positive opposite-phase cats and arbitrarily rare positive correlated cat branches. It avoids summed marginal coercivity and survives I279.

Additional analytic obstructions are proved with explicit scopes:

- For nu=1/2, arbitrary-relative-phase weighted opposite cats satisfy d_n^2<=(8/(1-gamma))D_n for every sufficiently large n, uniformly over all branch weights, including superexponentially rare ones. A Pauli-channel factorization and error-ensemble Gram calculation control the entropy without dimension-dependent continuity; exact output block eigenvalues are recorded.
- Separated sign-latitude codeword superpositions have D_n=H(weights) plus explicit coherence, continuity and decoding errors. Their fixed nontrivial weights retain positive entropy excess. The relative-error conclusion requires the entropy to dominate those errors; extremely rare arbitrary complex weights are not silently covered.
- In the unital small even-cat regime n delta^2->0, the exact input overlap and diagonal relative entropy both have n(n-1)delta^4 scale. The dimension-independent lower bound rules out a diverging distance/excess ratio for this attack.
- A trace-norm Pinsker remainder strengthens the thermal recursion without inversion. It controls noisy conditional output distinguishability, not arbitrary input distance.

**Outstanding:** arbitrary nonlocal phase-only inputs, dense overlapping codebooks, collective phase fluctuations outside the proved small even-cat regime, and hidden-coherence/rare-weight scales outside the stated codebook resolution. The amplitude bound is identically zero for sqrt(Q(x))e^(i f(x)); no truth of U follows from these failed attacks. I273's R0/R1 route and missing uniform nonlinear radius remain unpaid.

The parent-supplied Bae–Gour–Lee–Park–Sanders depolarizing lead was read at §II and §III.1–III.2. Its n-independent quadratic coefficient does not supply an explicit n-uniform Taylor remainder/radius in the inspected proof. Its channel covariance and minimizer manifold also differ from GAD's. The exact quantifier/remainder audit is analysis §8; no GAD consequence is imported.

Primary-source scope and novelty limits are in the [literature note](../sources/i281_gad_uniform_stability_adversarial/literature.md); [reading/failures](../experiments/i281_gad_uniform_stability_adversarial/reading-and-failures.md) distinguishes fully read files and limited excerpts; [authentication](../experiments/i281_gad_uniform_stability_adversarial/input-authentication.json) binds evidence and outputs. No substantiality or worldwide-priority claim, counts edit, live sibling read, subagent, staging, commit, publishing, numerical scan or history replay accompanies this report.
