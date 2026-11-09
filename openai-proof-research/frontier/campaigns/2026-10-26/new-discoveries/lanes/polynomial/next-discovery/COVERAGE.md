# Formal coverage of the k=48 source sign certificate

Frozen supporting modules, pinned Lean4.34.1. Fresh verifier receipt: `build/verified/audit.json`, PASS44 declarations, warnings treated as errors, only `propext`, `Classical.choice`, and `Quot.sound`.

| Source or proof step | Formal declaration |
|---|---|
| Lemma3.5 initial C(k,0,0)=1/(k−1)! | `sourceC_initial` |
| Zero initial row and zero initial column | `sourceC_zero_row`, `sourceC_zero_column` |
| Full recurrence for every positive j, including indices beyond row length | `coeffRow_recurrence`, `sourceC_recurrence` |
| Literal Corollary3.7 rational and polynomial definitions | `rhoEval`, `sigmaEval`, `rho`, `sigma`, `sourceP` |
| Evaluation and rational-to-real polynomial-map bridge | `rho_eval`, `sigma_eval`, `sourceP_eval` |
| Exact rational constant bracket | `alphaLower_check`, `alphaUpper_check` |
| Exact rational five-point coefficient and endpoint sign checks | `rhoCheck_ok`, `signCheck_ok` |
| Existence and uniqueness of actual source φ48 | `phi_exists`, `phi_unique`, `sourcePhi48_spec` |
| Identification of actual source ψ48 | `sourcePsi48_spec`, `sourcePsi48_unique` |
| Actual α48=φ48^47, positivity and defining equation | `sourceAlpha48`, `sourceAlpha48_pos`, `sourceAlpha48_equation` |
| Derivation of exact bracket, with no bracket hypothesis in source endpoint | `alpha_interval`, `sourceAlpha48_interval` |
| Transfer of rational signs to real source polynomial | `rational_rho_negative`, `rational_endpoint_signs`, `real_negative_sign`, `real_positive_sign`, `signs_of_interval` |
| Unconditional five signs of actual source p48 | `sourceP_signs` |

The parent supplies the generic IVT/four-distinct-root/counting wrapper in a separate module. This supporting packet alone does not label a formal root-count theorem as already complete. It contains no analytic assumption concerning the source constant, no hypothesis that missing bridges hold, and no external numerical oracle. Every rational sign calculation is performed by Lean's ordinary kernel (`decide +kernel`).

The degree2303 of p48 is stated by the source but not separately formalized here. It is unnecessary for the contradiction: the formal polynomial is the exact defining expression, its first strict sign proves it is nonzero, and four distinct roots already contradict the proposed multiplicity bound2. Neither k-minimality nor an upper bound on the number of roots is claimed.
