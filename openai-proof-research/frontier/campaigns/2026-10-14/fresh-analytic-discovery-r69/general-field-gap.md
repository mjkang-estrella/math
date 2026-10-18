# Why this does not close the general Lipschitz target

The affine proof uses a single coordinate change, independent of the endpoint scale, which simultaneously conjugates every frozen map. For arbitrary u the corresponding composition law is not an affine translation/dilation action. Applying pointwise affine approximations does not preserve the Plancherel argument.

A quantitative limitation: if u and an approximating field u_0 differ by at most ω on a relevant spatial box, then the frozen displacements differ by at most |t|ω. For vertical-frequency-supported f with |η|≤R, the fundamental theorem of calculus along an interpolated bi-Lipschitz map bounds the L² difference by C|t|ω R||f||₂ (under the same small Lipschitz-time condition). On a δ-size box, a merely Lipschitz field admits only ω=O(δ) from a constant or arbitrary affine approximation with controlled slope. The scale cost is therefore O(Rδ²). At the parabolic frequency R≈δ^(−2), it is order one, not a summable small error. This is a limitation of this perturbative estimate, not a counterexample to the full theorem or to SSα. The r65 explicit curved-field example already shows that treating all curvature as O(a) in L² is false.

Differentiability almost everywhere gives an o(δ) remainder at most points but supplies no uniform rate over all admissible Lipschitz fields or scales. A uniform all-width square/Carleson estimate for the bad approximation scales would be a new unpaid step. One cannot sum their order-one errors by counting boxes or invoke dominated convergence without an integrable uniform majorant.

Thus SSα for arbitrary Lipschitz fields remains unpaid. The long selected diagonal estimate

    ||sup_k |Σ_w P_w H_a^(δ_k)P_w f|||₂≤C||f||₂

also remains unpaid, independent of the affine short-cutoff success. The global B1 packet-error sum and B2 summable-disparity bound remain unproved. The frozen full target has not been narrowed to affine fields, and no source-family switch or new candidate freeze is made in this checkpoint.
