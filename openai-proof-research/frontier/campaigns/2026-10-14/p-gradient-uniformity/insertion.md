# Suggested replacement for I345 §2.2

For every finite P≥3, there are common constants theta(n,P)>0 and C(n,P)<∞ such that every bounded actual weak p-harmonic function on B_1, with 3≤p≤P, satisfies

`||Du||_(L∞(B_(1/2)))+[Du]_(C^(0,theta)(B_(1/2)))≤C osc_(B_1)u`.

This includes zero gradients. Apply Uhlenbeck, *Regularity for a class of non-linear elliptic systems*, Acta Math. 138 (1977), 219–240, scalar specialization p. 222 and Theorem (5.4), pp. 238–239, with `rho(Q)=Q^s`, `s=(p−2)/2∈[1/2,(P−2)/2]`, C=0. The separate support audit `p-gradient-uniformity/lemma.md` verifies common structural constants, a common Sobolev exponent, the nonlinear comparison estimate and common iteration thresholds in Sections 4–5. It also obtains the uniform gradient maximum by Caccioppoli and Theorem (3.2), so the compact-p interface does not require an additional uniformity assumption on Kotschwar–Ni. For dimension two, extend constantly in a third coordinate and restrict the three-dimensional estimate.

The compact-p input is essential in the bounded-p branch of §4: it gives one Euclidean Taylor modulus `C r^(1+theta)` and hence `lambda_i≤C s_i^theta`, contradicting the chosen bad-scale lower bound once gamma_i<theta. The finite-effective-viscosity limit for bounded p is not covered by the infinity-source or I236 Liouville interface, so this branch is paid by this classical compact-p estimate itself.

For a single fixed p, scaling the same gradient Holder estimate on arbitrarily large balls shows that an entire p-harmonic function with a globally bounded gradient is affine. This uses no finite total energy on R^n.

This insertion cites a supporting classical-uniformity deduction. It is not an additional frontier finding and does not change the p≥3 scope of I345.
