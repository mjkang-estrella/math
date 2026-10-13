# I340 parent supporting lemmas: continuous limit and uniform transfer

2026-10-13. Technical deductions only, not a proposed substantial finding. They do not supply microscopic path tightness. All source statements below refer to Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Continuous Gaussian coordinate version

For a fixed real phi in C_c^infinity(R^6), the source Section 02 gives its Gaussian field on weighted test spaces E_a, the uniform second-moment operator bound, the collision covariance bound, and the weak identity

    zeta_t(phi)=zeta_0(phi)+integral_0^t zeta_s(A_s phi) ds+W_t(phi).

Choose fixed 0<a<b<beta. The source's operator estimates show sup_s ||A_s phi||_a<infinity: transport is bounded because phi is compactly supported, and the collision part has at most linear velocity growth with compact spatial support. Hence sup_s E|zeta_s(A_s phi)|²<infinity. By Tonelli, the drift integrand is in L²(0,T) almost surely, and its indefinite integral has a continuous version and samplewise one-half Hölder bound with random finite constant.

The centered Gaussian noise has independent increments and

    E|W_t(phi)-W_s(phi)|²=integral_s^t C_r(phi,phi) dr <= C|t-s|.

Gaussian moments give E|W_t-W_s|^(2p)<=C_p|t-s|^p for each integer p. Kolmogorov's theorem yields a version Hölder of every exponent less than one half. Combine it with the drift and initial Gaussian variable, and use the source weak identity at all rational times to obtain a continuous version of this coordinate process with the same finite-dimensional laws. A finite list of coordinates is handled on the common probability-one event. This does not assert a samplewise Banach-dual-valued field.

## Uniform exact-centering transfer

Let X^eps and Xtr^eps be vectors of the original and pasted empirical coordinate sums, each centered by its own exact expectation and divided by sqrt(mu), using the source's common-initial-law coupling. Let Eeps be the event of any discrepancy in [0,T]. The source supplies P(Eeps)<=C eps^(1+eta), preservation of N, and uniformly bounded moments E(N/mu)^p for every fixed p. For one bounded test,

    sup_t |E sum_i phi(z_i(t))-E sum_i phi(ztr_i(t))|/sqrt(mu)
      <=2||phi||infinity sqrt(mu) [E(N/mu)^p]^(1/p) P(Eeps)^(1-1/p)
      <= C_p eps^(-1+(1+eta)(1-1/p)) -> 0

when p>(1+eta)/eta. The supremum is outside the expectation on the left; the inequality follows from the stronger pointwise trajectory bound 2||phi||infinity N 1_Eeps, so its constant is uniform in time. For all t simultaneously the uncentered paths coincide on Eeps complement. Consequently the sup distance between the two centered vector paths tends to zero in probability. The J1 distance is bounded by sup distance using the identity time change. Thus any proved pasted-path limit transfers to the true process by Slutsky. No microscopic tightness or rate for the pasted paths follows from this transfer alone.

## Read scope and boundary

The parent read the complete Section 08 source (3357 bytes, SHA256 3efa338da518fd1141222a800e9ef45b3a3b998145d3aa39e725abe35b240136) and Section 02 lines 270–510, including the full backward-propagator statement, covariance formula, field bound and weak-equation derivation. Section 02's complete byte hash is 51fad6beefe3041c56ea2686776dbfdedf8522120762f4aaef019947fe902396 (23065 bytes); the rest was not semantically read in this check. Source truth is stipulated. Kolmogorov, Tonelli and the elementary coupling argument are standard credited operations. The unproved I340 target is precisely tightness of the microscopic paths, which these lemmas do not replace.
