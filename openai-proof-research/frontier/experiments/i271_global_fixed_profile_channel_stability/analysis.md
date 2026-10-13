# I271 analytic checks

The complete unreviewed proposed proof is in frontier/iterations/i271-global-fixed-profile-channel-stability.md. This is one further scope in the existing spectral chain, not an accepted finding.

The new exponent comparison uses q=s-1/2 and the exact profile integral. Cancellation of the Gamma factors gives B_s/a^(2s)=(r+1)^(q+1)q^q/[r(q+1)^(q+1)]. Its logarithm has a minimum zero at q=1/r, first derivative log((r+1)q/(q+1)) and second derivative 1/[q(q+1)]. These exact derivatives, not a numerical approximation, justify the quadratic Taylor upper bound on the lower-exponent interval.

Writing the dimensionless lowest-energy displacement as d, choose gamma-s=d/(2r). The exponent remains in the admissible interval even at d=1. For 0<d<1, log(1-d)<=-d and the Taylor bound give a negative exponent -k0 d². The case d=1 is handled separately by the absence of negative spectrum, avoiding log(0); d=0 uses D>=0. Finite spectral lists or monotone exhaustion give the same sum inequality. No eigenvalue-count factor enters.

The global gap/projection comparison is rederived in the candidate rather than relying on the verdict of I266. The upper test gives delta<=J; the lower comparison is valid even if the intermediate bound |b|²>=1-R_u/a² has a negative right side. J<=Z=z0 a² makes its denominator uniform in every finite dimension. Scaling is consistent: A_global has units a^(2gamma-4), and A_global J² has units a^(2gamma).

The final linear estimate uses the exact independently validated I264 local lemma with its original tau, plus the new global quadratic bound outside that radius. This is a case split, not a claim of a sharper local asymptotic or a new value of tau. Its constants remain dependent on the fixed exponent and scale. Neither an infinite-dimensional equality theorem nor compactness uniform in channel dimension is invoked.
