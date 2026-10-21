# Prefreeze: strict subclusters are clean, the full screening cluster is resonant

This calculation uses the ACTUAL rank-one integrand in AF (3.6)–(3.8), pp.9–10, after the twisted Fock charge nu=m-kappa n has been inserted. It supplements the screening-complex comparison; it is not an assertion that the general geometric comparison is false.

## Homogeneous radial calculation

Take m,n>=0, kappa irrational, ell=m+1. Up to the normal-ordered operator factor, the screening differential is the multivalued top form

    I(z) = product_i z_i^(-nu/kappa)
           product_(i<j) (z_i-z_j)^(2/kappa)
           dz_1 ... dz_ell,

on configurations of ell nonzero pairwise distinct complex points. AF integrates it against a twisted cycle. The normal-ordered factor is retained in the actual screening operator; this calculation concerns its displayed local-system factor and top-form Jacobian.

Let k of these points approach the origin with all ratios distinct/nonzero and the other points fixed away from the origin. On a radial blowup chart write z_i=rho u_i for those k points, with one u_i fixed to 1. Then the radial power, including the Jacobian, is

    E_k = k-1 - k nu/kappa + k(k-1)/kappa
        = k(n+1)-1 + k(k-1-m)/kappa.

For 1<=k<ell, the numerator k(k-1-m) is a nonzero integer. Thus E_k is nonintegral for every irrational kappa: if an integer plus this number divided by kappa were an integer, kappa would be rational. This includes non-real kappa. The corresponding rank-one local system has nontrivial radial monodromy. On a transverse smooth punctured disk its local cohomology invariants and coinvariants vanish, so its ! and * extensions agree. This is ordinary Kummer cleanness, and is already part of the source/classical toolkit.

For the full cluster k=ell=m+1, the nonintegral term cancels EXACTLY:

    E_ell = (m+1)(n+1)-1.

The radial monodromy is one. Equivalently the full top form scales by rho^N with N=(m+1)(n+1). This N is exactly the integer gap between the incoming and outgoing Virasoro weights in the other calculation.

For the dual screening there are ell_dual=n+1 variables, inverse level 1/kappa, and charge n-m/kappa. The same calculation gives E_full_dual=N-1 and nonintegrality for every proper cluster meeting the origin. Thus the two constructions have identical full-cluster exponent, not just identical W highest weights.

Clusters of k>=2 screening points away from the origin, in a chart retaining the common center and scaling k-1 relative coordinates, have radial exponent

    k-2 + k(k-1)/kappa.

This is again nonintegral for irrational kappa. These statements concern generic transverse radial divisors. No assertion is made that this short calculation by itself constructs all iterated blowups or settles simultaneous nested collisions. The original m=0 or n=0 cases remain included; the corresponding one-variable full cluster has no proper nonempty subcluster.

## What can and cannot be inferred from the radial calculation

It is incorrect to say that irrationality makes EVERY screening collision clean. The full origin cluster is forced to be resonant by the weight labels permitting the screening map. It is equally incorrect to claim that this resonance obstructs duality: the primary screening resolutions and the source principal-reduction family theorem already exist and pay those operations in their stated categories.

Locally, a rank-one radial connection with exponent N-1 is gauge-equivalent on the punctured disk to the trivial connection. Its extension from the punctured disk is not determined merely by that restriction: j_! and j_* differ by the invariant/coinvariant boundary contribution, computed by the nonzero cohomology of the circle (or algebraic de Rham G_m). Matching N therefore does not alone identify a boundary extension morphism. One must match the chosen cycles, residues, extension maps and enhanced action. Proper-cluster cleanness is insufficient.

The strongest integrated pointwise comparison has been carried through: common incoming Fock module, common simple screening kernel, isomorphic outgoing W quotients, identical characters and full radial exponent. After all of this the unexplained operation is a coherent comparison in the enhanced Jacquet/factorization-module category, including the chosen total-cluster boundary maps and residual Levi action. Gaitsgory–Lysenko's semi-infinite-IC construction is an actual possible mechanism and is explicitly taken into account; the calculation here does not supersede it or prove its failure. Its identification with the particular reciprocal-irrational source functor has not been obtained in this work.
