# Finite-type Ising: preselection calculations, no frozen theorem

This entire investigation remained before scope freeze. It is not a theorem submission, a mathematical gate, or an independent contribution judgment. The formulas below were worked out while deciding whether the direction has an unpaid compatibility operation. No full Ising factor theorem is claimed here. In particular the calculation is not a replacement for the old critical-posterior wave target, a finitary coding result, a Potts factor theorem, or a random-environment construction.

The question considered was the exact factor-of-IID threshold for the free, zero-field binary broadcast on the universal covering tree of an arbitrary finite connected simple graph of minimum degree at least three, with a fixed positive edge parameter theta_e in (0,1), symmetric under edge reversal. The prospective condition is spectral radius at most one for the finite directed nonbacktracking matrix B_ef = 1_(e followed by f) theta_f^2, including equality. The intended equivariance would be for the full group preserving the lifted couplings, not merely a selected path or root; no coding radius or uniformity over all base graphs was proposed. Constants in the calculations depend on the entire fixed base graph and all its parameters. None of these quantifiers was frozen, and no full proof was developed after a purported freeze.

## Strongest source and primary operations

The pinned source236 is much stronger than its headline. Its posterior and innovation sections give component-local versions, exact scalar path responses, the whole countable stochastic equation without an orthogonal martingale remainder, and transport of that equation to the compatible conditional joining given all innovations. Its critical sections give the information scale, attenuation conditional on path spins, marginal-difference representation control, two-sided dependent path averages, high moments, and the integrable Osgood comparison. Recovery supplies the full spin law and equivariance. Those are credited operations throughout.

The actual primary operator proof substantially strengthens the initially considered reduction. Haagerup (1979), Lemmas1.2–1.4 and Theorem3.1, supplies both the polynomial times l2 convolution bound and the exact criterion that a positive-definite coefficient is weakly associated with the regular free-group representation when every exponential damping is square summable. Backhausz–Gerencser–Harangi–Vizer, arXiv:1603.08423v2, §§4.2–4.4, realizes the nonbacktracking operator in a process representation, transfers its norm from the regular representation, and expresses averaged edge correlation as its matrix coefficient. Their final conversion of an average into each individual correlation uses regular-tree symmetry; the averaged identity itself does not need that last conversion. Section4.5 gives the actual tree operator proof, with individually selectable Schur weights. These operations were read before any freeze and are not claimed as new here.

Nam–Sly–Zhang, arXiv:2012.09484v2, Theorem1 and §2.2–part of §2.3, already use the planted Gaussian observation law and innovation SDE, recover spins by large-time signs, and compare different roots. Their theorem is for regular trees in a smaller range; the finite inhomogeneous interaction notation in §2.1 is not by itself a sharp anisotropic factor theorem. No such extrapolation is made. The much stronger stipulated source is the operative construction.

## Perron path law and reversal

Write q_e=theta_e^2 and let r>0 satisfy Br=lambda r. The directed nonbacktracking graph is irreducible for the base graphs under consideration. Reversal is denoted by a bar. A left eigenvector is l_e=q_e r_(bar e), because

    sum_(e preceding f) l_e B_ef
      = q_f sum_(bar e following bar f) q_(bar e) r_(bar e)
      = lambda q_f r_(bar f).

Define

    P_ef = B_ef r_f/(lambda r_e),
    pi_e = q_e r_e r_(bar e) / sum_g q_g r_g r_(bar g).

Then P is stochastic, pi is stationary, pi_e=pi_(bar e), and

    pi_e P_ef = pi_(bar f) P_(bar f,bar e).

Thus the reversed path, with every edge reversed, has the same stationary law. Every row has at least two positive entries. Since the state set is finite,

    a = max_(e,f) P_ef < 1.

For a path e1,...,er,

    product_(i=1)^r q_ei
      = q_e1 lambda^(r-1) (r_e1/r_er)
        product_(i=1)^(r-1) P_(ei,ei+1).

At lambda=1 the ratio to pi_e1 times the Markov path probability is bounded above and below by positive constants independent of the path length. This simultaneously controls forward and backward shell sums. Replacing a shell count by its maximum branching rate would lose this compatibility; the endpoint factors cannot be discarded until bounded using the finite positive Perron vector.

## Information-scale feasibility

For a directed cavity type e let M_e(t) be the second moment of its posterior mean. The scalar binary-signal fusion operation in source236, `lem:binary-fusion`, remains the same with the edge's own theta. Observing only one successor component gives M_e >= q_f M_f. Strong connectivity and positivity therefore compare all finitely many M_e by constants depending only on the fixed data.

Combining two successor signals first and the remaining signals afterwards gives the prospective vector inequality

    M_e <= sum_(f following e) q_f M_f
           - c q_f1 q_f2 M_f1 M_f2 + t+t^2.

Multiplication by l_e and summation cancel the linear terms at lambda=1. The comparison of types then gives the same square-root upper scale as the source. The whole-site mean is bounded by adding its finitely many component information terms. This uses the actual negative fusion term, not merely nonreconstruction or a linear recursion at criticality.

For the lower scale, use Z_n=sum_(depth<=n) theta(path) X_u(t) in a rooted cavity component. Perron shell bounds give E[sigma_root Z_n] comparable to t(n+1). Its Brownian variance is O(t(n+1)). For each ordered pair of depths and each possible last-common-ancestor depth, the weighted spin contribution is O(1): first sum the two descendant squared path weights and then the squared root-to-ancestor weights. Consequently E Z_n^2 <= C[t(n+1)+t^2(n+1)^3]. Choosing n of order t^(-1/2) gives the lower square-root scale. For larger times the root observation suffices.

The side-branch attenuation operation then uses one intact side branch at each path vertex, theta_min>0 and theta_max<1. The finite-type bounds are uniform over which side type occurs. This gives the same e^(-c min(sqrt(t),1) r) candidate attenuation and an expected response row of order t^(-1/2). Source04's finite-boundary Gaussian attenuation, early-time information bound, exact energy identity, martingale test, and component-local version construction then have the same required inputs. This is a compatibility calculation; the entire generalized filtering theorem is not separately asserted in this archive.

## Averaged discrepancy cancellation

Let Gamma be the deck group, a finitely generated free group acting freely and cocompactly on the tree. Choose finitely many vertex and oriented-edge representatives only for this estimate. The eventual factor question was not intended to depend on that choice.

For bounded centered functions of finitely many planted observations, distant translates have covariance bounded by a constant times theta along the connecting path. This follows by conditioning on the two endpoint spins of the separating tree segment: their centered function spaces are one dimensional and the intervening binary transition multiplies the correlation by the product of edge parameters. The independent Gaussian observations do not change this separation. Enlarging the two finite supports costs only a fixed constant. Squaring and summing over a distance shell is bounded when lambda<=1, by the Perron shell calculation. The tree displacement and a free generating-set word length are comparable. Hence every exponentially damped covariance coefficient is square summable on Gamma.

Haagerup's actual Theorem3.1 therefore supplies weak containment of these cyclic representations in the regular representation; density of bounded finite-coordinate functions supplies it for the centered observation representation. This does not assume the observation process is already a factor of IID. It is also stronger than just a bound for one vertex-neighbor averaging operator.

For any invariant joining of two identical observation marginals, the map

    f -> f(X)-f(X')

is a bounded intertwiner and kills constants. Its closed range is a quotient/subrepresentation of the centered marginal representation (via polar decomposition). Therefore the same weak containment holds on the closed marginal-difference space. It need not hold on arbitrary joining observables. This is exactly the distinction already enforced by the source's conditional-copy spectral argument.

Put the finitely many directed types in a pi-weighted direct sum and define the Markov nonbacktracking operator N using P and the deck transformations between chosen lifts. In a matrix entry of N^k, a nonbacktracking path determines its lifted endpoint uniquely, so no two paths with the same starting edge, final type and deck element collide. Its nonnegative coefficients have total at most one and maximum at most a^k. Thus their squared sum is at most a^k. Their free-group word length is O(k+1). Haagerup's Lemma1.4, followed by Cauchy–Schwarz over the possible word lengths, gives

    ||N^k|| <= C(k+1)^(3/2) a^(k/2)

on the regular representation and hence on the marginal-difference representation. Finite matrix size and the pi weights change only C. This is a standard matrix amplification of a reduced group algebra representation, not a new free-group inequality.

For an edge-indexed marginal difference D, set S=sum_e pi_e E D_e^2. Stationarity and the inner-product identity in the primary nonbacktracking argument give summable lag covariances. Therefore

    E_(stationary path,joining) [(D_e1+...+D_er)^2] <= C r S.

The reverse path satisfies the corresponding estimate by the pi reversal identity. No individual-path covariance bound is inferred. In particular a colored tree may have little path-stabilizer symmetry; failure of the original pointwise symmetry shortcut does not create a contribution if the averaged estimate supplies the actual summed SDE terms.

## Compatibility with the dependent path averages

The source07 proof cuts a path after a prefix and controls an average of independent descendant continuation variables, conditional on the prefix spins and observations. In the Perron path law the prefix weights p_y have sum one and maximum at most a^k, whence sum_y p_y^2<=a^k. The same weighted Hoeffding estimate has exponent of order a^(-k) times the square of the continuation threshold. The entering cavity can be removed with a fixed multiplicative cost: theta_max<1 sums its propagated logarithmic effect. Conditional side-branch attenuation bounds the continuation expectations uniformly over the finitely many types.

Choosing a threshold e^(-eta omega r), k proportional to r and eta sufficiently small relative to -log a gives the same double-exponential exceptional bound for r>=C/omega, omega=min(sqrt(t),1). The reversed argument is available under the same stationary law, rather than a separately chosen path distribution. This is why the reversal identity is checked above.

The source's split of a log-product discrepancy into prefix and suffix now calls for the averaged variance just calculated. The intended estimates have the same form

    Q_r <= C exp(-c omega r) r S + C_T r^2 exp(-c a^(-c r)),
    L_r <= C exp(-c omega r) V + C_T exp(-c a^(-c r)),

where V is a positive finite weighted sum of site discrepancy variances. Endpoint Perron factors and finitely many root types are uniformly comparable, so both Q_r and L_r feed the same shell sums in that V inequality. One does not condition the joining on the exceptional event and then claim its original marginal law.

The small-field moment argument also has a compatible finite-type coefficient. In its pure p-th-power term, B_p has entries 1_(e followed by f) theta_f^p and

    B_p <= theta_max^(p-2) B.

At lambda=1 its Perron-weighted sup norm is at most theta_max^(p-2), uniformly bounded away from one for integers p>=3. The source's lower mixed moments and Gaussian moments then have the same proposed exp(Cp^2)t^(p/4) induction budget, with constants depending on the finite data. The critical log-response derivative still vanishes at zero for each edge parameter. Thus the source08 tail interpolation and cutoff r of order omega^(-1)+log I have the same intended integrable coefficient 1+t^(-3/4)+1/[t log^2(1/t)]. All these operations have been compared together: varying the path weights does not demand a separate growing constant at either orientation or at the final shell summation.

## Selection outcome and exact limits

The calculation identifies a compatible existing route rather than an unpaid one. It is not rejected simply because individual steps have familiar names. The same Perron path law simultaneously pays the shell normalization, the variance average, the weighted descendant concentration and reversal needed by the source's conditional-copy comparison. Haagerup's full criterion removes the apparent need for a new representation invariant. This is the strongest reduction tried here, stronger than replacing d by a maximum degree or demanding pointwise path transitivity.

There is no full candidate proof in this packet. In particular the vector high-moment induction, the complete generalized stochastic-integral comparison with every type weight, strict-subcritical case, full automorphism-equivariant recovery, and the supercritical nonfactor converse have not been assembled as a standalone general theorem. They must not be treated as proved by these feasibility notes. For a converse, exponential growth of squared broadcast coefficients against Haagerup's polynomial sphere bound is the natural compatible route, but no complete converse is submitted. For full automorphism equivariance, the source's compact-stabilizer selection would need to be written for the weighted tree; a deck-equivariant surrogate is not offered instead.

No mathematical impossibility, worldwide absence, contribution gate or acceptance follows. The contemplated full threshold question remains unfrozen here. The old finitary and Potts gaps are not closed here. The posterior-wave archive has its own full author proof and a recorded PASS_FULL_PCW / TECHNICAL review; its disposition is not replaced by this round. The actual review opening and §§1–4 through text line180 were read late, after the present feasibility calculation and before sealing; this corrected an initial overbroad description of all three directions as unresolved. No new PCW review or gate is asserted. This round supplies neither a restricted replacement nominee nor an inference that one of those stronger interfaces has closed.
