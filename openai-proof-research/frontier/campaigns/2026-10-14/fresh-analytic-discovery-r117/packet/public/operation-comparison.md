# Additional operation comparisons

## 214: bond consequences and a still-incomplete site transfer

The source's `thm:main` already gives p_c<p_(2->2) for every infinite connected locally finite quasi-transitive graph with positive vertex isoperimetric constant. The fresh corridor proof is the unimodular part after its reduction; the full theorem also covers the nonunimodular case. Source `consequences.tex` supplies further consequences; none is new here. The actual primary [Hutchcroft, 1904.05804v2](https://arxiv.org/pdf/1904.05804v2), Theorem2.2, Proposition2.4 and Lemma2.5 with their proofs, gives the compatible implication from a bounded connection operator to exponential extrinsic two-point decay. Splitting a simple path at a distance sphere and applying BK gives C_(n+m)<=C_m S_n. Averaging spheres bounds blocks by ||T||/(m+1), and iteration gives exponential decay. The source's stronger L2 premise feeds directly into this proof. No new decay or ballisticity claim follows from changing the wording.

A different prospective interface is Bernoulli site variables. The source's actual bond operation is more than a generic sprinkling argument. `def:templates` fixes full-graph random-walk weights before choosing an induced domain. Its internal path edges are open and all nonpath incident edges are closed. `def:calibration` deletes only the internal vertices I_w, so those specified edge bits are independent of all remaining exterior edges; c(w)P(Q_w)=mu_u(w) exactly. `def:deletion` charges any whole weighted loss to a visit to N[A], including pendant-branch removal. `def:correlation` exposes a full cluster and retains an independent Bernoulli exterior. `def:legs` then splits the total penalty into two exterior legs plus one e^(Ck) allowance.

For a site version, all neighbors of an internal vertex outside the retained path must be closed to isolate that vertex. A chord in the retained path cannot be removed by closing an extra edge while retaining all path vertices. Choosing an induced path is therefore a natural first repair. The exterior now loses a neighborhood of the interior, and its endpoints must be handled consistently with their open/conditioned status. One cannot copy the old D_w=V minus I_w formula verbatim. The BK splitting at a shared vertex also needs the appropriate endpoint normalization; it is not literally disjoint occurrence on vertex bits.

The strongest inspected source operation makes this prospect less hopeless than a generic objection suggests. `path:selection` constructs two escapes by a labeled geodesic/middle-walk experiment, rooted reversal and domination. Its collision probabilities sum geometric series uniformly in the escape length. Requiring avoidance of a fixed-radius neighborhood should change degree-dependent constants in those sums. `path:smoothing` already tests the potential on N[I_w]; another fixed-radius enlargement is bounded by a constant times k and can still be tested before conditioning on avoidance. These are feasibility observations, not a completed site lemma: induced-path selection, endpoint escape avoidance and the site exterior law must hold simultaneously for the same weighted templates.

The missing certificate is the complete site analogue of domain monotonicity, calibration, exposed-cluster correlation, two-leg penalty decomposition, and two-endpoint escape, with one choice of normalized kernel and domain convention. The round did not establish it, and did not freeze the headline site conclusion while those interfaces remained open. This is not a proof that a site theorem fails, or that the compatible transfer could not be routine once written.

## 346: the actual endpoint and the strongest inspected stratification reduction

Source `thm:main` bounds the singular-set Hausdorff dimension by m−1 for every Euclidean stationary integral m-varifold, without stability or a density upper bound. Its `prop:density-comparison` retains density-Q centers through a height-square normalization under a Frostman exponent s>m−1. In `06b-density-centers.tex`, the inverse reference-volume density cancels the reference error exactly. The remaining radial inequality is

    dot I_i(X0,t) >= −C epsilon_i t^(1−m)
                         integral_(B_Ct(X0)) (e_i+a_i^2) dmu_i.

Averaging over s-dimensional center measures and then integrating scales uses integral_0^l t^(s−m) dt. At s=m−1 this particular estimate is logarithmically divergent. This does not invalidate any stipulated source statement; that source assumes the strict inequality. It also does not prove an endpoint conclusion false.

The primary [Naber–Valtorta, 1505.03428v4](https://arxiv.org/pdf/1505.03428v4), Theorem1.5, gives rectifiability of the classical symmetry strata. Theorem6.1 and the inspected final proof bound the measure's covariance eigenvalue using tilt and density drop, with a quantitative failure of (k+1)-symmetry supplying the coercive lower bound. For k=m−1 that hypothesis excludes planar tangents. A singular point with a multiplicity-Q planar tangent need not satisfy it. Thus this strongest inspected reduction controls the nonplanar stratum, not the full singular set. I27 already identifies exactly that residual and endpoint problem. No new full rectifiability claim is made.

The abstract source `prop:measure-reduction` itself already supplies the full dimension contradiction for positive height/stress measures, using its PSD block, differential identities and center inequality. Merely reapplying it under another name is not a new mechanism. A summable endpoint comparison or a different structural description of the planar-tangent singular set remains absent here.

## 356: continuous majorants already pay the rough-coefficient variant inspected

The companion `weight:every-geodesic` assumes bounded globally Lipschitz F and bounded continuous G, on every full-support finite-dimensional unreduced RCD(K,N) space, and concludes the distributional Hessian bound along every minimizing geodesic. Its weighted curvature proof works in a common generator graph domain; it does not demand the unprovided second-order regularity of arbitrary Lipschitz F. The final localization fixes a strict geodesic subsegment, concentrates endpoint measures and uses nonbranching uniqueness before the large-parameter entropy limit. These operations are already stipulated, including every-geodesic quantifiers.

For a bounded upper-semicontinuous G, set

    G_j(x)=sup_y {G(y)−j d(x,y)}.

These are bounded j-Lipschitz majorants, decrease pointwise to G, and stay between inf G and sup G. The weak inequality with G implies the one with every G_j. Apply the actual source to each G_j and then bounded convergence on the same prescribed geodesic. This pays the entire bounded USC extension; analytic r112 already records this exact construction. No density-dependent rate or weak/subsequence replacement is required.

Changing a merely Borel coefficient on an ambient null set can change its values along a particular geodesic while leaving the weak ambient hypothesis unchanged. That observes a representative issue, not a refutation of every possible Borel formulation. This round supplies no canonical representative/trace operation or complete new all-geodesic theorem. The related Gigli characterization introduction retains exact Hausdorff reference measure, full test classes and noncollapsed RCD structure; it is not an arbitrary equivalent-weight theorem.
