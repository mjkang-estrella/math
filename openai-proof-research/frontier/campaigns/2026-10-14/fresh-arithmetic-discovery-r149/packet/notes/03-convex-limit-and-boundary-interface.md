# Prefreeze: convex trace completion and the unresolved effective interface

This is sustained feasibility work, not a frozen theorem or author-proof nominee. Source050 and all its operative proofs are stipulated true. Primary proof reads and original-history reads preceded this note. The supplied earlier full scopes and dispositions are unchanged.

## 1. Exact convex class

A squared complex seminorm Q on a finite-dimensional complex vector space means Q=p², where p is finite, nonnegative, absolutely complex homogeneous and subadditive. Equivalently, Q is nonnegative, real convex and Q(lambda v)=|lambda|²Q(v). Degeneracy is allowed, but the total function must not vanish identically when used as an obstruction. No claim is made for a general strongly pseudoconvex Finsler function: it need not be real convex.

For squared seminorms Q_i, their positive weighted sum is again a squared seminorm: its square root is the ell2 norm of the vector (sqrt(weight_i) p_i), and Minkowski gives the triangle inequality. Pointwise finite limits preserve convexity and degree-two homogeneity. If Q(v)≤C||v||², then

    |sqrt(Q(v))−sqrt(Q(w))|≤sqrt(C)||v−w||,
    |Q(v)−Q(w)|≤C(||v||+||w||)||v−w||.          (5)

These inequalities replace the source's finite matrix coefficient bounds. They use no base derivatives or uniform strict convexity.

## 2. The entire trace construction retains this class

Suppose, for an unbounded sequence m, the dual f_m*F⊗P^−1 carries a continuous positive squared complex norm Q_m that is psh on its total space. Define q_{m,t} by the source trace formula, replacing the squared Hermitian norm by Q_m. The mth root ambiguity has modulus1, so complex homogeneity makes the summands well defined. Averaging preserves squared-norm structure by the preceding ell2 argument. Holomorphic inverse branches preserve psh. Counting multiplicities makes the trace continuous across the coordinate branch locus; local boundedness and removal across the pluripolar branch set then give psh everywhere. This is the SAME branch operation, including crossings, used by the source.

The frame law remains

    q_{m,gt}=|g|^(2/m)q_{m,t}.

Using fixed background metrics, normalize the globally continuous homogeneous function N_m=q_{m,t}|t|_0^(−2/m) to have maximum1 on the compact unit sphere bundle of F. Thus

    0≤q_{m,t}(x,v)≤|t(x)|_0^(2/m)|v|_0².       (6)

Together (5) and(6) supply uniform fiber Lipschitz bounds on compact coordinate balls. Neither derivatives of Q_m nor a uniform lower norm bound is imposed.

## 3. Full distributional extraction, not an a.e. restriction to D

Fix a chart and a countable dense subset of C^r closed under rational real convex combinations and rational complex multiplication. For each such fiber vector c, the functions q_{m,t}(x,c) are bounded in local L². Extract a simultaneous weak subsequence over all these c and a countable chart exhaustion. Positivity, convexity, degree-two homogeneity on rational data, and the bounds(5)–(6) pass to the weak limits: pair the corresponding linear inequalities with arbitrary nonnegative test functions. A countable intersection gives one full-measure set where all inequalities hold. Extend from the dense vectors by(5). This gives a measurable function Q_U(x,v), continuous in v on that full-measure set, with squared-seminorm fibers and the same local upper bound. Assign arbitrary values on the base-null set for now.

Convergence also holds as distributions on the full total-space chart. To verify it, approximate a compactly supported smooth test Phi(x,v) by a finite partition in v with sample vectors in the dense set. The error against each q_m and against Q_U is bounded by the common fiber Lipschitz constant times the mesh, multiplied by a fixed compact volume and a bound on Phi. For the resulting finite sum, weak convergence in x applies. Let the mesh tend to zero. This argument does not identify any value on a specified divisor.

On an overlap with holomorphic frame matrix T(x), the q_m functions are related by pullback along(x,w)↦(x,T(x)w) and the scalar |g|^(2/m). Pullback of test densities through this fixed diffeomorphism preserves distributional convergence. The scalar tends uniformly to1 on compacts. Hence the Q_U obey the untwisted bundle transition almost everywhere on total space. Since their fibers are continuous outside a base-null set, this is also an almost-everywhere base transition for every fiber vector.

## 4. Every-fiber recovery for seminorms

Convolve ONLY in base variables with the same smooth nonnegative radial kernels as the source:

    Q_delta(x,v)=int Q_U(x−y,v) rho_delta(y)dy.

Convolution of q_{m,t} is jointly psh and fiberwise a squared norm. For fixed delta, weak convergence at a finite fiber net gives convergence of convolved values and base derivatives on smaller compact charts; uniform bounds on differentiated kernels and(5) extend this to locally uniform convergence for all v. Thus Q_delta is jointly psh, and every fiber is a squared seminorm. Smoothness in fiber directions is neither asserted nor needed.

For each constant v, radial means of the subharmonic x↦q_{m,t}(x,v) increase with radius. Passing to the convolved limit at two fixed radii shows Q_delta decreases as delta decreases. Therefore

    q_U(x,v)=lim_(delta↓0) Q_delta(x,v)

is finite, nonnegative and psh on the total-space chart. At EVERY x, finite decreasing limits preserve real convexity and complex degree-two homogeneity. Hence every fiber is a squared seminorm. This avoids finite polarization, which cannot recover a nonquadratic norm from finitely many values.

At almost every base point, approximate-identity convergence on the dense fiber set and(5) identify q_U with Q_U for all v. The local q_U therefore agree almost everywhere on overlaps. Locally bounded psh functions agreeing a.e. agree everywhere by their small-ball mean representatives, exactly as in the source. Thus they glue to a single q on F. The values on the graph divisor are values of THIS representative, not claimed limits of the q_m restrictions.

## 5. Noncollapse and the graph obstruction survive completely

Take maximizing unit vectors(x_m,v_m), pass to a convergent subsequence, and express v_m by c_m→c≠0 in one fixed chart. Inequality(5) replaces the source operator-norm estimate and shows q_{m,t}(x_m,c)→1. The fixed-vector psh function u_m(x)=q_{m,t}(x,c) is at least1/2 at x_m for large m. Integrating its submean inequality against the source's fixed cutoff yields a positive lower bound independent of m. Weak convergence at c (or approximation by the dense vectors using(5)) transfers this to Q_U. Thus q is not identically zero.

Pull q back by the two actual line inclusions. Holding a line vector fixed and varying the complementary P1 coordinate gives a finite subharmonic function on a compact curve, hence a constant. The graph relations give a common nonnegative squared seminorm a on O(−24), invariant under the lifts A^⊗24 and B^⊗24.

The nonzero argument still works: if both restrictions vanish, each fiber seminorm off D vanishes on two spanning lines, hence on their span by its triangle inequality. Then q vanishes off D and thus everywhere by the submean inequality. Therefore a is nonzero. On a one-dimensional complex fiber, homogeneity already gives a(z,w)=u(z)|w|², so the source logarithmic-weight proof applies verbatim. Its positive measure has mass48π, including all atoms and zero weights. The explicit certificate in note02 or the source annulus proof excludes that invariant measure.

Thus the traced continuous-convex class above cannot occur for infinitely many m. This calculation closes the nonquadratic finite-dimensional compactness interface; it does not claim compactness for arbitrary singular metrics or arbitrary Finsler dual functions.

## 6. Strongest primary polar composition and its payment

Liu–Wan Proposition3.5 actually constructs, from a smooth strongly pseudoconvex metric G on the ORIGINAL E with semipositive Kobayashi curvature,

    Q(x,xi)=max_(v≠0) |xi(v)|²/G(x,v).

Their complete read proof shows that Q is continuous, fiberwise the square of a complex norm, and psh even at zero. Its osculating holomorphic section argument treats semipositive curvature by a local exp(−epsilon|z|²) perturbation. The argument does not infer that the original G is convex. The strong real-convexity estimate is also proved there, but is unnecessary for Sections2–5. We do not use their separate globally smooth replacement, whose homogeneous-regularization antecedent was not independently read.

Consequently the exact polar can be fed into the completed trace calculation for E_m. It gives an eventual exclusion of this smooth semipositive original-bundle Finsler class for the SAME fixed power family. This includes smooth Hermitian semipositivity only through that explicit interface. It gives no statement about every small m and no threshold. No Nakano/dual-Nakano, arbitrary symmetric/tensor/pullback, or singular original-metric extension is inferred.

This is a compatible application of the source's entire trace/graph proof, the primary's already-proved polar, and elementary compactness of finite-dimensional seminorms. It is retained as prefreeze payment, not offered as a renamed substantial nominee or as a retry of an older full positivity target. Parent alone assesses contributions. The broader existence of stable ample Finsler counterexamples on P1×P1 is already in Liu–Wan Theorem1.1; its actual Sections3–4 mechanisms were read before this derivation.

## 7. Concrete obstruction to a naive smooth split test

In the dual of the source local basis e=(1,h),f=(0,d), the inclusions are columns

    v1=(1,0), v2=(h,d), I=((1,h),(0,d)).

For d≠0,

    I^−1=((1,−h/d),(0,1/d)).

A Hermitian H is detected by its values on these two vectors only with constants degenerating like |d|^−2. For the explicit semidefinite H=diag(0,1),

    H(v1,v1)+H(v2,v2)=|d|²,   tr H=1.

Positive definite H_eta=diag(eta,1) gives eta(1+|h|²)+|d|², which can also be arbitrarily small. Thus there is no uniform algebraic lower bound of these two line values by a fixed positive multiple of tr H at D. At a node d=uv, the loss is |uv|^−2, with nonintegrable behavior already along each branch.

There is also a numerical hypothesis mismatch with Liu–Wan Theorem3.2. On S, the source dual sublines have classes −24H1 and −24H2. For any smooth strictly positive ddc-closed testing (1,1)-form Theta, their degrees are strictly negative: int(−24H_i) wedge Theta<0, because H_i has a smooth nonzero semipositive ruling representative and its wedge with Theta has positive integral. Thus the required positive degrees of the primary split line factors are not present. The source obstruction is genuinely carried by its graph identifications, not by importing that split-degree test.

This calculation explains why the Du–Xie parallel split projections cannot simply be substituted: the two source sublines coincide on D and cannot be two global complementary parallel projections. It does NOT show that a different smooth separable adjoint test is impossible. A genuine construction could add directions and derivatives with compensated coefficients. None is constructed here.

## 8. The strongest effective interface still unpaid

Note02 pays a fixed positive lower bound c_dyn for dynamical invariance defects. Sections2–6 pay the global trace, all-fiber limit, graph obstruction and compatible primary polar transfer. They still produce a threshold only by contradiction/compactness. No rate is supplied by weak extraction, radial limiting, or a.e.-to-everywhere recovery.

A sufficient additional operation would construct, for every normalized finite-m candidate trace, a positive measure mu_m of a fixed positive mass and establish

    |int h_A d(A_*mu_m−mu_m)|
      +|int h_B d(B_*mu_m−mu_m)| ≤ C m^(−alpha)

with specified C<infinity and alpha>0 depending ONLY on the displayed source data and fixed chosen charts/background norms. Then(3) gives an explicit finite cutoff. No such estimate is established. It is not enough to say that curvature measures converge weakly or that a graph pullback exists for each smooth input.

A second sufficient form would be an actual global smooth separable adjoint test Q with an explicitly proved strictly negative coefficient bound on the relevant finite-power dual bundle, together with controlled construction in m. The first-jet alternative supplies zero-adjoint positive measures at each failed level, not that strict smooth coefficient. The split-primary constructions supply strict tests for different holomorphic structures, not one for this nonsplit graph equalizer.

The smooth-to-divisor trace is a genuine quantitative loss. Even locally, bounded psh functions may have no rate of agreement of restrictions with their canonical limit: on a bidisc,

    u_epsilon(z,w)=max(0, 1+epsilon log|z−w|)

is nonnegative, locally bounded and psh (with value0 on the diagonal). It tends to1 at each off-diagonal point while remaining0 on the diagonal. Its a.e. limit has psh representative1, agreeing with the source's warning about divisor values. This scalar example is NOT a realization of the source matrix trace and does not refute its stipulated limit theorem. It disproves only the shortcut from bounded psh convergence to uniform convergence on a chosen graph. The source's all-fiber representative bypasses the qualitative problem, but does not supply the required rate.

No alternative explicit compatible rate or smooth adjoint certificate has been obtained. This round therefore remains PREFREEZE/no nominee. The retained calculations are not exhaustion, an impossibility result, or an assertion of worldwide novelty.
