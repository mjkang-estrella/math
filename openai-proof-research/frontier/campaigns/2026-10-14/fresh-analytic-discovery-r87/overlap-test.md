# What the new cluster bound does not permit

These are supporting diagnostics, not counterexamples to the full critical maximal target.

## A. Absolute cluster summation fails even for arbitrarily separated atoms

Fix a smooth nonnegative bump a supported in a sufficiently small ball inside a unit cube, with integral1. Its Fourier transform has modulus at least1/2 on the unit sphere. Choose N centers z_i separated by at least D, all contained in a ball of diameter L_tot (for example a line of N centers has L_tot<=2ND). Let

 F_i(r,z)=chi(r/R) exp(-ir) a(z-z_i),

with the same cutoff chi and annular P as in localized-vector-restriction.md. Each input atom has uniformly bounded Lq_z H norm. Choose R arbitrarily large compared with L_tot²; also require R>lambda^c for any prescribed c. On the common interior shell11R/8<|x|<13R/8 the exact far-field calculation gives

 V_i(x)=exp(-i|x|) exp(i omega.z_i) ahat(-omega) + O(L_tot²/R).

Thus |V_i(x)|>=1/4 after enlarging R, simultaneously for every i and omega. The sum of absolute cluster outputs is at least N/4 on a set of measure comparable to R³, while

 sum_i R³ ||F_i||_{Lq(H)}^q <=C N R³.

At level lambda=N/8, the claimed restricted-weak q bound for this positive majorant would give measure at most C N^(1-q)R³. This fails for every q>1 as N→infinity. The LRS good-cube condition N<=lambda^q is satisfied for all sufficiently large N. D may itself be an arbitrarily large power of lambda; choosing R still larger preserves the example. Therefore spatial separation and the occupancy bound alone cannot justify taking absolute values of the individual outputs.

The actual deterministic sum retains exp(i omega.z_i), which can cancel. The example does not disprove its desired bound. A tube-incidence approach must preserve this angular oscillation or an equivalent cancellation estimate; a positive overlap count of these whole spherical waves cannot suffice.

## B. Lr diagonals plus small signed L2 cross terms do not form a summation principle

Let1<r<2. Take a set E of measure1 and N disjoint sets F_l each of measure epsilon/N. Define functions v_i to equal1 on E, and on F_l set

 v_i=N/sqrt(epsilon) (1_{i=l}-1/N).

Then integral v_i conjugate(v_j)=N delta_(i,j): all distinct cross inner products vanish exactly. Also sum_i v_i=N1_E. For each i,

 ||v_i||_r^r=1+N^(r-1) epsilon^(1-r/2) [(1-1/N)^r+(N-1)N^(-r)].

Choose epsilon sufficiently small relative to N. Then each Lr norm is bounded by2, whereas ||sum_i v_i||_r=N. Thus even exact L2 orthogonality plus uniformly bounded Lr diagonals does not imply an ellr summation bound. The missing information is in the large L2 mass on the small compensating sets.

This explains why one cannot combine(CL) with the old LRS cross-inner-product estimate and simply discard the old L2 diagonal term. Cutting off each v_i at a level also changes the cross inner products; their original cancellation may have occurred on the removed sets. Additional structural information about the actual oscillatory kernels is needed.

## C. Exact remaining operation after the cluster improvement

Let q be fixed in[4/3,3/2), and choose q<r0<3/2. A good radius-R cube has at most lambda^q input centers. Partition its centers into D-connected components (join pairs at distance<=D). Each component has diameter at most C lambda^q D. If D=lambda^a and R>=C lambda^(4(q+a)), the cluster lemma at exponent r0 has loss at most lambda^((q+a)epsilon). This is an arbitrarily small power of the level lambda, independent of how large R is. Therefore the former single-cluster R^epsilon obstacle is actually removed.

What remains is a cancellation-preserving assembly of all these components and all long radii. Direct triangle summation incurs the component-count factor K^(1-1/r0); taking absolute outputs fails by A. Retaining only signed L2 pairwise inner products while using Lr0 diagonals is invalid by B. A sufficient new estimate would control the good long-radius sum at level lambda by

 measure{|sum_(j>c log2 lambda) sum_(z in E_j^lambda) V_(j,z)|>lambda}
 <= C_q lambda^(-q) sum_j 2^(3j)#E_j,

with the actual t-dependent profiles and all dyadic scales, and with no hidden R-dependent loss. The current supporting lemmas do not establish this. No subcritical, single-cluster, or convergence-only assertion is nominated in its place.
