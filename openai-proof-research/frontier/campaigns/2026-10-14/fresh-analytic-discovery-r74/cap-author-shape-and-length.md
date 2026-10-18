# Local cap approximation, uniform shape, and length bounds

Author assistance only; notation and moment/ergodicity facts are in cap-core.md. Constants may depend on G and M, but not on n, the center of a segment, or its endpoints. All norms below can be taken as l-infinity except for path lengths and coordinate-route lengths, which use l-one. Fixed norm conversion constants are absorbed. No upstream theorem is audited here.

## 1. A bounded local approximation with a useful domination

For integer R>=1, search all open protecting circuits for e of length at most R. Every such circuit lies within distance R of e: its coordinate spans are at most half its length and it encloses the endpoints of e. If the search succeeds use its least length; otherwise use R. Call the resulting integer L_e^R and set

  s_e^R=min(t_e,M((L_e^R)^3+U_e)).

This uses only originals and auxiliaries within distance R+O(1) of e. It is bounded by b_R=M(R³+1). More precisely:

  s_e^R=s_e on {L_e<=R};
  s_e^R<=s_e always;  E s_e^R<=m:=E s_e<infinity;
  P(s_e^R!=s_e)<=C exp(-c sqrt(R)).                     (5)

The domination follows because on the failure event L_e>R the default R is smaller than the actual minimum length. No error term is required for the expectation. Equality in(5) need not fail on every L_e>R because a low original can remain uncapped in both fields.

For a horizontal or vertical segment, color its edges by position modulo k_R, where k_R is an integer greater than twice the dependency radius and k_R<=C(R+1). Within one color the approximations are functions of disjoint underlying iid sets, so are independent. Different colors need not be independent.

For a segment of length ell>=k_R and a fixed d>0, if its sum exceeds (m+d)ell, some color has centered sum exceeding d ell/k_R. Each color has at most ell/k_R+1<=2ell/k_R variables, each in [0,b_R]. Hoeffding and a union over colors give

  P(sum_segment s_e^R>(m+d)ell)
  <= k_R exp(-c d² ell/(k_R b_R²))
  <= C R exp(-c_d ell/R^7)                            (6)

for R>=2, adjusting constants. This proves the R^7 exponent rather than assuming independence of an entire row.

## 2. Uniform segment bounds and macroscopic local continuity

Fix A>=2 and eta>0. Put R_n=ceil((log(n+2))^4). The number of horizontal and vertical segments in Q_{An}=[-An,An]^2 is O_A(n³). The number of edges in that box is O_A(n²). Combining(5),(6), for segments with length at least eta n, the failure probability is at most

  C_A n³ R_n exp(-c eta n/R_n^7)
  + C_A n² exp(-c sqrt(R_n)).                          (7)

This is summable in n. Indeed sqrt(R_n) is comparable to (log n)², and n/R_n^7 grows faster than any multiple of log n. For large n, eta n>=k_{R_n}. With d=1, Borel–Cantelli says that eventually EVERY such segment has s-cost at most C_0 times its length, C_0=m+1. This same C_0 works for every eta; the eventual threshold may depend on eta. Take a countable intersection over rational eta>0 and integer A.

Any shorter segment in Q_n can be extended on its line to length ceil(eta n) inside Q_{2n}, for eta<=1 and large n. Positivity bounds its cost by the extended segment cost. A coordinate route joining x,y in Q_n therefore yields, simultaneously over all x,y,

  T_s(x,y)<=C_1(|x-y|_1+eta n),                       (8)

eventually, for every fixed eta>0, with C_1 independent of eta. Enlarging the fixed ambient box only changes harmless constants. This is uniform local metric continuity with arbitrarily small linear remainder, not concentration around the time constant.

## 3. Cheap-long-path exclusion and finite minimizers

Choose a in (0,M) with epsilon=P(t_e<a)<1/144. This is possible since G({0})=0. For every e,

  s_e>=min(t_e,M).

For a fixed simple path of ell edges to have s-cost below a ell/2, at least ell/2 of its independent originals must be below a. Its probability is at most 2^ell epsilon^(ell/2). There are at most 4*3^(ell-1) simple paths of length ell from a specified vertex. With beta=6sqrt(epsilon)<1/2, a union over O_A(n²) starting vertices in Q_{An} and all ell>=n gives

  P(some such path has cost below a ell/2)
  <=C_A n² sum_{ell>=n} beta^ell.                     (9)

This is summable. Almost surely, for every fixed A and all large n, every simple path starting in Q_{An} of length ell>=n has s-cost at least a ell/2. The same is true for t since t>=s.

For a fixed start x, sufficiently long simple paths consequently have cost tending to infinity. A finite coordinate competitor has finite cost, so only finitely many path lengths, hence finitely many finite simple paths, can improve it. The infimum is attained. Loop erasure strictly reduces cost, so this proves finite-minimizer existence in both metrics. The no-tie proof in cap-core.md makes these minimizers unique.

## 4. Uniform linear length of every box-to-box geodesic

Using(7) for rows/columns of a fixed box enlargement, or(8) with eta=1, there is a deterministic C_2 such that with failure probability summable in n,

  max_{x,y in Q_{2n}} T_s(x,y)<=C_2 n.

Intersect with(9), with starts in Q_{2n}. Every geodesic between these endpoints is simple. If its length ell>=n, its cost is at least a ell/2, so ell<=2C_2 n/a. Shorter ones already have length below n. Hence a fixed L>max(1,2C_2/a) gives

  P(some geodesic between vertices of Q_{2n} has length >Ln)
  <= a summable sequence tending to zero.             (10)

The geodesic may leave the box: (9) counts all simple paths from the box, without restricting where they go. This proves the exact needed uniform length input, not just a typical endpoint bound.

For the same-status lowering use, if only one capped edge e with endpoints in Q_{2n} decreases, any new geodesic avoiding e is an old geodesic. Any new geodesic using e splits into two pieces avoiding e. Each is an old geodesic: an old cheaper competitor would also be cheaper after lowering. Both pieces have endpoints in Q_{2n}, so under the old length event their lengths are <=Ln. The new geodesic length is at most 2Ln+1<=3Ln for large n. This is the deterministic C1-to-C1' implication; no assertion about the AH order selectors is included.

## 5. Ordinary uniform shape, proved from these estimates

For integer z, the process T_s(mz,nz) satisfies the hypotheses of the standard subadditive ergodic theorem: stationarity, ergodicity under translation by z when z is nonzero, nonnegativity, and finite expectation from coordinate paths. Thus

  T_s(0,kz)/k -> mu(z)

almost surely and in L1, with deterministic mu(z). Countability makes the radial convergence simultaneous for every integer z. Homogeneity on integer multiples follows by taking subsequences. Expectation triangle inequalities and stationarity show mu(z+w)<=mu(z)+mu(w); reversal and stationarity give symmetry. Equation(9) gives mu(z)>=a|z|_1/2, and coordinate expectations give mu(z)<=m|z|_1. These facts extend mu uniquely to a norm on R², with lattice symmetries.

Fix a small eta and a finite rational directional net. For every large lattice x choose a point kz on one of these finitely many integer rays with |x-kz|<=C eta |x|; the rounding error is bounded by a fixed net-dependent constant and can be absorbed for large x. Radial convergence is uniform over the finite set of chosen rays. Equation(8), in a box of radius O(|x|), controls |T_s(0,x)-T_s(0,kz)| by C' eta|x|. Norm continuity gives the same bound for |mu(x)-mu(kz)|. Let eta decrease through a countable sequence. Therefore

  lim_{r->infinity} sup_{|x|>=r}
     |T_s(0,x)-mu(x)|/|x|=0, almost surely.             (11)

This step uses no finite-energy property and no independence of the s edges. It does not transfer(11) to the original t metric.

## 6. Extended shape with a fixed good-center event

Here is a detailed repair-safe version of the good-center step. For fixed delta>0 and deterministic integer N, define the stationary event at v

  G_N(v)={ |T_s(v,w)-mu(w-v)|<=delta|w-v|
            for every lattice w with |w-v|>=N }.

By(11), P(G_N(0)) tends to one as N increases. For a fixed small eta>0 choose ONE deterministic N so that the bad probability is less than c eta², for a sufficiently small absolute c. Apply the spatial ergodic theorem to this fixed event and its translates. Almost surely, for all sufficiently large R, fewer than (say) eta² R²/10 centers in Q_{2R} are bad, after choosing c small enough for the box-volume factor. Every eta R-ball about a point x in Q_R lies in Q_{2R} and has more lattice points than that. Thus every x in Q_R has a good center v within eta R. This is a uniform covering conclusion from the density bound; the event being averaged does not vary with v or R.

For x,y in Q_R and such a v, if |y-v|>=N then triangle inequalities yield

 |T_s(x,y)-mu(y-x)|
 <=T_s(x,v)+|T_s(v,y)-mu(y-v)|+mu(v-x)
 <=C eta R+C' delta R.

Use(8) for the first term with local remainder eta R. If |y-v|<N, instead use(8) directly for T_s(v,y), obtaining the same bound plus O(N), which is absorbed once R is large. Choosing eta and delta sufficiently small proves

  lim_{R->infinity} sup_{x,y in Q_R}
     |T_s(x,y)-mu(y-x)|/R=0, almost surely.             (12)

For arbitrary z and displacement y, take R comparable to max(|z|,|z+y|), which is at most twice max(|z|,|y|). Equation(12) then supplies the AH Proposition3.4 type estimate, simultaneously for all |z| sufficiently large and all y:

  |T_s(z,z+y)-mu(y)|<=epsilon max(|z|,|y|).             (13)

The actual AH proof uses a good-center argument; this version explicitly avoids applying the ergodic theorem to a radius-dependent event. All conclusions concern the cap norm and cap metric only.

## 7. Limits of this core

Conditional on a coalescing family already being a measurable translation-covariant function of the underlying iid field, its integrable Busemann cocycle can be handled by additive ergodic theory, a directional net and the same metric continuity. This does not construct such a family. A weak-limit extension with additional randomness is not automatically ergodic under every directional translation just because its cap marginal is a factor of iid; extra arguments there are necessary.

The estimates above prove no label stability, no initial reference-family existence, no limiting-graph uniqueness, and no iid law for s. They justify the elementary shape/length inputs that those later bridges would use. The remaining full-target obligations belong to the main proof and are not silently imported from the iid source theorem.
