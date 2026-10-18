# T224G: replacement for path-series-tightness §4

This section replaces the original §4 and its clock discussion. Sections1–3 and the finite-coefficient replacement are used at exactly their reviewed scope. The finite-dyadic-core repair is credited to the independent proof reviewer in t224g-proof-r1, required repair R1. This integration is author work, not a new independent review. It asserts no improvement to the separate TECHNICAL contribution classification.

Fix an arbitrary finite T>0. Let S=D([0,T],H_C), with the full-plane J1 metric from GPS(9.7) and Definition4.2. Let W_e be the stationary Voronoi birth/death crossing path at physical time r_e t/2. Let W_delta^tri be stationary triangular fair-refresh dynamics with rate r_delta=1/E N_delta(Q_*). No equality of this rate with the original GPS rate is assumed.

## 4.1 Inputs actually used

For every fixed finite polygonal quad family Q, the preceding path-series argument gives tightness of its finite crossing-vector paths and, uniformly in mesh, a bound

 P(a visible vector jump in a deterministic interval I) <= C_Q,T |I|+o_mesh(1).       (A)

It also bounds short endpoint windows and collisions, as established in §2 from the summable signed-measure majorant b_k=C_T^k k^(-theta k), theta>0, and the uniform time-mark densities. The finite-coefficient argument §6 supplies limits of every finite collection of crossing observations; these limits are the same for the Voronoi and triangular unit-pivotal-clock models. Its two-replica version supplies the common limits for two processes independent conditional on the initial uncolored Voronoi geometry. The corresponding triangular replicas are independent.

For clarity, the triangular path-valued estimate needed here is justified by the same support argument, not by assuming coordinate continuity in H. Replace a scalar test kernel by the signed sum of point masses at finite-vector paths. Its variation is bounded by2^k, and noncancellation at a selected site requires influence on one of the fixed quads at some time. The unchanged agreement probes give the source forest bound, with no factor from the number of observation times. On each selected triangular site, conditional on at least one refresh, two or more refreshes have mass O_T(r_delta). The pointwise-in-history forest bound makes their total path-law error O_T(r_delta) sum_k k b_k. One-refresh times have bounded densities (indeed uniform conditional on exactly one refresh), so separated-time compactness and(A) follow. The same argument with two labels gives tightness on the vector state space E×E. These are exactly the existing source V forest and author path-measure operations, with their constants depending on Q,T.

GPS Proposition3.9(i), Definition3.3, heredity and(9.7) imply the deterministic finite-core fact: for each epsilon>0 there is a finite union Q_epsilon of dyadic polygonal quads in finitely many boxes such that equal Q_epsilon vectors imply d_HC<=epsilon for ALL full-plane states. For absent Q, heredity excludes the harder displaced quad; for present Q, Q itself is in its open quad-neighborhood. Thus equality implies membership in the required O_k neighborhood. Discard the bounded metric tail in(9.7) and choose the finite cores in the retained boxes. No critical law or boundary-nullity assertion enters this fact.

## 4.2 Discrete vector paths are identified first

Fix epsilon and its core. Let E_epsilon be the finite set of crossing vectors actually realized by full-plane states, equipped with the discrete metric. This avoids choosing representatives of impossible Boolean patterns. Choose one full-plane representative h_v for every v in E_epsilon. Define

 Psi_epsilon(v)(t)=h_(v(t)).

This map D([0,T],E_epsilon)->S is J1-continuous: under a J1-convergent sequence in a finite discrete space, a sufficiently accurate time change matches the entire state list exactly, and the same time change works after applying v->h_v. In the GPS logarithmic time-change metric the time distortion is unchanged. For each discrete-model path,

 d_S(W,Psi_epsilon(V_epsilon(W)))<=epsilon                         (B)

with the identity time change. The selector on H need not be continuous. We never apply it by a continuous-mapping theorem to an unknown H-valued limit.

By(A) and the compactness proved in §2, the Voronoi vector laws are tight. Each subsequential limit has no jump at a fixed deterministic t in(0,T). To justify passing the bound, realize a convergent subsequence almost surely in discrete-state J1. A jump of its limit at t forces a prelimit jump in every sufficiently small neighborhood of t, because the aligned state values agree. Fatou and(A) give probability at most C eta for this event; send eta to zero. Endpoint evaluation is continuous in J1; the endpoint-window estimate additionally rules out an endpoint jump if needed. Thus evaluation at every deterministic observation time is almost surely continuous in the limit. The supplied vector FDD limits are therefore its FDDs.

These FDDs determine a unique law on D([0,T],E_epsilon), since evaluations on a countable dense time set together with T generate its Borel sigma-field and a cadlag path is determined by those values. Denote this law by nu_epsilon. Hence the full Voronoi vector sequence converges to nu_epsilon.

The triangular vector laws are tight by the triangular path-series argument above, have no fixed jumps, and have the SAME supplied FDD limits. They too converge to nu_epsilon. This identifies finite-vector path laws without asserting that any Voronoi H-valued marginal is already the critical law.

## 4.3 Full-plane path-law identification

Let rho_epsilon=(Psi_epsilon)_* nu_epsilon. The full-plane path laws of both models are tight, by(B), finite-vector tightness and the complete-metric approximation argument in §3. Explicitly, at a sequence epsilon_j decreasing to zero, choose compact sets K_j for the approximate path laws with summable exceptional probabilities. The intersection of the closed epsilon_j-neighborhoods of K_j is closed and totally bounded, hence compact in the complete compatible J1 metric. This gives tightness for each model; finitely many initial meshes do not affect the subsequential assertion.

Use the Lévy–Prokhorov metric on probability laws on S. The pathwise coupling(B) gives distance at most epsilon between each original path law and its finite-core approximation. By continuity of Psi_epsilon, the approximating laws converge to rho_epsilon. Consequently every subsequential limit mu of either model satisfies

 LP(mu,rho_epsilon)<=epsilon.                                      (C)

If mu and mu' are any two subsequential limits, even from different models, their distance is at most2epsilon by(C). The argument is valid for every positive epsilon, with no need to make the chosen cores nested. Letting epsilon decrease to zero proves equality of the limits. Tightness guarantees existence. We have therefore constructed a unique triangular unit-pivotal-clock path law mu_T and proved W_e converges in law to mu_T on the FULL-PLANE space S.

This does not pass crossing indicators through H-valued weak convergence. Critical-state boundary nullity, GPS Theorem2.7, and an unstated H-valued critical Voronoi convergence theorem are not hypotheses of this argument.

## 4.4 Two replicas and quenched convergence

Use two Voronoi processes independent conditional on the initial UNCOLORED geometry G_e. For the same finite core, their joint vector takes values in E_epsilon×E_epsilon. The reviewed two-label path-TV bound gives tightness in D([0,T],E_epsilon×E_epsilon), and(A) applies to any visible vector jump. Its FDDs have the common limits supplied by the two-replica coefficient calculation. Those are the FDDs of two independent triangular vector limits. Thus the discrete-vector argument identifies its full path law with that of two independent nu_epsilon paths, viewed jointly. Independence here follows from triangular independence and the already proved single-vector convergence, or equivalently from factorization of all finite-dimensional cylinder laws. It is not inferred from sharing a Poisson base.

The representative map from joint vector paths to S×S is continuous, using one time change in its domain and hence a valid time change for each component. Its limit is rho_epsilon tensor rho_epsilon. Under the max product metric, the original pair and its representative pair are within epsilon pathwise. The joint original laws are tight (marginal tightness suffices). Any subsequential joint limit pi therefore satisfies

 LP(pi,rho_epsilon tensor rho_epsilon)<=epsilon.

Since LP(mu_T,rho_epsilon)<=epsilon, independent product couplings give LP(mu_T tensor mu_T,rho_epsilon tensor rho_epsilon)<=2epsilon (a union bound suffices). Therefore LP(pi,mu_T tensor mu_T)<=3epsilon, and epsilon->0 proves pi=mu_T tensor mu_T. Only product J1 is claimed for the pair; this is sufficient for the conditional-law argument.

Let K_e be the random conditional law of W_e given G_e. For every real bounded continuous Phi on S, conditional independence gives

 E K_e(Phi) -> mu_T(Phi),
 E[K_e(Phi)^2] = E[Phi(W_e^(1))Phi(W_e^(2))] -> mu_T(Phi)^2.

Thus K_e(Phi)->mu_T(Phi) in L². To pass to random probability laws, choose a compact K carrying all but an arbitrarily small mass of the annealed laws and of mu_T. Markov's inequality applied to K_e(K^c) makes the conditional mass outside K small in probability. Restrictions of the bounded1-Lipschitz test functions to K have a finite uniform net. The preceding L² convergence for those finitely many tests, plus the outside-K bound, proves convergence in probability in the bounded-Lipschitz metric. Hence K_e converges weakly in probability to mu_T. This retains all initial-color, birth and death randomness in the conditional law and conditions only on the original uncolored geometry.

## 4.5 Reference clock and optional GPS corollary

The limit just constructed is precisely the triangular limit at r_delta=1/E N_delta(Q_*), which is the frozen reference clock. GPS Definition1.3 instead uses rho_delta=delta²/alpha4(delta,1). The supplied pivotal-scale comparison bounds r_delta/rho_delta above and away from zero, but does not set it equal to1. On any subsequence choose a further one where this ratio converges to c in(0,infinity). GPS Theorems1.8 and9.8 identify the reference-clock path law along that further subsequence as the deterministic time change t->W_GPS(c t). One can work on a larger fixed time horizon; deterministic time-rescaling converges in J1 at horizons with no fixed jumps. The finite-vector small-window argument above also yields absence of deterministic jumps for the identified full-plane law by the uniform core approximations.

Uniqueness of mu_T makes this time-changed LAW independent of the chosen rate-ratio subsequence. No uniqueness of the numerical ratio or equality c=1 is claimed. GPS Proposition9.7 then gives mu_T's fixed-time critical marginal P_infinity as a COROLLARY. Neither that marginal identification nor GPS crossing-boundary nullity was used to obtain mu_T or the quenched convergence.

## Scope and status

T was arbitrary. The proof retains every finite time horizon, the full plane, one common state-path time change, the physical Voronoi factor r_e/2, the prescribed triangular unit-pivotal clock, and quenched weak convergence in probability. The repair introduces no source strengthening and no new probabilistic estimate beyond the reviewed path-series and fixed-coefficient inputs. It does not repair, re-prove or expand unrelated geometric lemmas. This is the review-supplied R1 repair integrated for a technical archive; any fresh proof review is a parent decision, not claimed here.
