#140 quantum-memory interface — working, not frozen

Contemplated FULL target Q140 (not yet frozen): for each fixed A>0 there are c_A>0,d_A such that, for d>=d_A,0<epsilon<=1/10, every one-pass quantum learner with persistent Hilbert-space dimension D<=2^{A d^2}, given fresh independent classical x_t~N(0,I_d), y_t=<x_t,S>, S uniform on S^{d-1}, and producing a classical unit vector with average angular success>=2/3 by deterministic horizon T, has T>=c_A d log(1/epsilon). No restriction to commuting states, fixed measurement bases, measure-and-prepare updates, polynomial computation, or unentangled persistent registers. All retained classical control counts in the Hilbert-space dimension as orthogonal sectors; only the public sample index and a data-independent shared seed are free. Input rows may not be revisited. Borel CPTP instruments may use the entire current exact pair and disposable ancillas. Stopping by T is allowed, with output from terminal register, stopping index and fresh randomness only. All initial states/seeds are independent of signal and rows. Quantum sample oracles are NOT supplied.

This is a proposed research scope, not a proved theorem, freeze or nomination. Primary and all companion interfaces are still being checked.

Scalar source: private/140-2/build/sections/blocks.tex, Lemma h:block:bound. Let a=(d-1)/2 and q=floor((d-1)/8); for m<=q, finite continuation success functions h_j satisfy integral over each sphere-centered ball B(z,r) <=(Rr)^a. Routing probabilities g_j(A,b)>=0 sum<=1. The backward h has local mass<=exp(Cd) N^(1/q)(Rr)^a. This uses private/140-2/build/sections/projection.tex, Theorem h:dv:finite-density: a finite positive scalar measure supported on B(z,r) with ambient mass<=H t^beta, beta>m+q-2, has exact (A,As)-density f relative to lambda_m=gamma_m(dA)db with Lq norm bounded by
(2pi)^(-m(q-1)/(2q)) H r^[beta-m(1-1/q)] [product_{j=0}^{q-2}(1+3^j 2^beta m/(beta-j-m))]^(1/q).
For beta=a this is exp(Cd)H r^[a-m(1-1/q)]. Exact projected ellipsoid lambda-volume is<=exp(Cd)r^m. Radius powers cancel under Holder.

Quantum backward formulation: a continuation is a Borel effect H(s) in M_D,0<=H(s)<=I. For every input density rho, its future success is Tr(rho H(s)). The natural invariant is the operator inequality integral_{B(z,r)} H(s)d sigma(s) <= (Rr)^a I. Terminal POVMs obey it by the scalar cap calculation tested against arbitrary rho.

For a fixed incoming rho, an m-row CPTP block produces a positive output matrix rho(A,b) with trace1; stopping can instead be represented by a finite direct sum of subnormalized destination matrices with total trace1 and at most(m+2) blocks. Its score is integral Tr[rho(A,As)H(S)] over S,A. Localize the matrix measure H(s)1_B(s)d sigma and push it through (A,s)->(A,As), obtaining a PSD matrix density F(A,b).

Sufficient NEW estimate: under the operator ball bound mu(B(x,t))<=H0 t^a I, and support B(z,r), prove
 integral Tr(F(A,b)^q)d lambda_m <= D [exp(Cd) H0 r^[a-m(1-1/q)]]^q,
uniformly in D. With direct-sum stopping sectors use D'<= (m+2)D. Schatten Holder plus Tr(rho^{q'})<=1 and the exact ellipsoid volume then give exp(Cd)(D')^(1/q)(Rr)^a. Taking the a-th root recovers exp(O(1+log D/d^2)) per block. This would pay the backward iteration; the full-data constant-accuracy endpoint still must be justified for quantum outputs, likely by data processing from the whole classical transcript.

Why scalar proof does not automatically prove this: its qth moment expands into positive scalar replica products and integrates an inverse Gram determinant by successive affine-distance bounds. Matrix expansion contains Tr(H(s1)...H(sq)), which need not be nonnegative. Replacing H by Tr(H) incurs D in the mass coefficient, not D^(1/q); an entrywise expansion similarly loses the desired memory dependence. No matrix estimate or impossibility theorem is claimed yet. A counterexample to this estimate would reject this repair, not automatically Q140.


## Further attempted routes, still unpaid

A residual-subsphere formulation from companion140-6 supplies an operator conditional-mean bound for H(Y_j) by testing its scalar cap estimate against each fixed vector. This is not yet a homogeneous high-moment bound for the random fiber average. Applying matrix concentration to a sum of q replica effects retains repeated-index terms. Already (sum_j H_j)^2 contains sum_j H_j²; under only0<=H_j<=I, its expectation is controlled at order qK, whereas the desired homogeneous estimate scales as K². Local K can be arbitrarily small. Thus that direct empirical-sum comparison does not establish the required inequality. Taking arbitrarily many replicas is not licensed by the source's dimension margin. This identifies a debt of this attempted proof, not a counterexample to the desired matrix estimate or Q140.

The source's scalar positive-cap domination can also be tested against each fixed vector, but separate scalar dominating measures do not yield one positive operator-valued decomposition uniform over vectors. A semidefinite dual argument would require operator-valued tests; substituting the scalar duality result at that step is circular with the present obligation.

Similarly, a classical discretization of all pure input directions incurs a net with exponentially many points in D, not polynomially many in D. That loses the desired log D memory scale when D itself is exponential in d². This does not rule out a structured quantum simulation, but it excludes treating a generic state-space net as free.

The parent second-moment proof at ../quantum-regression-parent-r1/matrix-second-moment.md was read in full and checked author-side. It obtains sqrt(D), not D^(1/q), with exact Gaussian labels. Its nonpositive trace and nonpositive-functional examples reject literal Loewner iteration. No higher-moment impossibility follows. Parent work is author collaboration, not an independent gate.
