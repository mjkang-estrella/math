# Analytic r137 — thermal-floor Boltzmann question (PREFREEZE)

Working research, not a frozen theorem, author-proof nominee, manuscript, or independent grade. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and operative source proof operations are stipulated true.

## Full question retained during derivation

On the unit three-torus, does there exist a nonnegative density F0, constants a,b>0, with F0(x,v)>=a exp(-b|v|^2) almost everywhere, finite mass, energy and absolute entropy, and two distinct global entropy solutions of the hard-sphere Boltzmann equation with THAT SAME F0, both in the exact October Source363 class: strong L1 continuity for all nonnegative times; exact local conservation of mass, all momentum components and kinetic energy including initial traces; the stated entropy-dissipation inequality; and separate gain/loss integrability with every polynomial velocity weight on every bounded time interval? Difference must have positive spacetime-velocity measure. No bounded-velocity-support condition is imposed because it is incompatible with the floor. No L2 initial-data claim is imposed: r52's full L2/bounded-support question is separate and unchanged.

The floor is uniform in space and all velocities. Positivity almost everywhere with a floor flat near the concentrating axis is not this question. Removing only the high-velocity cutoff while keeping a spatial hole is not this question. Nearby initial data, finite-approximation seed separation and stationary solutions of another collision equation are not answers. This is a feasibility question, not an asserted theorem or claim of novelty from hypothesis removal.

## Actual source mechanism and compatible classical operations

Use the exact October normalization P(f,g)=Q+(f,g), symmetric for hard spheres, and nu_f(v)=2 pi integral |v-p| f(p) dp. Let D=partial_t+v.grad_x. The source weight is H=e^{-|v|^2}<v>^-100(1+|vbar|^-q), 1<q<2. A colder Maxwellian lies below C H.

The source cold datum has disjoint scale-s spatial masks, mass O(s^2), velocity width d_s=d0 s^10 and amplitude about s^-31. Its scalar mass amplitude near the active core is O(1/(s+t)); both stream signs average to a two-stream measure only AFTER dilation. At finite scale distinct opposite stripes do not overlap. Cold self gains and nonmain tails already have the source's full barriers.

The October construction contains a nearly Maxwellian bath outside a fixed spatial hole. Its weighted bath estimate is C exp(-b'|v|^2) exp(-c dist(x,hole-complement)^2/t). Hence cold-bath production is flat at t=0 on the active cores. The source already pays cap selection, cold optical-depth control, velocity averaging, five-gain/nonconcentration, robust branching, and global retirement/entropy continuation at their exact hypotheses. These are not new operations.

The source's entropy/flight-average construction is the compatible global continuation framework to examine after an early weighted hot bound. DHWY supplies a bounded-amplitude antecedent, but its theorem does not apply directly to the singular H class. A floor does not give the required early upper bound. Nor does failure of one coarse Gronwall inequality prove it cannot hold.

## Initial floor insertion and an actual gain calculation

Take the original F0 and add A mu, where mu(v)=exp(-b0|v|^2), A>0. Its entropy and all polynomial moments remain finite. One elementary bound proving this is (f+g)log(f+g) <= f log f+g log g+(f+g)log2 for nonnegative f,g, interpreted by continuity; the negative entropy is controlled by the existing Gaussian-reference mass/energy estimate. The added term makes F0>=A mu uniformly. Finite cutoff equations remain meaningful since each retained jet and mu have finite H norm. This constructs admissible DATA, not the required solution pair.

Keeping the old colors makes the new hot source include 2A P(c,mu). Its lack of flatness is not just an upper-bound artifact. At a point in an initial sign mask with |z|<=c s, the cold velocity measure has total mass comparable to 1/s and converges, after multiplication by s, to a nonzero multiple of delta_p, p near +e3 or -e3. For any nonzero nonnegative compact velocity test phi,

  integral phi(v) P(c,mu)(v) dv
   = integral c(p) mu(q) |(p-q).omega| phi(p-((p-q).omega)omega) dp dq d omega.

This follows by the elastic change of variables, whose Jacobian is one. Choose phi supported in a small ball off the velocity axis reached by an open set of collisions with p near e3 and q in a fixed ball. Such open q,omega sets have positive measure and relative speed bounded below. Compactness and positivity of mu then give

  integral phi P(c,mu) >= c_phi/s

uniformly on a smaller initial core and sufficiently small s. The upper bound C_phi/s follows from bounded incoming cold speeds and Gaussian mu. Thus the instantaneous hot source is genuinely of order A/s there. This does not by itself imply a lower bound at later times: transport and depletion must be retained.

In particular the old bound S<=C_L t^{L-1}H, uniform in the retained smallest scale, cannot hold near t=0 for this same color assignment. Each fixed finite approximation has positive source trace at such a core, while t^{L-1}->0 for L>1. A tiny FIXED A is not flat in t. Sending A to zero with the approximation would lose the requested fixed positive floor.

## Stronger reorganization: mark descendants of the seed

A compatible reorganization removes that source term entirely, so the preceding observation is not the end of the analysis. Let b denote all particles not descended from the distinguished seed and h its descendants. At each finite cutoff define

  D b = P(b,b)-b nu_{b+h},
  D h = P(h,h)+2P(b,h)-h nu_{b+h}.

Every seed/nonseed collision puts BOTH outgoing particles in h. Their sum F=b+h solves the exact cutoff Boltzmann equation. Both equations preserve nonnegativity, and h=0 is invariant. This is a standard collision coloring, credited rather than nominated. The unseeded b solves the full Boltzmann equation from the floored datum. Thus a positive background does not inherently create a source in the *descendant* equation.

At a cap h<=m_T(t+s_N)H, seed-induced killing of b is integrably small. If one could independently keep the unmarked remainder dilute, then after t,x rescaling by r the coefficient r b could converge to the source cold measure B, and h/(m_T r) would satisfy the SAME paid linear branching equation

  D g=2P(B,g)-g nu_B.

This is the strongest compatible integrated reduction examined so far. Declaring that all forward coloring fails merely because the old hot source is nonflat would miss it.

## Why a nonzero descendant limit does not yet separate total solutions

Let b^0 be an unseeded solution and b^h the unmarked component of a seeded solution, at the same finite cutoff. Put d=b^h-b^0, so d(0)=0. Exact subtraction gives

  D d = 2P(b^0,d)+P(d,d)
          -d nu_{b^0}-b^0 nu_d-d nu_d-b^h nu_h.

The total difference is d+h. The forcing -b^h nu_h is negative, while the linearized loss -b^0 nu_d has no positivity-preserving sign. There is no general order comparison b^h<=b^0 furnished by the gain positivity. Under hypothetical linearization d=eta d1, h=eta h1, its first-order equation has all of these linear loss-feedback terms; omitting -b^0 nu_d is invalid.

The old separation step compared a nonzero h dilation with a total dormant F that vanished off the axis after division by m_T T. A uniform positive initial bath invalidates the literal vanishing argument. To use descendant marking, one must instead show that d/(m_T r) has negligible off-axis part, or otherwise prove d+h cannot cancel, at the actual cap scales. No such estimate follows from source weak stability. Conservation is consistent with cancellation: descendants gain mass by converting unmarked particles, not by creating mass in F.

## Current feasibility ledger

No scope has been frozen. No two floored solutions have been constructed. Next test: can a uniformly H-bounded unmarked thermal remainder coexist with the source's nondepleted cold dilation and its supercritical branching? The source's stronger positive-history growth, rather than only its top theorem, must be used to assess this bootstrap.

## Completed test of the uniform thermal bound

This is a source-composition diagnostic for the specified cold construction, not a substitute theorem or a nomination. Fix the source's branching parameters once and for all, and use the original finite cold colors with initial noncold part equal to the original exterior bath plus A mu, A>0 fixed. Let a_N be ALL noncold particles (not merely seed descendants), c_N=sum_i c_i, and let the collision cutoff tend to infinity with N. Before the first retirement, the exact equations are

  D c_i = P(c_i,c_i)-c_i nu_{c_N+a_N},
  D a_N = 2P(c_N,a_N)+P(a_N,a_N)
             + Scc_N-a_N nu_{c_N+a_N},
  Scc_N = sum_{i != j} P(c_i,c_j).

Cutoff superscripts are suppressed. The sum solves the correct finite equation. Consider the proposed bootstrap: there exist t1>0 and C<infinity, independent of N and cutoff along this sequence, such that these finite evolutions exist on [0,t1] and 0<=a_N<=C H there. Reduce t1 below one and the first retirement if necessary. This particular bootstrap is incompatible with the source branching operation, as follows.

Set r_N=s_N, l_N=s_N/r_N=1, C_N^r=r_N c_N(r_N t,r_N x,v), and a_N^r=a_N(r_N t,r_N x,v), with NO amplitude normalization of a_N. On each fixed dilated interval [0,L], the cold upper barrier from 05-cold, proposition cold:control, is independent of the thermal density. On every compact range of scaled annuli s/r_N, the thermal contribution to the free-core optical depth is O(C r_N L). The same-color contribution is O(r_N d_s/s), the remainder O(r_N s^(15/2)), and the distinct nonmain colors are flat. Therefore the source free-core survival sandwich remains valid. Its exact Jacobian calculation and stripe averaging identify C_N^r with precisely the source medium B on the mesh {1,e^eta,e^(2eta),...}. The largest retained scaled annulus tends to infinity.

The thermal equation rescales to

  D a_N^r = 2P(C_N^r,a_N^r)-a_N^r nu_{C_N^r}
                + r_N Q(a_N^r,a_N^r)
                + r_N Scc_N(r_N t,r_N x,v).

Here Q(a,a)=P(a,a)-a nu_a. Under a_N^r<=C H, the nonlinear term is bounded by C' r_N <v>H. The cross-color source remains flat by the cold geometry and upper barriers; unlike the failed old hot coloring, it contains NO cold-thermal term. Thus its rescaled contribution tends to zero. The sheet gain bound and l_N=1 bound all transport derivatives by C_L <v>H down to time zero on every fixed dilated interval. This integrable majorant gives local weak compactness, strong compactness of velocity averages (08-compactness, comp:averaging), and the mixed cold-thermal product passage proved in 09-dilation. In particular the averaging is not replaced by a product of weak limits.

A diagonal extraction on all finite dilated intervals is allowed because t1/r_N tends to infinity. It gives

  0<=g<=C H,     Dg=2P(B,g)-g nu_B     on (0,infinity).

The same down-to-zero majorant and integrated transport equation give local strong L1 continuity at zero with trace A mu: the original bath vanishes in a fixed physical spatial neighborhood, so on every compact dilated spatial set a_N^r(0)=A mu eventually. One can obtain the trace directly by bounding the integral of the transport derivative by C_L t on compact sets and using free translation of A mu. Positive-time gain/loss integrability and the mild formula are exactly those supplied by the source product and transport argument. Consequently g is nonzero.

But g/C<=H<=(t+1)H, whereas 11-branching, proposition prop:finite-dilated-horizon, says that the only global nonnegative mild solution of this linear equation with this cap, for EVERY permitted mesh and l=1, is zero. Contradiction. The operative proof uses compact positive collision histories, retention, a three-collision minorization, robust block reproduction, accessibility, and iteration. Its reproduction factor is at least three on multiplicative time blocks whose expansion factor a_br satisfies (1+a_br)^4<3. This is stronger than failure of a coarse upper estimate.

The conclusion concerns the simultaneous uniform-H bootstrap and continuation for THESE finite cold-color approximations with a fixed positive floor. It does not contradict finite-N local existence, assert uniqueness or nonuniqueness of the floored full datum, or exclude other cold constructions, time-dependent weights, nonlinear depletion, or forward methods. No upstream operation is being audited or proposed as new.

## Time-singular repair: what the scaling does and does not pay

A possible alternative estimate is a_N(t,x,v)<=C(t+s_N)^(-alpha)H(v), 0<alpha<1. This is unproved. At the smallest scale r_N=s_N, its thermal optical depth on [0,r_N L] is O(r_N^(1-alpha)); hence cold survival on fixed dilated intervals is still compatible with this estimate. To get compactness one must now normalize g_N=r_N^alpha a_N^r. The equation becomes

  D g_N = 2P(C_N^r,g_N)-g_N nu_{C_N^r}
                  + r_N^(1-alpha) Q(g_N,g_N)
                  + r_N^(1+alpha) Scc_N(r_N t,r_N x,v).

The bound is g_N<=C(t+1)^(-alpha)H, but its initial trace is r_N^alpha A mu, which tends to ZERO. The same source branching result forces every global extracted normalized limit to be zero, and supplies no contradiction: the nonzero initial floor disappeared under normalization. This is one reason the previous diagnostic must not be advertised as an obstruction to all time-singular estimates.

Conversely this scaling compatibility is not a proof of the proposed estimate. Linear positive histories suggest large amplification of the ambient thermal floor over many scales. Passing from fixed dilated intervals to a number of multiplicative blocks growing with N would require uniform quantitative error control for the actual striped cold medium and the evolving reservoir. The source's qualitative fixed-compact convergence does not automatically permit that passage. This growing-horizon operation is not proved here, nor is impossibility of the time-singular estimate.

There is also a separate integrability issue. A pointwise t^(-alpha)H bound controls the noncold/noncold collision integral with every polynomial velocity weight by C_k t^(-2alpha) on the finite-volume torus, using the source H kernel bound and integrable Gaussian velocity tails. Thus alpha<1/2 would be a sufficient condition for THIS term near zero. Mixed cold/noncold integrals additionally require the uniformly integrated cold weighted moments, and no pointwise t^(-alpha) estimate may be cited as an automatic proof of all local conservation/entropy/trace conclusions. An alpha in (0,1) only makes the short core optical depth integrable; it does not by itself close the full requested solution class.

## Actual primary reduction and its boundary

Duan--Huang--Wang--Yang, arXiv:1603.06037v2, theorem 1.1, allows large but FINITE weighted L-infinity amplitude Mbar, with smallness thresholds depending on that amplitude, as well as a small spatially integrated velocity supremum and entropy defect. The proof of lemma 4.2 estimates the gain using a weighted velocity supremum and a local velocity L1 factor, through a Carleman/Hölder split. Lemma 5.1 and the global bootstrap use flight averaging, velocity truncations, a short-time cutoff, and entropy to control that L1 factor. The constants and local lifespan depend on Mbar. This actual proof is compatible with bounded-amplitude approximations but does not remove their amplitude dependence.

Here the cold initial amplitude scales as s_N^(-31). A scale-s packet has spatial volume comparable to s^3 in its nonnegligible axial core, so its contribution to the spatial integral of the velocity supremum scales as s^(-28), up to fixed parameters. Consequently the classical hypotheses do not remain uniform in N merely because mass and entropy do. A Gaussian lower floor supplies no missing upper estimate. This comparison uses the primary proof, not a claim that all classical bounded-data methods fail.

Chen--Guo--Shen--Zhang, arXiv:2606.01331v3, was read at its theorem/outline interface only: its nearby-data instability does not directly give two solutions of the SAME datum in this class. Gismondi--Golding--Novack, arXiv:2608.13758v1, was read at its stated stationary Krieger--Strain flexibility interface; it is a different equation and does not give this full Boltzmann conclusion. Their lower proofs were not used to infer an impossibility or a literature-wide novelty claim.

## End state: PREFREEZE / no nominee

No exact theorem was frozen because full proof feasibility did not close. The retained full question is the one at the start of this file, not a weakened floor, a time-limited approximation statement, or a linear branching diagnostic. What remains unpaid is a nonlinear early-time construction for the fixed floored datum with a compatible thermal-reservoir bound (or a different construction), followed by a genuine separation of two TOTAL solutions and passage to the complete global entropy/local-conservation/strong-trace class. Descendant marking alone does not pay the signed reservoir response, and the old dormant off-axis comparison cannot be reused unchanged.

The late uniform-H contradiction and the time-singular normalization calculation are prefreeze evidence, not a substantial full-scope result. Old r52 L2/bounded-velocity nonuniqueness, I20 microscopic branch selection, and the user-specified frozen/completed scopes remain unchanged. I20's operative original was read late (lines 1--220) after the main coloring derivation; it concerns microscopic same-evolution selection and its regular approximation gap, not the thermal-floor question. No absence-of-overlap or worldwide-priority claim is made.
