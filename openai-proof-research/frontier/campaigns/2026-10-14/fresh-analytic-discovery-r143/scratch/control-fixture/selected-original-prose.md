# Selected-family completion: PREFREEZE, no nominee

This is an original r3 research note, not a frozen theorem, independent correctness review, contribution grade, or acceptance. Earlier r1 and r2 records retain their original bytes. The single selected family is Source377 infinity-harmonic regularity and gradient trajectories; no second family is introduced. Statements below are supporting deductions and strongest-reduction comparisons, not substitutes for an old full target.

## What is actually available

Write G = O \\ K, where O is a bounded open convex subset of R^n, n >= 2, and K is a nonempty compact convex subset of O; K may have empty interior. Let u be the infinity-harmonic potential, zero on the outer boundary and one on K, continuously extended as one through K. Put D = diam(O). The operative saved primary is Peng–Zhang–Zhou (PZZ), arXiv:2310.08093v4, not an inferred claim from a catalogue.

PZZ Theorem `c1-re` and its Section 5 proof give C^1 regularity and nonvanishing of Du on G, with u_p -> u locally in C^1 for p-harmonic potentials. Section 3 proves convexity of the superlevels from the Lewis p-harmonic result and uniform convergence. Section 4, Lemma `low-u` and its cone-comparison proof, gives

    |Du(x)| >= u(x)/D > 0.

The same lower bound holds for u_p, with u_p in place of u. The approximation also converges uniformly in value on the closed ring. Source377's authenticated introduction gives general interior C^{1,alpha_d} regularity in d >= 3, but this stronger general result is unnecessary for the chosen convex-ring deduction: PZZ already pays precisely the needed regularity. Pin and source operations remain stipulated true; no upstream truth audit is made.

## 1. The full elementary contraction, including its domain qualification

Let u be C^1 on an open set G and noncritical on the region traversed. Assume it has an extension whose superlevel sets C_s are convex, and that near a point x in G with u(x)=s this extension agrees with u. The ring case uses the extension through K. We do NOT assume the punctured set {x in G: u(x)>=s} is convex; generally it is not. The support-plane argument only uses an initial segment near x and convexity of the filled-in superlevel C_s.

For x,y in G with u(x)=u(y)=s, convexity gives u(x+h(y-x))>=s for all sufficiently small h>0. Differentiating at h=0 gives

    Du(x)·(y-x) >= 0,
    Du(y)·(x-y) >= 0.

A forward gradient curve gamma solves gamma'=Du(gamma); Peano's theorem gives local existence because the field is continuous. The chain rule gives d(u∘gamma)/dt=|Du(gamma)|^2>0, so level s=u(gamma(t)) is a legitimate parameter until the curve exits the noncritical region. Writing X(s)=gamma(t(s)),

    X'(s)=Du(X(s))/|Du(X(s))|^2,       u(X(s))=s.

For two curves on a common level interval with equal starting level a,

    (1/2) d|X-Y|^2/ds
      =(X-Y)·Du(X)/|Du(X)|^2 -(X-Y)·Du(Y)/|Du(Y)|^2
      <=0.

Each term has the needed sign separately; the unequal positive denominators cause no problem. Thus |X(s)-Y(s)|<=|X(a)-Y(a)| on every common forward level interval. No Holder exponent or Lipschitz gradient enters.

If X(a)=Y(a), the geometric curves coincide. Their physical clocks also coincide, since

    t(s)-t(a)=integral_a^s |Du(X(r))|^{-2} dr.

The integrand is continuous and positive on compact interior level intervals. This proves forward uniqueness for the original ODE, not merely uniqueness up to an unspecified reparametrization. It also proves coalescence after a meeting point. It does not prove backward uniqueness or injectivity of a flow map.

The normal-cone formulation is -X'(s) in N_{C_s}(X(s)); the above two support inequalities are exactly the monotonicity calculation for a convex sweeping process. Daniilidis–Salas, arXiv:2310.01364v2, Proposition `UniqueSolutionSweeping` and the proof of `InvertibleSweeping` explicitly use the level clock and nonincreasing distance for convex moving sets, crediting Moreau (1977). Their additional reverse-flow hypotheses are NOT needed for this forward calculation and are NOT inherited by the ring. Moreau's original paper has not been read here; its attribution is mediated by that actual primary body. The calculation itself is proved above without invoking a transitive theorem.

For completeness, on a compact filled level band a<=s<=b in the ring, the same ODE existence and |X'|<=D/a show

    d_H(C_s,C_t) <= (D/a)|s-t|   (a<=s,t<=b).

For s<t, a point already in C_t needs no motion. Any other point z in C_s has level r in [s,t); follow its forward curve to t, with distance at most D(t-r)/a. The segment of the trajectory stays in a compact band inside G; continuity and the positive slope prevent premature termination. This checks compatibility with the usual Lipschitz moving-set hypothesis instead of invoking sweeping theory without its hypotheses.

## 2. Global interior-start continuation and quantitative tails

Fix x in G and a=u(x)>0. Every closed band {a<=u<=b}, b<1, is compact in G. On it the level vector field Du/|Du|^2 is continuous and bounded, so Peano continuation reaches every level b<1. Uniqueness from part 1 patches these continuations. In particular, there is a single X_x:[a,1)->G with X_x(a)=x and u(X_x(s))=s.

PZZ's lower bound yields, for a<=s<t<1,

    length(X_x|[s,t]) <= integral_s^t D/r dr = D log(t/s),
    t_x(t)-t_x(s) <= integral_s^t D^2/r^2 dr = D^2(1/s-1/t).

Consequently X_x(s) has a single limit E(x) as s↑1, and

    |E(x)-X_x(b)| <= D log(1/b),
    0 < T(x) <= D^2(1/a-1),
    0 <= T(x)-t_x(b) <= D^2(1/b-1).

The limiting point lies on ∂K: continuity gives u(E)=1, and a limit of points outside closed K cannot lie in its interior. T(x) is positive because the clock integrand is positive on any nontrivial compact level interval. Its inverse defines the unique gradient curve up to T(x). This proves the endpoint and finite-time statements without assuming a continuous gradient on ∂K. In the u case the known global Lipschitz bound additionally makes the physical curve Lipschitz up to that endpoint; this is not needed for the tail argument.

On a fixed level a, the endpoint map is nonexpansive:

    |E(x)-E(y)| <= |x-y|        (u(x)=u(y)=a).

This follows by taking s↑1 in part 1. More generally, for u(x)=a<=b=u(y), advance x to level b first. Then

    |E(x)-E(y)| <= |x-y|+D log(b/a).

On a region u>=a0>0 where u has Lipschitz constant L for the pairs in question, this is at most (1+DL/a0)|x-y|. These are triangle-inequality consequences, not additional candidates. Equal-level contraction is not automatically contraction at a common physical time.

## 3. Stability and the full p→infinity sequence, including endpoints

For a fixed u, part 1 gives 1-Lipschitz dependence on initial points on the same level. On compact interior bands, ordinary compactness plus uniqueness also yields continuity with varying starting levels. No Osgood modulus is being smuggled into this statement.

The stronger useful stability test is the existing p-harmonic approximation. Fix x in G. Put a_p=u_p(x), a=u(x)>0. We use sufficiently large p (in particular p>n is enough to avoid point-capacity complications in lower-dimensional K). By the PZZ inputs cited above, a_p→a, u_p→u uniformly in value, Du_p→Du locally uniformly in G, and |Du_p|>=u_p/D. Each p trajectory exists and is unique in the interior because its field is smooth and nonzero; the level continuation and tail proof in part 2 apply verbatim.

To avoid silently equating different initial levels, put

    s_p(theta)=a_p+(1-a_p)theta,   s(theta)=a+(1-a)theta,
    Z_p(theta)=X_p(s_p(theta)),    0<=theta<1.

For each theta0<1, uniform convergence of values confines all Z_p([0,theta0]) for large p to a single compact interior band of u. Moreover,

    Z_p'=(1-a_p) Du_p(Z_p)/|Du_p(Z_p)|^2,
    |Z_p'| <= (1-a_p)D/a_p.

Thus Arzela–Ascoli supplies subsequential uniform limits there. Local uniform convergence of Du_p, the lower gradient bound, and the integral equation identify every such limit as the normalized-level curve of u starting at x. Part 1 makes this limit unique. The standard subsequence contradiction then proves convergence for the entire p→infinity family on each [0,theta0]. This is the same compactness/integral-equation/uniqueness mechanism used in the actual Lindgren–Lindqvist convergence proofs, with the stronger PZZ C^1 approximation already available.

The endpoint is not left behind a boundary-gradient assumption. If theta0 is close to 1, s_p(theta0) is uniformly close to 1, and

    |E_p(x)-Z_p(theta0)| <= D log(1/s_p(theta0)),
    |E(x)-Z(theta0)| <= D log(1/s(theta0)).

First send p→infinity at fixed theta0, then theta0↑1. This proves E_p(x)→E(x). The same tail estimates, and the triangle inequality via theta0, prove uniform convergence of the normalized-level curves on the closed interval [0,1] after adjoining their endpoints. No C^1 convergence up to ∂K is asserted.

Likewise let

    tau_p(theta)=integral_0^theta (1-a_p)/|Du_p(Z_p(v))|^2 dv.

At theta0<1 these clocks converge uniformly, by local C^1 convergence and a common positive denominator. Their remaining tails are bounded by D^2(1/s_p(theta0)-1). Hence T_p(x)→T(x), and the clocks converge uniformly on [0,1]. This proves arrival-time convergence with no quantitative rate of convergence in p. A rate does not follow from qualitative C^1 convergence.

PZZ's already-proved existence curve has nondecreasing speed and convex u∘gamma; uniqueness identifies the unique forward curve with that curve. Alternatively, at finite p the identity

    d²(u_p∘gamma_p)/dt² = -2 |Du_p|² Delta u_p/(p-2) >=0

passes on compact physical-time intervals through the local C^1 convergence. Both paths are compatible classical compositions. This note does not infer constancy of speed from an a.e. Sobolev identity along arbitrary curves.

## 4. What the general Source377 regularity cannot supply

The credited Aronsson saddle u(x,y)=|x|^(4/3)-|y|^(4/3) is infinity-harmonic and C^{1,1/3}. Even a nonzero gradient at the start does not ensure uniqueness without convex superlevels. Fix c>0 and start at (0,c). For any waiting time q>=0, on a time interval 0<=t<9 c^(2/3)/8 the curves

    x_q(t)= (8/9)^(3/2) (t-q)_+^(3/2),
    y(t)= (c^(2/3)-8t/9)^(3/2)

solve (x',y')=Du(x,y). The identically zero x-component is another solution, as is the negative of x_q. Direct differentiation gives x'= (4/3) sign(x)|x|^(1/3) and y'=-(4/3)y^(1/3), including the C^1 joining at t=q. Throughout such an interval y>0, so Du is nonzero. Additional coordinates may be kept constant in higher dimensions.

Thus arbitrary-source forward uniqueness is false, including a noncritical local version. Holder regularity alone does not pay it. There is no unpaid positive conjecture at that unrestricted scope to nominate; convexity is an essential added structural premise of the supporting deduction, not a substitute solution of an old full target.

## Stopping point

The proposed uniqueness mechanism, local stability, full-sequence approximation, endpoint convergence and finite arrival-time limit all reduce to PZZ's already-available convex-ring regularity/approximation, normal-cone monotonicity, inverse clocks, compactness and elementary integrable tails. The older paper's remark that higher-dimensional uniqueness was unclear does not by itself establish substantial contribution. No nonroutine mathematical operation is isolated after this composition. The determination here is PREFREEZE/no nominee, not an independent TECHNICAL verdict. It makes no priority, current-open, literature-exhaustion or family-exhaustion claim.
