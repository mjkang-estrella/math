# PCW: a proposed critical posterior wave process limit

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Third-party sources retain their rights and are private reading material.

**Status: full proof proposed for the unchanged frozen target.** No independent
proof PASS, contribution verdict, acceptance, manuscript, or formalization is
claimed. The scalar normal-form calculation is credited antecedent methodology;
the proposed contribution is the coupled path-space limit proved below.

## 1. Statement and source boundary

Use exactly the hypotheses and versions in `original-scope.md`. Write

    b=d-1 >=2, theta=b^(-1/2), beta=atanh(theta),
    kappa=sqrt(b/(b-1)), A=(b+1)/sqrt(b(b-1)),
    phi(n)=(1+(b-1)n/(b+1)) b^(-n/2).

For every finite tuple F of vertices and every finite T>0, the claim is

    (epsilon^(-1/4) m_v(epsilon t): v in F, 0<=t<=T)
       ==> (G_v(t): v in F, 0<=t<=T)                         (PCW)

in C([0,T],R^F), with uniform norm, and also with h_v=atanh(m_v)
instead of m_v. The centered continuous Gaussian limit has covariance

    E G_u(s)G_v(t) = A phi(dist(u,v)) sqrt(min(s,t)).          (1.1)

All convergence is under the actual planted observation law. In particular
the same Brownian observations are used at all times before taking a limit.
The time law is not obtained by independently sampling scalar fixed points.

Here are the only nonstandard mathematical premises taken from the stipulated
pinned manuscript P, family236. Their exact paths and Git blob identities are
in `inputs/source-authentication.json`; interfaces and reading extents are in
`source-contracts.md` and `source-reading.md`.

* P, `lem:posterior`, gives the free prior, Gaussian observation posterior,
  cavity recursion and field bound. With C=T_(v->w), set

      Y_v(t)=h_(v->w)(t), M_v(t)=tanh(Y_v(t)),
      psi(z)=atanh(theta tanh z).

  The component is a rooted b-ary tree. Each child component has the same
  field law as Y. The full-site recursion has d terms; the component
  recursion has b terms. The root is auxiliary, not added to the spin law.
* P, `prop:innovations` and its continuous-causal-version construction, give
  simultaneous continuous component and site versions, all-time recursions,
  |Y_v-X_v|<=b beta, and |h_v-X_v|<=d beta. M_v is the bounded continuous
  martingale E[sigma_v | observations in C through time t], in its own
  usual observation filtration, starting at zero. This component-filtration
  assertion is explicit at P `04-innovations.tex` 589–603. We do not need
  the field SDE, inverse innovation map, or spectral copy comparison.
* P, `lem:critical-tail`, supplies, for every fixed integer p>=1,

      E|Y(t)|^p <= C_p t^(p/4),  0<t<=t_0.                 (1.2)

  Constants depend on d,p. Only finitely many fixed orders are needed.
  P `lem:critical-information` gives the scale behind this premise, but we
  will determine its leading constant independently.

The usual free-broadcast conditional independence and Bayes spin tilt are
also derived below where needed. Standard tools used are Doob's inequality,
the L^4 Burkholder–Davis–Gundy inequality, the continuous-martingale time-change
theorem, Brownian maximal/tail estimates, and weak-convergence mapping rules.
The new martingale-array deduction is proved in Section4, not assumed from
scalar normality. Upstream truth is stipulated, not audited.

## 2. Uniform path bounds and spin tilts

All constants in what follows may depend on fixed d,p,T, or a fixed finite
subtree, as indicated. They do not depend on the small parameter epsilon,
the depth of the eventual cut, or the index of a component.

### 2.1 From endpoint moments to uniform path moments

For every fixed integer p>=2 and sufficiently small s>0,

    E sup_(0<=r<=s) |Y(r)|^p <= C_p s^(p/4).               (2.1)

Indeed, Doob and |tanh z|<=|z| give

    E sup |M(r)|^p <= (p/(p-1))^p E|M(s)|^p
                     <= C_p E|Y(s)|^p <= C_p s^(p/4).

On E_s={sup_(r<=s)|X_v(r)|<=1}, the field bound implies
sup|Y|<=1+b beta. On this compact interval |z|<=C|tanh z|,
so the preceding bound controls E[sup|Y|^p 1_(E_s)]. On the complement,

    sup|Y|^p <= C_p (1+sup|X_v|)^p.

Since X_v(r)=r sigma_v+B_v(r), for s<=1/2 the complement requires
sup|B_v|>1/2. Reflection, the Gaussian tail and integration of that tail
give E[(1+sup|X_v|)^p 1_(E_s^c)]<=C_p exp(-c_p/s).
This proves (2.1). For p=1 use Cauchy–Schwarz and the p=2 bound.

The whole-site field has the same path bound: apply its d-term cavity
recursion, |psi(z)|<=theta|z|, and Minkowski to its incoming component
fields and to its own X_v. In particular

    || sup_(r<=s)|h_v(r)|^3 ||_2 <= C s^(3/4).             (2.2)

No supremum over infinitely many vertices occurs here. We use uniformity
of the single-coordinate bounds and sum over specified finite cut levels.

### 2.2 The tilt is valid for whole histories

Let O_C^s denote all observations in a component C through time s, and let
nu_s be its unconditional law. Conditional expectation gives, for any
bounded measurable f of O_C^s and eta in {-1,1},

    E[f(O_C^s)|sigma_v=eta]
       = E[f(O_C^s)(1+eta M_v(s))].                       (2.3)

This follows by conditioning 1_{sigma_v=eta} on O_C^s and dividing by
P(sigma_v=eta)=1/2. It applies to infinite observation arrays, because
these are countable products of standard continuous path spaces.
In particular the conditional history law has density 1+eta M_v(s).
The entire M_v path through time s is measurable from O_C^s and includes
M_v(s), so its conditional law has this same density relative to its
unconditional path law. This is not just a fixed-time marginal identity.

If w is the neighbor excluded from C, conditioning instead on sigma_w=eta
changes this density to 1+eta theta M_v(s). The proof uses
E[sigma_w|O_C^s]=theta M_v(s), by the broadcast Markov property.
In particular, at a fixed time the unconditional Y law is symmetric, even
moments are unchanged by either tilt, and odd moments gain one power of Y.

## 3. Exact scalar normalization

This section uses a critical cavity normal form. The general scalar method
is established in Yu–Polyanskiy; it is supporting work, not the proposed
independent contribution. Details are included to fix the constants and
the forced-observation parameter used here.

At fixed t, put

    Q=E Y^2, R=E Y^4, q=E(tanh Y)^2,
    a=E[tanh Y psi(Y)], k=E psi(Y)^2.

From (1.2), Q=O(sqrt t), R=O(t), and E|Y|^6=O(t^(3/2)).
Given the component-root spin +1, its b child fields are independent with
law (1+theta tanh y) times the symmetric law of Y. Its own observation
is independent of these fields and has law Z_0=t+sqrt(t) Z for Z standard
normal. Set Z_i=psi(Y_i) for the children. Even moments are unchanged;
for odd j,

    E[Z_i^j | root spin +1]
       = theta E[tanh Y psi(Y)^j] = O(t^((j+1)/4)).       (3.1)

The component recursion says Y=Z_0+sum_(i=1)^b Z_i. Its second and fourth
moments, being even, are the same under this root-spin conditioning.

Taylor formulas with globally bounded remainders of the displayed orders
give

    psi(y)=theta y-theta(1-theta^2)y^3/3+O(|y|^5),
    psi(y)^2=theta^2 y^2
              -(2/3)theta^2(1-theta^2)y^4+O(|y|^6),
    psi(y)^4=theta^4 y^4+O(|y|^6),
    tanh(y)psi(y)=theta y^2+O(|y|^4).                    (3.2)

For |y|<=1 these follow from smooth Taylor expansions. For |y|>=1,
psi is bounded and the right-side powers dominate the polynomial terms;
enlarging constants makes the bounds global. Thus no truncation or
uncontrolled large-field Taylor step is hidden.

Expand the fourth moment conditionally. The terms supported on one child
and on two children of multiplicity2 give respectively b E psi(Y)^4 and
3b(b-1)k^2. All other child-only patterns are O(t^(3/2)): the patterns
3+1 and 2+1+1 use (3.1) and the even-moment bounds; 1+1+1+1 is O(t^2).
Terms containing Z_0 are also O(t^(3/2)). Explicitly E Z_0=t,
E Z_0^2=t+t^2, E Z_0^3=3t^2+t^3, E Z_0^4=3t^2+6t^3+t^4;
for the residual child sums use their fixed-order absolute-moment bounds.
Consequently, since b theta^4=1/b,

    R=(1/b)R + 3(b-1)Q^2/b + O(t^(3/2)),
    R=3Q^2+O(t^(3/2)).                                 (3.3)

For the second moment, conditional independence gives the exact identity

    Q=t+t^2+2bt theta a+bk+b(b-1)theta^2 a^2.            (3.4)

Here E Z_i=theta a, not a. This factor is needed for the constant.
By (3.2),

    a=theta Q+O(t),
    k=theta^2 Q-(2/3)theta^2(1-theta^2)R+O(t^(3/2)).

Insert these and (3.3) into (3.4), and cancel Q=b theta^2 Q:

    0=t-(2/3)(1-1/b)R+(b-1)Q^2/b+O(t^(3/2))
     =t-(b-1)Q^2/b+O(t^(3/2)).                         (3.5)

Since Q>=0, division of Q^2-kappa^2 t=O(t^(3/2)) by
Q+kappa sqrt(t)>=kappa sqrt(t) yields

    Q(t)=kappa sqrt(t)+O(t),
    q(t)=kappa sqrt(t)+O(t).                            (3.6)

The second equality follows from |tanh^2 y-y^2|<=C|y|^4.
All errors hold with one constant on a fixed sufficiently small interval.
For each fixed T, therefore,

    a_epsilon(t):=epsilon^(-1/2)q(epsilon t)
       -> kappa sqrt(t) uniformly on [0,T].             (3.7)

At t=0 both sides are zero, and the O(epsilon^(1/2)t) error is uniform.

## 4. An independent continuous-martingale averaging lemma

We need a path statement that remains valid when each summand's law
changes with epsilon. Let L_epsilon be a real continuous square-integrable
martingale on [0,T], starting at zero, such that

    E sup |L_epsilon|^4 <= C,
    E L_epsilon(t)^2 -> a(t) uniformly on [0,T],          (4.1)

where a is continuous, nondecreasing and a(0)=0. Let N(epsilon)->infinity,
and take N independent copies of this martingale with their own independent
filtrations. Then

    N^(-1/2) sum_(i=1)^N L_(epsilon,i)(t)
       ==> B(a(t)) in C([0,T]),                         (4.2)

where B is a standard Brownian motion.

Proof. Write A_(epsilon,i)=<L_(epsilon,i)>. The L^4 BDG inequality gives
E A_(epsilon,i)(T)^2<=C' E sup|L_(epsilon,i)|^4<=C''. Independence
implies zero cross brackets (the product of any two coordinates is a
martingale in the product filtration, first by testing cylinder pasts).
Thus S_epsilon=N^(-1/2)sum L_(epsilon,i) has bracket

    <S_epsilon>(t)=N^(-1)sum_i A_(epsilon,i)(t).

At every deterministic time its variance is at most C''/N and its mean
is E L_epsilon(t)^2. A finite time grid, monotonicity of brackets, and
uniform continuity of a therefore imply

    sup_(t<=T)|<S_epsilon>(t)-a(t)| ->0 in probability.   (4.3)

For completeness choose a grid on which the a-increment is at most delta;
at its finitely many endpoints apply Chebyshev and (4.1). Between endpoints
the bracket is squeezed between its endpoint values. Then let delta->0.

The continuous-martingale time-change theorem realizes S_epsilon(t) as
B_epsilon(<S_epsilon>(t)), with B_epsilon standard Brownian, on an enlarged
space if necessary. One can first extend S after T by an independent
Brownian motion, giving unbounded total bracket, so the representation
covers all of [0,T]. Independence of B_epsilon from its clock is neither
claimed nor needed. On (4.3), both clocks lie in a fixed compact interval
with probability tending to one. The standard Brownian modulus-of-continuity
bound then makes

    sup |S_epsilon(t)-B_epsilon(a(t))| ->0 in probability.

Every B_epsilon(a(.)) has the desired same law, proving (4.2). This also
proves tightness at the initial singular clock t=0; differentiability of a
is not required. This completes the lemma.

Apply it to

    L_epsilon(t)=epsilon^(-1/4)M(epsilon t).              (4.4)

Doob and (1.2) give its uniform fourth maximum bound; (3.7) gives (4.1)
with a(t)=kappa sqrt(t). Consequently *independent triangular averages*
of cavity posterior martingales converge to sqrt(kappa) B(sqrt(t)).
The actual cavity process is not such an independent average. The next
section pays that distinction in uniform path topology.

## 5. Increasing-depth decoupling on a component

Root a component at o, with b children at each vertex. Work through time
s=epsilon T, and denote by Y_u the field using descendants of u. All of
these fields have the same process law as Y_o. Their joint law is planted
and correlated. The all-time recursion and (2.1) imply

    Y_u = X_u + theta sum_(z child of u)Y_z + e_u,
    ||e_u||_(L^2(C[0,s])) <= C s^(3/4),                 (5.1)

because e_u=sum_z[psi(Y_z)-theta Y_z] and
|psi(y)-theta y|<=C|y|^3 globally. Here and below the L^2(C) norm
means (E sup|.|^2)^(1/2), not an endpoint norm.

Iterate the identity through n generations, leaving the level-n fields:

    Y_o = theta^n sum_(|u|=n)Y_u
              + sum_(j=0)^(n-1)theta^j sum_(|u|=j)(X_u+e_u).

The triangle inequality, the identical coordinate bounds and
||X_u||_(L^2(C[0,s]))<=C sqrt(s) give, with N=b^n,

    ||Y_o-theta^n sum_(|u|=n)Y_u||_(L^2(C[0,s]))
       <= C sum_(j<n)b^(j/2)(sqrt(s)+s^(3/4))
       <= C sqrt(N)(sqrt(s)+s^(3/4)).                   (5.2)

This bound is deliberately an absolute sum; no independence at internal
vertices is assumed. Replacing all leaf Y_u by M_u=tanh Y_u costs at most
C sqrt(N)s^(3/4), using the same sixth-moment maximum bound. Since
theta^n=N^(-1/2), after time/amplitude rescaling we obtain

    ||epsilon^(-1/4)Y_o(epsilon .)
       -N^(-1/2)sum_(|u|=n)epsilon^(-1/4)M_u(epsilon .)||_(L^2(C[0,T]))
       <= C_T sqrt(N)epsilon^(1/4).                    (5.3)

For sufficiently small epsilon fix, once and for all,

    n=floor(log_b(1/epsilon)/8), N=b^n.                 (5.4)

Then N->infinity, N<=epsilon^(-1/8), and the right side of (5.3)
is O_T(epsilon^(3/16)), hence vanishes.

It remains to remove the correlations of the N leaf processes. Given the
level-n spin vector eta, their descendant observation histories are
independent. Relative to N independent copies of the unconditional
component history law through s, the conditional law is the product of
the densities 1+eta_u M_u(s), by (2.3). For each fixed eta the elementary
product total-variation bound gives

    TV( product_u Law(O_u^s|sigma_u=eta_u), nu_s^N )
       <= (1/2) sum_u E|M_u(s)| <= C N s^(1/4).         (5.5)

The product bound follows by telescoping product measures one factor
at a time, with other factors probabilities. Average over the actual,
possibly strongly correlated eta distribution; the same bound remains.
Pushforward to paths does not increase total variation. Thus the joint
law of the actual leaf M paths is within C_T N epsilon^(1/4)
of N independent unconditional copies, which vanishes by (5.4), at
rate O_T(epsilon^(1/8)). This controls entire paths through T after
rescaling, not merely their finite-time marginals.

By (5.3), (5.5), and the lemma in Section4,

    epsilon^(-1/4)Y_o(epsilon .)
       ==> H(.)=sqrt(kappa) B(sqrt(.)) in C([0,T]).      (5.6)

The same holds for epsilon^(-1/4)M_o(epsilon .), since (2.1) and
|y-tanh y|<=C|y|^3 make their L^2(C) difference O_T(epsilon^(1/2)).
This completes the component functional theorem, including t=0.

The two cut requirements have different origins:

    sqrt(N)epsilon^(1/4)->0  (uniform expansion error),
    N epsilon^(1/4)->0       (planted-history dependence).

Both are checked for a single increasing n(epsilon); no fixed-depth
limit is interchanged with an unproved large-depth approximation.

## 6. Sewing a finite spatial hull

Let K be any finite connected subtree containing the desired vertex
tuple. Write partial K for the finitely many outward oriented edges
e=(x,y), x in K, y not in K. The components C_e=T_(y->x) are disjoint.
Put Y_e=h_(y->x) and M_e=tanh Y_e, using observations in C_e alone.

Repeatedly substitute the cavity equations within the finite tree K.
Linearizing psi at zero yields, for every v in K,

    h_v = sum_(x in K)theta^dist(v,x) X_x
                 +sum_(e=(x,y) in partial K)theta^dist(v,y)Y_e
                 +R_v,                                (6.1)
    ||R_v||_(L^2(C[0,s])) <= C_K s^(3/4).

Here is a justification covering the internal messages in this expansion.
For an oriented internal edge, exclude the predecessor and recursively
expand over the component of K on its forward side. Since K is a finite
tree, this terminates at the outward edges. Each own X_x appears exactly
once with one theta for every traversed edge. Each boundary Y_e appears
exactly once with coefficient theta^dist(v,y). At each traversed edge
the discarded term is psi(Y)-theta Y for an actual infinite component
field; (2.1) bounds its L^2(C) norm by C s^(3/4). There are only finitely
many such terms, with bounded fixed coefficients. This proves (6.1)
without postulating independent or small deterministic boundary values.

The own-observation sum vanishes after amplitude rescaling, in L^2(C),
at order O_K,T(epsilon^(1/4)). Boundary Y_e may be replaced by M_e with
error O_K,T(epsilon^(1/2)). Conditional on the spins at their component
roots y, the boundary histories are independent; using (2.3) exactly
as in (5.5), their joint law differs from the product of their unconditional
laws by at most C_K,T epsilon^(1/4). There are a fixed number of boundary
components, so no growing-count issue is suppressed here.

The component theorem (5.6), product convergence for finitely many independent
copies, and (6.1) now give jointly for all v in K a Gaussian continuous
path limit representable as

    G_v(t)=sum_(e=(x,y) in partial K)theta^dist(v,y) H_e(t),       (6.2)

where the H_e are independent copies of sqrt(kappa)B(sqrt(t)). Thus

    E G_u(s)G_v(t)=kappa S_K(u,v) sqrt(min(s,t)),
    S_K(u,v)=sum_(e=(x,y) in partial K)
                         theta^(dist(u,y)+dist(v,y)).    (6.3)

Formula (6.2) is only a construction of the limit on the specified finite
hull. It does not claim independent cavity processes for all oriented
edges of the infinite tree simultaneously.

## 7. Identifying and constructing the spatial Gaussian law

For u,v in K the value S_K(u,v) is unchanged when a leaf z adjacent to x
is added to K. Indeed the old boundary edge (x,z) contributes
theta^(dist(u,z)+dist(v,z)). Its b new outward successors contribute
b theta^2 times precisely that quantity, which is the same quantity at
criticality. All other boundary edges are unchanged.

Any finite K containing u,v is obtained from their joining path by
successive additions of leaves (or reduced to that path by pruning).
It therefore suffices to compute S on a path of n=dist(u,v) edges.
For n>=1 each endpoint has b outward neighbors; each of the n-1
interior vertices has b-1. Every one of these edges has exponent n+2.
Hence

    S_K(u,v)=[2b+(n-1)(b-1)]theta^(n+2)
            =[(b+1)+(b-1)n]theta^n/b
            =(b+1)phi(n)/b.                            (7.1)

For n=0 the one-vertex hull has d=b+1 outgoing edges, giving S=d/b,
the same formula. Multiply by kappa to obtain (1.1).

Existence and consistency are explicit, rather than an appeal to a name
for Gaussian waves. For every finite tuple choose its hull and use
(6.2). This gives a positive semidefinite spatial covariance matrix.
Formula (7.1) makes it independent of the hull and consistent under
restriction. Independent Brownian clocks give the stated positive
semidefinite space-time covariance and continuous finite-tuple path laws.
These centered Gaussian laws are uniquely determined by that covariance.
They are consistent on the countable vertex set. The standard countable
product extension therefore constructs the process on (C[0,T])^V;
each coordinate is continuous, simultaneously, by countability. Repeating
over integer T, or extending the Brownian construction consistently,
gives the asserted process for all t>=0. Its law is tree-automorphism
invariant because (1.1) depends only on distance.

For identification only: phi is the familiar spectral-edge Gaussian-wave
covariance, already described by Elon. It satisfies phi(0)=1,
d phi(1)=2sqrt(b), and

    phi(n-1)+b phi(n+1)=2sqrt(b)phi(n), n>=1.

The resulting Gaussian field satisfies sum_(w~v)G_w(t)=2sqrt(b)G_v(t)
almost surely: the variance of their difference is zero by these
identities (or directly from the hull representation). Rational times,
continuity and countability give the identity at all vertices and times.
No novelty is claimed for this covariance or its Gaussian-wave interpretation.

## 8. Completion, scope and checks

Sections5–7 prove the frozen full-field path convergence for every finite
tuple and every finite T. By (2.2),

    ||epsilon^(-1/4)(h_v(epsilon .)-m_v(epsilon .))||_(L^2(C[0,T]))
       <=C_T epsilon^(1/2)->0,

so the same full limit holds for the posterior magnetizations. Time0 is
included in all suprema and in the continuous-martingale averaging lemma.
No strict-temperature hypothesis, vertex-subsequence, positive-time cutoff,
independent-time resampling, or narrowed target has been inserted.

There are no numerical premises. Concrete proof checks were: the extra
theta in (3.4), fourth-moment odd-pattern accounting, the two different
cut errors in Section5, terminal-history rather than fixed-time tilts,
the component's own filtration, and finite-hull consistency. These are
analytic checks explained in the proof, not computational certification.

The scalar normalization is not nominated separately. Neither are the
component theorem, Gaussian-wave covariance, or the standard martingale
averaging lemma. The only proposed package is unchanged full PCW.
Operation comparison credits source moments, classical normal-form/branching
Gaussianity, martingale time change, and the known spatial Gaussian law.
Whether the simultaneous path decoupling beyond these operations warrants
a substantial contribution is left to an independent primary-literature
review. The author does not award a PASS or change the campaign count.
