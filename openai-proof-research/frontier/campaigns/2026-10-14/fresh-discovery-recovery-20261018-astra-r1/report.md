# T369H remains unresolved: a quartic boundary obstruction

Status: **NO NOMINEE; full frozen quantitative target unresolved.** This packet proves a local analytic obstruction to one proof route and an exact criterion for the remaining global estimate. Neither is a counted frontier solution. No independent proof or contribution review is claimed.

The question in `original-scope.md` asks whether every basis F=(u,v) of a double first positive Neumann eigenspace on every bounded smooth simply connected planar domain satisfies

    |x-y| <= C |F(x)-F(y)|^(1/2),  x,y in closure(Omega),

with a finite constant depending on the domain and basis. All boundary points are included. This question has not been replaced by an interior estimate or a weaker exponent.

## 1. Source and prior-operation accounting

Pinned input: openai/math, commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, family369, *Strict hot spots and absence of interior critical points on smooth simply connected planar domains*. Its `build/sections/01-introduction.tex`, `thm:main`, says that every nonzero first-mode eigenfunction has nonzero gradient everywhere in the interior. Source truth is stipulated. With a two-dimensional eigenspace this gives det DF nonzero in the interior, by elementary linear algebra. The same source's `lem:nodal`, `lem:gap`, `lem:conformal`, smooth boundary regularity and interior analyticity supply the other operative qualitative interfaces. No quantitative boundary Jacobian estimate is stated in those interfaces.

The qualitative global eigenmap is **already I214**, independently proof-passed in I218 and classified **TECHNICAL/KNOWN ONLY** in I219. It maps the interior analytically and diffeomorphically onto a smooth strictly star-shaped domain, extends homeomorphically to the closure, and maps the boundary diffeomorphically as a one-dimensional manifold. It does not have a differentiable or Lipschitz inverse at the boundary. I214 explicitly claims no inverse Hölder exponent. We use its qualitative conclusion as credited project support, never as a new finding.

An initial narrow search restricted to campaign `candidate.md`/`checkpoint.md` files missed I214. The broader search found the complete old chain before any target freeze, and its full discovery proof, full contribution review and parent disposition were read. The initial description of family369 as provisionally history-clean was corrected to the parent. The local construction below is a distinct quantitative operation, not a relabeling of the old global univalence argument.

The actual primary comparison with Alessandrini–Nesi, *Globally diffeomorphic sigma-harmonic mappings*, arXiv:1906.00902v1, confirms that the local-to-global degree/monodromy operation is classical. Their Theorems1.1 and3.4 concern divergence-form equations without a zero-order term and specified boundary univalence/nondegeneracy. They do not directly apply to a Helmholtz eigenmap with zero normal derivative and identically zero boundary Jacobian. We do not silently change that equation or claim their theorem proves T369H. Bañuelos–Pang's *Level sets of Neumann eigenfunctions*, Theorems1.1–1.2, addresses finite level components on strictly positively curved smooth convex domains; it supplies neither the full smooth-domain quantitative conclusion nor the strict coefficient below. Exact bounded reading is recorded separately.

## 2. The exact unpaid boundary coefficient

Orient the basis so J=det DF>0 in Omega. Write p(s) for counterclockwise unit-speed boundary parametrization, tau=p'(s), and n the inward unit normal. The coordinates x=p(s)+t n(s), t>=0, have positive orientation for small t. Set

    G(s,t)=F(p(s)+t n(s)),  f(s)=G(s,0).

Neumann data give G_t(s,0)=0. The Laplacian in boundary normal coordinates, evaluated at t=0, therefore gives

    G_tt(s,0)=-mu f(s)-f''(s).

The curvature term multiplying G_t vanishes at t=0. Thus, with K=det(G_s,G_t),

    K(s,0)=0,
    K_t(s,0)=A(s):=mu det(f,f')-det(f',f'').               (2.1)

Since K(s,t)>0 for t>0 sufficiently small, **A(s)>=0**. This limit does not imply strict positivity. The physical Jacobian is K divided by the positive normal-coordinate area factor, so its first normal coefficient is the same A.

The old qualitative result gives det(f,f')>0, after the orientation choice, and f' never vanishes. Hence A=0 is compatible with a nonzero radial Wronskian: the missing assertion is the strict curvature-type inequality

    det(f',f'') < mu det(f,f')  at every boundary point.  (2.2)

### Exact criterion

Under the credited I214 qualitative conclusions, the full T369H inequality holds **if and only if A(s)>0 everywhere on the boundary**. This is a local geometric criterion, not a proof of the spectral strict inequality.

**Necessity.** Let h be the smooth inward signed distance to the target boundary near f(s0). Its inward unit normal at f(s0) is the counterclockwise rotation of f'/|f'|. Along the source normal x(t)=p(s0)+tn(s0),

    h(F(x(0)))=0,  d/dt h(F(x(t))) at0=0,
    d²/dt² h(F(x(t))) at0=A(s0)/|f'(s0)|.

If A(s0)=0, this signed distance is o(t²). Let z(t) be the nearest target-boundary point to F(x(t)), and let q(t) be its unique preimage on the source boundary. The smooth tubular projection and G_t=0 give q(t)=p(s0)+O(t²), but more simply the source distance |x(t)-q(t)| is at least t for small t because x(t) has distance t from the entire source boundary. On the other hand

    |F(x(t))-F(q(t))|=o(t²).

The proposed bound t<=C sqrt(o(t²)) is impossible. Since A>=0, strict positivity at each point is necessary.

**Sufficiency.** If A>0, compactness gives a positive uniform minimum after division by |f'|. Use target tubular coordinates (z,h), where z is target-boundary arclength. Near a given source-boundary point, the map (s,t) to (z(F(p(s)+tn)),t) is a smooth local diffeomorphism: its s derivative at t=0 is |f'|>0. In these source coordinates the eigenmap is

    (z,t) -> (z,H(z,t)),
    H(z,0)=H_t(z,0)=0, H_tt(z,0)>0.

The coordinate change does not alter the last second derivative at t=0, because its first t derivative vanishes there and H(z,0) is identically zero. On a sufficiently small compact collar patch, H_t(z,t)>=c t for a fixed c>0, and |H_z|<=L. For two points in a rectangular patch, integration at fixed z gives

    (c/2)|t-t'|² <= |H(z,t)-H(z,t')|
                        <= |H(z,t)-H(z',t')|+L|z-z'|.

Both coordinate charts are bi-Lipschitz on the patch. Since |z-z'|² is bounded by a constant times |z-z'| there, this implies |x-y|²<=C_patch |F(x)-F(y)| for pairs in a smaller patch. Interior inverse-function charts provide the same estimate away from the boundary. A finite collection of such source neighborhoods covers the compact closure. Pairs at sufficiently small source separation lie in one member by the Lebesgue-number property. For the remaining pairs, compactness and injectivity give a positive minimum image separation. Increasing C handles those pairs. This proves the global inequality.

Thus T369H has been reduced exactly, without dropping a quantifier, to (2.2). The remaining issue is global first-mode information capable of forcing strictness.

## 3. A fully proved local analytic obstruction

The following construction is an obstruction to a **local proof of strictness**, not a counterexample to T369H.

There exist delta>0 and two real analytic functions u,v on a neighborhood of (0,0) such that, in the half-neighborhood |s|<delta, 0<t<delta,

1. (partial_s²+partial_t²+1)u=(partial_s²+partial_t²+1)v=0;
2. u_t(s,0)=v_t(s,0)=0;
3. J=u_s v_t-u_t v_s>0, so every nonzero linear combination a u+b v has nonzero gradient there;
4. for f(s)=(u(s,0),v(s,0)), det(f,f')=exp(s²)>0 and f' is nonzero;
5. the coefficient in (2.1) is A(s)=s² exp(s²), so A(0)=0;
6. on an appropriate half-neighborhood F=(u,v) is injective, but its inverse fails every Hölder estimate with exponent alpha>1/4, already along the normal at0.

All functions and constants are real. The local Helmholtz frequency is fixed to mu=1. We assert neither a complete bounded Neumann domain nor that1 is its first positive eigenvalue.

### 3.1 Exact construction

Let f(s) be the unique analytic vector solution of the ordinary differential equation

    f''(s)=(-1+s²)f(s)+2s f'(s),
    f(0)=(1,0), f'(0)=(0,1).                          (3.1)

Analytic linear ODE existence gives f near0. Solve the analytic, noncharacteristic Cauchy problem

    F_tt=-F_ss-F,  F(s,0)=f(s), F_t(s,0)=0.            (3.2)

The classical Cauchy–Kovalevskaya theorem gives a real analytic solution in a neighborhood of0. Its hypotheses are explicit: the coefficient of F_tt is1, the right side is analytic and depends only on derivatives not containing the second t derivative, and both Cauchy data are analytic. This standard existence theorem is an input to the local construction. No finite jet is substituted for its analytic solution.

Uniqueness and parity imply that u is even in s, v is odd in s, and both components are even in t. In particular v(0,t)=0 exactly, not only to finite order. The Taylor expansion in t is

    F(s,t)=f(s) -(t²/2)(1+D_s²)f(s)
                   +(t⁴/24)(1+D_s²)²f(s)+O(t⁶).     (3.3)

The remainder here is locally analytic in s,t with the indicated vanishing order; later two-variable remainders are stated separately.

### 3.2 Wronskian and boundary coefficient

Let D=det(f,f'). Equation(3.1) gives

    D'=det(f,f'')=2s D,  D(0)=1,
    D(s)=exp(s²).

Furthermore det(f',f'')=(1-s²)D. Substitution in(2.1) gives A(s)=s² D(s) exactly. This proves boundary immersion, radial transversality, and the isolated failure of the desired strict coefficient.

### 3.3 The two-variable Jacobian is strictly positive

The required initial derivatives are

    f''(0)=(-1,0), f'''(0)=(0,1), f''''(0)=(-1,0).

Write L=1+D_s². Differentiating(3.3) yields

    J(s,t)= t A(s)+t³ B(s)+O(t⁵),
    B(s)= (1/6)det(f',L²f)+(1/2)det((Lf)',Lf).

At0, Lf(0)=0 and L²f(0)=(-2,0), hence B(0)=1/3. Since J is even in s and odd in t, J/t extends real analytically across t=0 and is even in both variables. Its full quadratic Taylor polynomial is therefore

    J(s,t)/t = s²+t²/3+O((s²+t²)²).                  (3.4)

This is a two-variable remainder: there are finite M,r0>0 bounding its absolute value by M(s²+t²)² for s²+t²<r0². Reduce r0 until M r0²<=1/6. Then

    J(s,t) >= t[(5/6)s²+(1/6)t²]>0

for t>0 and s²+t²<r0². Every nonzero coefficient vector (a,b) thus has nonzero gradient for a u+b v, because DF is invertible there. Positivity is proved for a whole neighborhood, not inferred from sampled points or finite Taylor coefficients alone.

### 3.4 Injectivity and the obstruction to inverse exponents

Since v_s(0,0)=1, (s,t)->(v(s,t),t) is a real analytic local diffeomorphism. Use (z,t)=(v,t) as coordinates and restrict to a small rectangle |z|<epsilon, 0<=t<epsilon contained in the region above. Write U(z,t)=u(s(z,t),t). Direct differentiation gives

    U_t = (u_t v_s-u_s v_t)/v_s=-J/v_s<0  for t>0.

The eigenmap in these coordinates is (U(z,t),z). Equality of two images gives equality of z, and strict monotonicity in t then gives equality of t. This proves injectivity, including the flat boundary. At t=0 strict monotonicity follows by integrating the strictly negative derivative over any nontrivial interval with positive t.

Along s=0, parity gives v(0,t)=0. From(3.3) and the computed jets,

    u(0,t)=1-t⁴/12+O(t⁶).                            (3.5)

Consequently

    |F(0,t)-F(0,0)|=t⁴/12+O(t⁶),
    |(0,t)-(0,0)|=t.

For any alpha>1/4 and any finite C, the quotient t/|F(0,t)-F(0,0)|^alpha tends to infinity as t decreases to0. No such inverse Hölder estimate holds, although every item of the local PDE/noncriticality/radial-boundary interface listed above holds. In particular a local argument deriving the1/2 estimate from just those facts is false.

For a general check, replace(3.1) by f''=(-1+c s²)f+B s f', with the same initial data. Then D=exp(Bs²/2), A=c s²D and

    J/t=c s²+(B-c)t²/3+O((s²+t²)²),
    u(0,t)=1+(c-B)t⁴/12+O(t⁶).

Every B>c>0 gives the same type of local obstruction. The fixed rational choice c=1,B=2 suffices for the theorem and avoids an unneeded parameter claim.

## 4. What remains and what is not claimed

The construction satisfies the local Helmholtz equation, analytic flat Neumann boundary, interior noncriticality for every nonzero linear combination, boundary immersion, positive radial Wronskian, local injectivity, and nonnegative A. It defeats the proposed inference from this complete local package to A>0 or a1/2 inverse exponent. The new calculation is the cubic positive Jacobian with quartic normal image, not the known rank-one boundary degeneracy or the elementary failure of Lipschitz inversion.

It does **not** satisfy a specified bounded global domain's complete Neumann boundary condition, the first-positive variational characterization, global mean-zero conditions or global nodal constraints. Those missing global properties might force A>0; alternatively a realizable global example might violate it. Neither direction is proved. A local analytic model cannot be advertised as a counterexample to the source theorem or T369H.

The qualitative I214 theorem remains credited technical support. The exact criterion in Section2 is also supporting reduction. The local example has not undergone a literature priority review, and no broad novelty claim is made. This packet meets a research stopping point by preserving a specific new-to-this-attempt obstruction with a full argument, rather than merely listing unexamined source families. The campaign count changes by zero.

## 5. Reproducibility and formal coverage

Run `python3 exact_checks.py`. It uses exact rational arithmetic and a degree16 Taylor recurrence. It checks both Helmholtz residuals through total degree14, Neumann and parity identities, the leading Jacobian, the normal quartic coefficient, Wronskian and boundary-coefficient identities to their stated finite degrees, four parameter cases including sign/degeneracy controls, and two wrong-coefficient/linear-bound controls. The retained `validation.json` is its deterministic output. These checks support the derivation; Sections3.1 and3.3 supply analytic existence and whole-neighborhood positivity.

There is no Lean formalization of this construction, the criterion, the upstream theorem, or T369H. No independent gate is represented as passed. Public packet identity is checked by `verify_packet.py` against an externally supplied SHA256 of `MANIFEST.json`; mathematical validity does not follow from identity verification.

Primary links: [Alessandrini–Nesi v1](https://arxiv.org/pdf/1906.00902v1), [Bañuelos–Pang author PDF](https://www.math.purdue.edu/~banuelos/Papers/neumann.pdf). Pinned source URLs and canonical blob identities appear in `source-receipt.json`. Third-party and historical source bodies remain under `private/` and are excluded from the public payload.
