# T366A166 — leading loose-end curvature with bounded fidelity

Frozen author statement. Codex / GPT-6 Astra / high / default service tier. This is a research nominee, not an independent correctness or contribution verdict.

Let nu be the unique root in (3/2,2) of

 nu cos(pi nu) = (pi/2)(1/4-nu^2) sin(pi nu),

and put mu=nu-1/2, so 1<mu<3/2.

Let Omega be any bounded Lipschitz domain in R^2 and let g in L-infinity(Omega;R). Let K be relatively closed in Omega with H^1(K)<infinity, and let u in L^2(Omega) have restriction in W^{1,2}(Omega minus K). Assume K is reduced, meaning K=support_Omega(H^1 restricted to K). Assume (u,K) is an absolute minimizer of

 F_g(u,K;V)=integral_(V minus K)|grad u|^2 + H^1(K intersect V)
             + integral_V |u-g|^2

under every admissible comparison (v,L) for which (L symmetric-difference K) union ess-support(v-u) is compactly contained in V, for every open V compactly contained in Omega.

For every loose end p of K (a point where, in a neighborhood, K consists of a single embedded arc ending at p), choose oriented orthonormal coordinates (x,y) with origin p and the positive x-axis the outward tangent ray of that arc. There are delta>0, b in R, and a graph function

 psi in C^1([0,delta]) intersect W^{2,infinity}((0,delta)),
 psi(0)=psi'(0)=0,

whose graph agrees with K in a neighborhood of p, such that

 lim_(r down to 0) sup_(0<x<r)
   |psi(x)-b x^(1+mu)| / x^(1+mu) = 0,

 lim_(r down to 0) sup_(0<x<r)
   |psi'(x)-(1+mu)b x^mu| / x^mu = 0,

 lim_(r down to 0) ess-sup_(0<x<r)
   |psi''(x)-mu(1+mu)b x^(mu-1)| / x^(mu-1) = 0.

The coefficient b is allowed to vanish. No continuity of psi'' away from zero, uniform constants over minimizers, boundary regularity at partial Omega, or nonzero leading coefficient is asserted. In particular psi is twice differentiable at zero with psi''(0)=0, and its essentially bounded curvature tends to zero there.

The hypotheses cover every loose end of every reduced absolute minimizer in SOURCE366's full bounded-fidelity class. Existence of the tangent and local graph is a stipulated SOURCE366/primary regularity input. The proposed additional operation is the forced odd spectral asymptotic with measurable fidelity, including the dynamic boundary state, the Jordan sector, and the essential-supremum curvature limit.
