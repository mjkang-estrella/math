# Prefreeze feasibility: quantitative critical-law stability

These calculations follow complete canonical reading, original i135 mechanisms, and ELZ persistence Sections 2--4 through the next section boundary. They precede the frozen statement and author-proof drafting. Exploratory identification of the quadratic equality model occurred before the ELZ read; the quantitative construction below was developed after it. No endpoint radial or Orlicz bound is asserted.

Let K be the full normalized univalent half-plane class. Assume an exact inverse-square affine law P at exponent beta in [3/4,1]: E[|Q_F(x+iy)|^2 Phi(T_(x+iy)F)]=y^(-beta) E Phi(F) for all nonnegative Borel tests. This is a hypothesis, not an output claimed from the source operator at critical radius. Put eta=1-beta and k=(beta+3)/4. The source moment calculation gives E a=-beta/2, E|q|^2=beta(beta+1)/4 and E J_k=(beta-1)/(beta+3). Its weighted area/escape calculation still works for this exact law: k>=15/16>1/2 is sufficient for the boundary-cover sum. No rho>2 construction is used to produce P.

First attempt, insufficient: import strict equal-rank pairing. It yields E[J_+(c-1)]<=eta/(beta+3), but strictness alone has no uniform rate. A classification at eta=0 follows by elementary rigidity; compactness alone yields an unspecified modulus, not the proposed power rate. These are not new nominees.

Stronger construction: replace rank matching by component persistence. At each saddle of log V, the two rising local germs belong to different components of {V>V(s)}; otherwise lowering through that saddle creates a hole, incompatible with the source's Jordan superlevel property. Each component is represented by its largest maximum (or the unique pole). Pair the saddle with the lower of those two representatives. The older representative survives; finite superlevel exhaustion makes this assignment injective even when there are infinitely many critical points tending to level zero. The pole always survives. ELZ's 0-dimensional oldest-component rule is the primary starting operation, not claimed as new.

After rooting at a saddle, log V has uniform third-derivative bounds on a fixed disk, uniformly in F and k. Its Hessian has trace -k and determinant -k^4 J. Therefore its positive eigenvalue is at least c J_+. Move both ways a distance c times that eigenvalue. Taylor's formula raises log V by at least c J_+^3 on each branch. Both component representatives exceed this level. Thus the selected finite maximum satisfies (V(m)/V(s))^4 >= 1+c J_+^3. Rational polygon connectivity tests and local inverse-root enumeration make the assignment Borel; positive affine changes preserve the two germs, their components, their representatives and the choice. A complete treatment of these interfaces is required in the author proof.

Using this assignment in the source's box transport gives E J_+ + c E J_+^4 <= E J_-. Hence E J_+^4 <= C eta and E|J_k(i)| <= C eta^(1/4). Bounded local jets and exact covariance transfer this to E|J_1(z)|<=C_E eta^(1/4) uniformly on each compact E in H.

The analytic closure is an exact identity. With G_1=F-iyF', D=det DG_1, g=F', and H=D/y, one has
  H=y |g'|^2 + Im(g' conjugate(g)),
  2i H=(z-conjugate(z))g' conjugate(g') + g' conjugate(g)-g conjugate(g'),
  Delta H=4y |g''|^2=4y |F'''|^2.
Integrating against a nonnegative compact cutoff and using the preceding expected absolute determinant estimate controls the local L2 norm of F''' by C_E eta^(1/4). Submean/Cauchy estimates and integration along segments then control all compact C^m distances to the quadratic Taylor polynomial.

The quadratic coefficient c=F''(i) is projected onto |c+i/2|=1/2. Its distance from that circle is <=2||c|^2+Im(c)|=2|J_1(i)|. The circle parametrizes precisely the normalized real-root quadratics F_a and the affine limit. This projection is Borel with a fixed convention at the center. It closes the support-distance estimate with squared error C_(E,m) eta^(1/4).

At eta=0 the law is supported on those quadratics. Its affine atom has mass zero by scale covariance. The real root parameter a has measure mu; horizontal covariance makes (1+a^2)mu translation invariant. Therefore mu=da/[pi(1+a^2)]. This law directly satisfies full affine covariance at beta=1. The exact model is therefore present, so a strict spectral gap at this exponent would be wrong.

Nonvacuity below the endpoint: normalized powers (z-a)^alpha, 3/2<alpha<=2, with root density proportional to (1+a^2)^(-(alpha-1)), have exponent beta=2alpha-3. Their branch is defined by arg(z-a) in (0,pi). They are univalent and obey the exact covariance after a=x+yb. Thus the proposed stability addresses genuine laws arbitrarily near beta=1.

Residuals outside this operation: no law is produced from the critical dyadic operator; its horizontal cancellation retains an O(1) boundary term at rho=2. No transfer to arbitrary finite-radius extremizing sequences, no logarithmic/weak endpoint improvement, no numerical strict first-power gap, and no rate for an approximately covariant law is claimed. Those are not requirements of the exact-law stability target.
