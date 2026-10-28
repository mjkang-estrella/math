# New root equivalence: check before promotion

This addendum postdates the a6e42a96bc review freeze. It does not edit or
supersede the frozen ordinary Gamma/Laplace proof. Credit remains0.

The source sphere flow projects to the exact planar system

    x'=x z, z'=alpha-(alpha+1)x^2-alpha z^2.

Set u=x sqrt((alpha+1)/alpha)>0. This is a space coordinate change only:

    u'=u z, z'=alpha(1-u^2-z^2).

Then w=u^alpha satisfies EXACTLY in the same time variable

    w''=alpha^2 w(1-w^(2/alpha)),
    w''+alpha^2(w^(1+2/alpha)-w)=0, w>0.

Indeed the two z^2 terms cancel in differentiating w'=alpha*w*z.
Thus the source period equals the positive-well period of a power-potential
oscillator, with p=1+2/alpha>1 (p>=3 in source0<alpha<=1). Its energy is

    E=(w')^2/2+alpha^2(w^(p+1)/(p+1)-w^2/2),

between the minimum at w=1 and the separatrix E=0 at w=0. A complete
monotonicity theorem for this exact oscillator would subsume the new route
after checking how beta orders these energies. Do not confuse an orbital
equivalence with a time-preserving one: the displayed change IS time preserving.

Equivalent Loud coordinates are X=1-u, Y=z/sqrt(2alpha), tau=sqrt(2alpha)*t:

    dX/dtau=-Y+XY,
    dY/dtau=X-(1/2)X^2-alpha Y^2.

This is the quadratic Loud center with D=-1/2,F=-alpha. The constant time
factor preserves period monotonicity. The known Loud period diagram must
therefore be checked specifically on this ray, using actual theorem bodies.
If covered, the exact Coiculescu statement is an immediate classical corollary
and cannot receive campaign discovery credit, even if not explicitly noted.

## Concrete primary theorem now obtained

Root read the actual complete five-page RIMS1901(2014)116-120 paper of
Kazuyuki Yagasaki, "Bifurcation diagram for interior single-peak solutions in
a Neumann problem for u''+lambda(-u+u^p)=0 with p real and p>1".
Theorem2 on printedp118 states that the positive-well period T(u1), for
u''-u+u^p=0 and initialminimumu1 in(0,1), is strictly decreasing. Proposition3
on printedp119 invokes Chicone's period criterion. Section3 verifies its
second-derivative criterion for every realp>1, via positive polynomial
coefficients for rationalp and a limiting argument. Source:
https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1901-09.pdf .
Saved actual PDF/text in sources/miyamoto.* (filename historical; author of
this proceedings article is Yagasaki, collaborationwithMiyamoto acknowledged).

For the source's initialvector V_beta, u(0)=beta,z(0)=sqrt(1-beta^2).
The oscillator energy is exactly

    E_beta=-alpha^2 beta^(2alpha+2)/(2(alpha+1)),
    dE_beta/dbeta=-alpha^2 beta^(2alpha+1)<0.

The positive turning minimum w_min(E) satisfies
V'(w_min)=alpha^2(w_min^p-w_min)<0. Hence w_min increases withbeta, and
P_alpha(beta)=T_p(w_min(E_beta))/alpha (constant rescaling tau=alpha*t).
Yagasaki's Theorem2 thus supplies strict period monotonicity for everyalpha>0.
The small-oscillation limit is 2pi/(alpha*sqrt(p-1))=pi*sqrt(2/alpha).

One exact point requiring adversarial adjudication: Theorem2's wording
"strictly decreasing" alone does not logically imply pointwise T'<0.
The underlying Chicone integral criterion, with strict positivity near the
center as verified by Section3/Proposition3, should give pointwise T'<0 and
thus the source's literal derivative inequality. Check the actual criterion
or derive its short derivative integral; do not silently replace the source
derivative statement by strict monotonicity. If this closes, the full source
statement is an immediate classical oscillator corollary and credit0.
