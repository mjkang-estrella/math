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

## Pointwise derivative closure

This last logical distinction can be closed directly from the criterion in
the actual primary Proposition3. For a shifted well potential V with V(0)=0,
let v=sgn(x)sqrt(V(x)), x=X(v), and phi(x)=V(x)/V'(x)^2, extended smoothly
at zero. For energy e>0 the canonical period is

    T(e)=sqrt(2) integral_{-pi/2}^{pi/2} X'(sqrt(e) sin(theta)) dtheta.

On the compact orbit this has a smooth integrand, so differentiation gives

    T'(e)=sqrt(2)/(2sqrt(e)) integral_0^{pi/2}
        [X''(sqrt(e)sin(theta))-X''(-sqrt(e)sin(theta))] sin(theta) dtheta.

But X''(v)=2phi'(X(v)), since phi(X(v))=X'(v)^2/4. The bracket equals
2 integral_{X(-v)}^{X(v)} phi''(x) dx. Yagasaki Section3 gives phi''>=0
throughout the well and strictness near its center. Thus every bracket for
0<theta<pi/2 is strictly positive, and T'(e)>0 at EVERYenergy, not merely
strict monotonicity. For g(w)=w^p-w,

    phi''(center)=p(p+3)/(6(p-1))>0.

This also verifies the strict-near-center condition for irrationalp in the
paper's rational-limit argument. The beta-energy derivative and constant
time scaling above therefore give the literal P_alpha'(beta)<0.

Root decision: EXCLUDE as a routine classical oscillator corollary. The
new Laplace/Binet route remains a valid ordinary proof candidate, but a new
proof of an already subsumed endpoint does not create discovery credit.
No claim that Yagasaki explicitly discusses Coiculescu is made. Known theorem
+ explicit time-preserving reduction, rather than an exact prior paper using
the same question label, is the reason for this exclusion.
