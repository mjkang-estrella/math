# Prefreeze calculations III: a constant quadratic family tests the ambient estimate

This is a counterexample to an INFERENCE about chosen lifts, not to the exploratory theorem. The actual family is constant and has the identity as a bi-Lipschitz trivialization. The example shows that the source's qualitative ambient extension conditions, even supplemented by strong radial control and polynomial bounds on FIELD derivatives, do not force its arbitrary chosen flow to be bi-Hölder. It also leaves the prescribed zero-family lift unchanged.

## 1. The family and its fixed first integrals

Use complex spatial coordinates (x,y,z) and

    f(x,y,z)=xy+z^2,    F(x,y,z,t)=f(x,y,z).

The Jacobian ideal is (y,x,2z), so the only critical point is the origin and mu=1. This is a genuine isolated hypersurface surface family under the source hypotheses. Let r=(|x|^2+|y|^2+|z|^2)^(1/2). The real vector field

    A=i(x,-y,0)

satisfies df(A)=i xy-i xy=0, and dr(A)=0. It is the infinitesimal circle action (x,y,z)->(e^(is)x,e^(-is)y,z). Its spatial norm is at most r.

Choose smooth real cutoffs chi and eta with 0<=chi,eta<=1, where chi equals one near 1/2 and is zero for its argument <=1/4, and eta equals one near 1/4 and is zero near zero. Choose a smooth compactly supported function h on (-1,1), equal to -v for |v|<=1/2. All derivatives of these fixed functions are bounded.

On the sector where x≠0 and |arg x|<pi/4 let vartheta=arg x and put

    ell = r h(vartheta/r^3)
             chi(|x|^2/r^2) eta(|f|^2/r^4),
    W = ell A.                                                     (1)

Take r sufficiently small. Since h vanishes outside |vartheta|<r^3, its support lies well inside this sector. Extend by zero over the rest of the axis complement. The chi factor makes it vanish before x=0 is approached at fixed r, so W is smooth everywhere off the origin. Set W(0)=0.

Every multiplier is real. Consequently df(W)=0 and dr(W)=0 exactly. Moreover

    |W|<=C r^2.                                                    (2)

Thus W is continuous at the origin, and all its nonzero trajectories remain on compact spheres. They are complete for bounded time, with smooth inverse flows off the origin, and continuous forward/inverse flows at the origin. It is tangent to the boundary of every round ball.

The eta factor is zero near f=0 in the axis complement. Hence W agrees with the ZERO spatial lift on the entire punctured zero surface; in particular it is a legitimate kernel correction to the source's prescribed trivial zero transport. The field (W,1) lifts the real parameter direction and (0,i) lifts the imaginary direction in the constant family. Both preserve the defining function. Restricting to a small parameter disk gives the exact common tube situation of Section13. Combined radial parameter transports are also complete because r is conserved.

For every fixed derivative order j, a finite power bound

    |D^j W| <= C_j r^(-N_j)

holds off the origin. Indeed each differentiated factor is a smooth bounded function of ratios and angles; derivatives of r, arg x and the ratios on the support contribute only fixed inverse powers of r. The scaled argument vartheta/r^3 contributes further finite powers. There are finitely many products at each j. Smooth compact cutoffs make extension across the sector/support boundary harmless. No analyticity of this smooth cutoff field is claimed; the source's arbitrary extension is also smooth, using partitions of unity.

## 2. Exact exponential contraction on a nonzero level

For each sufficiently small r>0 consider

    p_r=(r/sqrt(2), r/sqrt(2), 0),
    q_r=(r exp(i r^3/2)/sqrt(2), r exp(-i r^3/2)/sqrt(2), 0).

Both have norm r and function value r^2/2≠0. Along their orbits, |x|^2/r^2=1/2 and |f|^2/r^4=1/4. The cutoffs are therefore identically one. For the q_r trajectory, 0<=vartheta<=r^3/2, so h(vartheta/r^3)=-vartheta/r^3. The exact angular equation is

    dvartheta/ds = -vartheta/r^2,
    vartheta(s) = (r^3/2) exp(-s/r^2).                              (3)

The point p_r is stationary. If Psi_s is the flow, direct computation gives

    |q_r-p_r|=2r sin(r^3/4),
    |Psi_s(q_r)-Psi_s(p_r)|=2r sin((r^3/4)exp(-s/r^2)).              (4)

For fixed s>0 these are respectively comparable to r^4/2 and (r^4/2)exp(-s/r^2), with constants independent of small r.

Suppose Psi_s^(-1) were alpha-Hölder near the origin, for ANY alpha>0. Applying its inequality to this pair would imply

    c r^4 <= C (C' r^4 exp(-s/r^2))^alpha,

and hence a bounded upper value for

    r^(4(1-alpha)) exp(alpha s/r^2).

This tends to infinity as r->0 for every alpha>0. For alpha<=1 the negative logarithmic power is dominated by alpha s/r^2; alpha>1 only makes the contradiction stronger. Therefore the inverse of this PARTICULAR smooth-off-axis complete flow is not Hölder of ANY positive exponent near the section. It already fails at a single fixed positive parameter, so a joint exponent is impossible for this choice.

## 3. What the example does and does not establish

The flow preserves f, r, the sphere, the origin, and the given identity zero-set transport. It satisfies the small-o spatial speed condition, has no finite-time collision with the section, has exact common tube domains, and has polynomial growth bounds for every fixed order of the generating field's derivatives. All the qualitative source mechanisms operate correctly. Nevertheless it fails the desired inverse two-point estimate.

Thus the proposed implication

    smooth controlled extension + complete transport + radial power bound
    + polynomial derivative bounds for the field => bi-Hölder ambient map

is false even for the simplest constant isolated surface family. This identifies why choosing the extension carefully is essential and why estimates for the FIELD and the MAP must be distinguished. The example does NOT prove that no good extension exists: W=0 gives the identity for this very family. It does not contest any source proof, identify a counterexample to note00, or yield a general impossibility claim.

A possible repair must exploit more than arbitrary kernel extension, for example the actual collapse/attaching relation, a simultaneous ambient analytic quotient, or a bilateral two-point estimate such as note03(7) or(9). No such repair has been supplied at the entire scope.
